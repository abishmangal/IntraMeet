#!/usr/bin/env python3
"""
IntraMeet server - updated to match requested configuration:
- Separate UDP ports for video, audio, and screen
- Audio mixing at 44100 Hz, 1024 samples per chunk
- Per-stream UDP addr tracking (video/audio/screen)
- Backwards-compatible udp_register handling (legacy single udp_port accepted)
- All other control/file/chat functionality remains on TCP port (5000)
"""
import socket
import threading
import json
import os
import time
import struct
from collections import defaultdict, deque

# ---------------- Config (matched to user's config block) ----------------
HOST = "0.0.0.0"
TCP_PORT = 5000              # control, chat, file (unchanged)
VIDEO_UDP_PORT = 5001        # for video streaming (V)
AUDIO_UDP_PORT = 5002        # for audio streaming (A -> server) and mixed audio out (M)
SCREEN_TCP_PORT = 5003       # not used separately here; screen control remains on TCP (if needed)
SCREEN_UDP_PORT = 5004       # screen frame data (S)
FILE_TCP_PORT = 5005         # optional separate file TCP (not required; we keep uploads on control TCP)

RECV_BUF = 65536
FILES_DIR = "server_files"
os.makedirs(FILES_DIR, exist_ok=True)

# Audio mixing params (must match clients)
AUDIO_RATE = 44100
AUDIO_CHUNK_SAMPLES = 1024
AUDIO_CHUNK_BYTES = AUDIO_CHUNK_SAMPLES * 2
MIX_INTERVAL = AUDIO_CHUNK_SAMPLES / float(AUDIO_RATE)  # seconds per mix

# Other params
VIDEO_JPEG_QUALITY = 60
SCREEN_JPEG_QUALITY = 50

# ---------------- Global state ----------------
clients = {}  # username -> {tcp, addr, udp_video_port, udp_audio_port, udp_screen_port, udp_video_addr, udp_audio_addr, udp_screen_addr, last_seen}
clients_lock = threading.Lock()

# audio buffers: username -> deque of latest payloads
audio_buffers = defaultdict(lambda: deque(maxlen=8))
audio_lock = threading.Lock()

# File state
available_files = {} # filename -> {"size": int, "token": str, "path": str}
files_lock = threading.Lock()

# ---------------- UDP sockets (separate) ----------------
video_sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
video_sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
video_sock.bind((HOST, VIDEO_UDP_PORT))

audio_sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
audio_sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
audio_sock.bind((HOST, AUDIO_UDP_PORT))

screen_sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
screen_sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
screen_sock.bind((HOST, SCREEN_UDP_PORT))

# ---------------- header helpers (compatible with client) ----------------
def build_header(pkt_type: bytes, username: str, seq: int):
    name_b = username.encode("utf-8")
    ts = time.time()
    return pkt_type + struct.pack("!H", len(name_b)) + name_b + struct.pack("!I", seq) + struct.pack("!d", ts)

def parse_header(data: bytes):
    if len(data) < 15:
        return None
    try:
        dtype = data[0:1].decode("utf-8", errors="ignore")
        name_len = struct.unpack("!H", data[1:3])[0]
        name_end = 3 + name_len
        username = data[3:name_end].decode("utf-8", errors="ignore")
        seq = struct.unpack("!I", data[name_end:name_end + 4])[0]
        ts = struct.unpack("!d", data[name_end + 4:name_end + 12])[0]
        payload = data[name_end + 12:]
        return dtype, username, seq, ts, payload
    except Exception:
        return None

# ---------------- file loading ----------------
def _load_existing_files():
    with files_lock:
        for f in os.listdir(FILES_DIR):
            try:
                token, fname = f.split("_", 1)
                path = os.path.join(FILES_DIR, f)
                size = os.path.getsize(path)
                available_files[fname] = {"size": size, "token": token, "path": path}
            except Exception:
                print(f"Warning: Skipping malformed file {f}")
        print(f"Loaded {len(available_files)} existing files.")

# ---------------- TCP handler ----------------
def handle_tcp_client(conn, addr):
    username = None
    fobj = conn.makefile("rb")
    try:
        while True:
            line = fobj.readline()
            if not line:
                break
            try:
                msg = json.loads(line.decode("utf-8", errors="ignore").strip())
            except Exception:
                continue

            mtype = msg.get("type")
            if mtype == "join":
                requested = msg.get("username")
                if not requested:
                    continue

                with clients_lock:
                    if requested in clients:
                        try:
                            conn.send((json.dumps({"type": "error", "message": "username_taken"}) + "\n").encode())
                        except:
                            pass
                        print(f"Rejected duplicate username: {requested} from {addr}")
                        break

                    # gather existing users for welcome
                    current_users = list(clients.keys())
                    clients[requested] = {
                        "tcp": conn,
                        "addr": addr,
                        "udp_video_port": None,
                        "udp_audio_port": None,
                        "udp_screen_port": None,
                        "udp_video_addr": None,
                        "udp_audio_addr": None,
                        "udp_screen_addr": None,
                        "last_seen": time.time()
                    }
                    username = requested

                print(f"User '{username}' joined from {addr}")

                # Welcome: include dedicated UDP ports so client knows where to send
                try:
                    conn.send((json.dumps({
                        "type": "welcome",
                        "udp_video_port": VIDEO_UDP_PORT,
                        "udp_audio_port": AUDIO_UDP_PORT,
                        "udp_screen_port": SCREEN_UDP_PORT,
                        "users": current_users
                    }) + "\n").encode())
                except:
                    pass

                # announce
                broadcast_control({"type": "user_joined", "username": username}, exclude=username)

                # send file list
                with files_lock:
                    for fname in available_files.keys():
                        try: conn.send((json.dumps({"type": "file_available", "filename": fname}) + "\n").encode())
                        except: pass

            elif mtype == "udp_register":
                # Support both legacy 'udp_port' and per-stream ports
                if username:
                    vport = msg.get("video_port") or msg.get("udp_port")
                    aport = msg.get("audio_port") or msg.get("udp_port")
                    sport = msg.get("screen_port") or msg.get("udp_port")
                    with clients_lock:
                        info = clients.get(username)
                        if info:
                            if vport is not None:
                                info["udp_video_port"] = int(vport)
                            if aport is not None:
                                info["udp_audio_port"] = int(aport)
                            if sport is not None:
                                info["udp_screen_port"] = int(sport)
                            info["last_seen"] = time.time()
                            print(f"User '{username}' registered UDP ports v={info['udp_video_port']} a={info['udp_audio_port']} s={info['udp_screen_port']}")

            elif mtype == "chat":
                print(f"Chat from '{username}': {msg.get('message', '')}")
                broadcast_control(msg)

            elif mtype == "video_stop":
                if username:
                    broadcast_control({"type": "video_stop", "username": username}, exclude=username)

            elif mtype == "screen_stop":
                if username:
                    broadcast_control({"type": "screen_stop", "username": username}, exclude=username)

            elif mtype == "file_upload":
                fname = msg.get("filename")
                try:
                    size = int(msg.get("size", 0))
                except Exception:
                    size = 0
                token = msg.get("token")
                if not fname or not token:
                    continue

                save_name = f"{token}_{fname}"
                save_path = os.path.join(FILES_DIR, save_name)

                # ack
                try:
                    conn.send((json.dumps({"type": "ready_for_file", "token": token}) + "\n").encode())
                except:
                    pass

                remain = size
                try:
                    with open(save_path, "wb") as fw:
                        while remain > 0:
                            chunk = fobj.read(min(8192, remain))
                            if not chunk:
                                break
                            fw.write(chunk)
                            remain -= len(chunk)
                except Exception as e:
                    print(f"Error receiving file {fname} from {username}: {e}")
                    try: os.remove(save_path)
                    except: pass
                    continue

                if remain == 0:
                    print(f"File '{fname}' uploaded by '{username}'")
                    with files_lock:
                        available_files[fname] = {"size": size, "token": token, "path": save_path}
                    broadcast_control({"type": "file_available", "filename": fname})
                else:
                    print(f"Incomplete upload for {fname} from {username}")
                    try: os.remove(save_path)
                    except: pass

            elif mtype == "download_request":
                fname = msg.get("filename")
                if not fname:
                    continue
                found = None; size = 0
                with files_lock:
                    data = available_files.get(fname)
                    if data:
                        found = data["path"]; size = data["size"]
                if not found:
                    try: conn.send((json.dumps({"type": "file_not_found", "filename": fname}) + "\n").encode())
                    except: pass
                else:
                    try:
                        conn.send((json.dumps({"type": "file_data", "filename": fname, "size": size}) + "\n").encode())
                        with open(found, "rb") as fr:
                            while True:
                                chunk = fr.read(8192)
                                if not chunk: break
                                conn.sendall(chunk)
                        print(f"Sent file '{fname}' to '{username}'")
                    except Exception as e:
                        print(f"Error sending file {fname} to {username}: {e}")

            elif mtype == "file_list_request":
                with files_lock:
                    for fname in available_files.keys():
                        try: conn.send((json.dumps({"type": "file_available", "filename": fname}) + "\n").encode())
                        except: pass

            elif mtype == "user_left":
                break

            else:
                # ignore unknown
                pass

    except Exception:
        pass
    finally:
        # cleanup
        if username:
            print(f"User '{username}' disconnected.")
            with clients_lock:
                clients.pop(username, None)
            with audio_lock:
                try: audio_buffers.pop(username, None)
                except: pass
            broadcast_control({"type": "user_left", "username": username})
        try:
            fobj.close()
        except:
            pass
        try:
            conn.close()
        except:
            pass

# ---------------- control broadcast ----------------
def broadcast_control(msg, exclude=None):
    remove = []
    with clients_lock:
        for uname, info in list(clients.items()):
            if uname == exclude: continue
            try:
                info["tcp"].send((json.dumps(msg) + "\n").encode())
            except Exception:
                print(f"Failed send to {uname}, removing")
                remove.append(uname)
        for uname in remove:
            info = clients.pop(uname, None)
            if info:
                try: info["tcp"].close()
                except: pass
            with audio_lock:
                try: audio_buffers.pop(uname, None)
                except: pass

# ---------------- UDP receive loops ----------------
def video_receive_loop():
    while True:
        try:
            data, addr = video_sock.recvfrom(RECV_BUF)
        except Exception as e:
            print("Video UDP recv error:", e); time.sleep(0.01); continue
        parsed = parse_header(data)
        if not parsed:
            continue
        dtype, uname, seq, ts, payload = parsed
        # record observed source
        if uname:
            with clients_lock:
                c = clients.get(uname)
                if c:
                    c["udp_video_addr"] = addr
                    c["last_seen"] = time.time()
        if dtype != "V":
            # ignore other types on video socket
            continue
        # rebroadcast to other clients' video destination
        with clients_lock:
            targets = list(clients.items())
        for other_name, info in targets:
            if other_name == uname: continue
            dest = None
            if info.get("udp_video_addr"):
                dest = info["udp_video_addr"]
            else:
                vp = info.get("udp_video_port")
                if vp:
                    dest = (info["addr"][0], vp)
            if not dest: continue
            try:
                video_sock.sendto(data, dest)
            except Exception:
                pass

def screen_receive_loop():
    while True:
        try:
            data, addr = screen_sock.recvfrom(RECV_BUF)
        except Exception as e:
            print("Screen UDP recv error:", e); time.sleep(0.01); continue
        parsed = parse_header(data)
        if not parsed:
            continue
        dtype, uname, seq, ts, payload = parsed
        if uname:
            with clients_lock:
                c = clients.get(uname)
                if c:
                    c["udp_screen_addr"] = addr
                    c["last_seen"] = time.time()
        if dtype != "S":
            continue
        # rebroadcast to all clients' screen destinations
        with clients_lock:
            targets = list(clients.items())
        for other_name, info in targets:
            if other_name == uname: continue
            dest = None
            if info.get("udp_screen_addr"):
                dest = info["udp_screen_addr"]
            else:
                sp = info.get("udp_screen_port")
                if sp:
                    dest = (info["addr"][0], sp)
            if not dest: continue
            try:
                screen_sock.sendto(data, dest)
            except Exception:
                pass

def audio_receive_loop():
    """
    Collect incoming audio frames from clients (type 'A') into per-user buffers.
    These frames are used by mix_and_broadcast.
    """
    while True:
        try:
            data, addr = audio_sock.recvfrom(RECV_BUF)
        except Exception as e:
            print("Audio UDP recv error:", e); time.sleep(0.01); continue
        parsed = parse_header(data)
        if not parsed:
            continue
        dtype, uname, seq, ts, payload = parsed
        if uname:
            with clients_lock:
                c = clients.get(uname)
                if c:
                    c["udp_audio_addr"] = addr
                    c["last_seen"] = time.time()
        if dtype != "A":
            continue
        # store latest audio frames
        if not uname: continue
        with audio_lock:
            audio_buffers[uname].append(payload)

# ---------------- Audio mixing ----------------
def mix_and_broadcast():
    import numpy as _np
    seq = 0
    silent_chunk = (_np.zeros(AUDIO_CHUNK_SAMPLES, dtype=_np.int16)).tobytes()
    prev_frames = {}
    SMOOTH_ALPHA = 0.15

    while True:
        start = time.time()
        frames_map = {}
        with audio_lock:
            for uname, dq in list(audio_buffers.items()):
                if dq:
                    payload = dq[-1]
                    if payload and len(payload) == AUDIO_CHUNK_BYTES:
                        frames_map[uname] = payload
        if frames_map:
            try:
                float_arrays = {}
                for uname, payload in frames_map.items():
                    arr_i16 = _np.frombuffer(payload, dtype=_np.int16)
                    arr_f = arr_i16.astype(_np.float32) / 32768.0
                    mean = arr_f.mean() if arr_f.size > 0 else 0.0
                    if abs(mean) > 1e-8:
                        arr_f = arr_f - mean
                    float_arrays[uname] = arr_f

                if float_arrays:
                    seq = (seq + 1) & 0xFFFFFFFF
                    with clients_lock:
                        targets = list(clients.items())
                    for target_name, info in targets:
                        dest = None
                        if info.get("udp_audio_addr"):
                            dest = info["udp_audio_addr"]
                        else:
                            ap = info.get("udp_audio_port")
                            if ap:
                                dest = (info["addr"][0], ap)
                        if not dest:
                            continue
                        others = [arr for uname, arr in float_arrays.items() if uname != target_name]
                        if not others:
                            mix_f = _np.zeros(AUDIO_CHUNK_SAMPLES, dtype=_np.float32)
                        else:
                            mix_f = _np.sum(others, axis=0) / max(1, len(others))
                            m = mix_f.mean()
                            if abs(m) > 1e-8:
                                mix_f = mix_f - m
                            max_abs = float(_np.max(_np.abs(mix_f)))
                            if max_abs > 1.0:
                                mix_f = mix_f / max_abs
                        prev = prev_frames.get(target_name)
                        if prev is None:
                            smoothed = mix_f
                        else:
                            smoothed = prev * (1.0 - SMOOTH_ALPHA) + mix_f * SMOOTH_ALPHA
                        prev_frames[target_name] = smoothed
                        out_i16 = _np.clip(smoothed * 32767.0, -32767, 32767).astype(_np.int16)
                        mix_bytes = out_i16.tobytes()
                        if len(mix_bytes) != AUDIO_CHUNK_BYTES:
                            mix_bytes = silent_chunk
                        hdr = build_header(b"M", "server", seq)
                        try:
                            audio_sock.sendto(hdr + mix_bytes, dest)
                        except Exception:
                            pass
            except Exception as e:
                print("Audio mix error:", e)
        elapsed = time.time() - start
        to_wait = MIX_INTERVAL - elapsed
        if to_wait > 0:
            time.sleep(to_wait)

# ---------------- TCP accept loop ----------------
def tcp_accept_loop(sock):
    while True:
        try:
            conn, addr = sock.accept()
            threading.Thread(target=handle_tcp_client, args=(conn, addr), daemon=True).start()
        except Exception as e:
            print("TCP accept error:", e)
            time.sleep(0.1)

# ---------------- main ----------------
def main():
    _load_existing_files()
    tcp_sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    tcp_sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    tcp_sock.bind((HOST, TCP_PORT))
    tcp_sock.listen(50)
    print(f"Server listening: TCP {TCP_PORT}, VIDEO_UDP {VIDEO_UDP_PORT}, AUDIO_UDP {AUDIO_UDP_PORT}, SCREEN_UDP {SCREEN_UDP_PORT}")

    threading.Thread(target=tcp_accept_loop, args=(tcp_sock,), daemon=True).start()
    threading.Thread(target=video_receive_loop, daemon=True).start()
    threading.Thread(target=audio_receive_loop, daemon=True).start()
    threading.Thread(target=screen_receive_loop, daemon=True).start()
    threading.Thread(target=mix_and_broadcast, daemon=True).start()

    try:
        while True:
            time.sleep(10)
    except KeyboardInterrupt:
        print("Shutting down")
        try: tcp_sock.close()
        except: pass
        try: video_sock.close()
        except: pass
        try: audio_sock.close()
        except: pass
        try: screen_sock.close()
        except: pass

if __name__ == "__main__":
    main()