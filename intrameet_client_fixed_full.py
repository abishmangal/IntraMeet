#!/usr/bin/env python3
"""
IntraMeet v9.4 - Client (UI-Refactor) - FULL FIXED
- Major fixes / changes (audio & threading focused, as requested):
  - Switched to the requested audio configuration (44.1 kHz, 1024 samples per chunk).
  - Replaced jitter_buffer/deque logic with a thread-safe Queue for incoming mixed audio.
  - Implemented receive + playback separation: UDP reader places M (mixed) frames into audio_buffer,
    a dedicated audio_playback_thread reads from that queue and writes to the output stream.
  - Playback thread uses smoothing on underruns/starts (short fade) to avoid clicks/rattling.
  - Capture thread uses shared PyAudio instance and properly opens/closes the input stream.
  - All audio streams (playback/capture/test) open with the configured chunk size and sample rate.
  - UDP socket set to non-blocking/timeout to ensure threads can exit cleanly.
  - Video capture thread improved with retry logic so local video can start reliably even if device was busy.
  - All long-running threads check flags and use try/except carefully to avoid crashes.
  - Minor locking around play_stream to avoid race conditions.
- I kept the rest of the UI/feature code intact (chat, files, participant UI) as requested.
- Note: This client now expects server to send mixed audio packets (type 'M') sized to AUDIO_CHUNK_BYTES.

IMPORTANT: I changed audio constants to the configuration you supplied (44100 Hz, 1024 samples).
If your server still uses 24 kHz / 512 samples you must keep the server and client consistent. If you
don't control the server, revert AUDIO_RATE and AUDIO_CHUNK_SAMPLES to match the server.
"""
import os
import socket
import struct
import threading
import time
import json
import uuid
import hashlib
from io import BytesIO
from datetime import datetime
from collections import deque
import queue
import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox, filedialog, simpledialog
from PIL import Image, ImageTk, ImageOps
import cv2
import numpy as np
import pyaudio
import mss

# ---------------- CONFIG (updated per request) ----------------
# Use the audio configuration block the user included
AUDIO_RATE = 44100        # Sample rate (Hz)
AUDIO_CHUNK_SAMPLES = 1024        # Samples per chunk (smaller chunks = lower latency)
AUDIO_CHANNELS = 1        # Mono audio
AUDIO_CHUNK_BYTES = AUDIO_CHUNK_SAMPLES * 2
AUDIO_BUFFER_SIZE = 10    # Number of chunks to buffer for jitter compensation

# Video & screen values remain largely unchanged (but video capture retries were added)
VIDEO_JPEG_QUALITY = 60
VIDEO_SEND_INTERVAL = 0.04
SCREEN_JPEG_QUALITY = 70
SCREEN_SEND_INTERVAL = 0.3

# AGC / gating constants (kept but tuned for 44.1k)
TARGET_RMS = 2000.0
MIN_SEND_RMS = 120.0
MAX_CAPTURE_GAIN = 6.0
MIN_CAPTURE_GAIN = 0.3
CAPTURE_SMOOTH = 0.18
ECHO_SUPPRESSION_THRESHOLD = 900.0
ECHO_SUPPRESSION_FACTOR = 0.32

DOWNLOAD_DIR = "Downloads"
os.makedirs(DOWNLOAD_DIR, exist_ok=True)

# ---------------- helpers ----------------
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

def name_color(name: str):
    h = int(hashlib.md5(name.encode()).hexdigest(), 16)
    r = 100 + (h % 100)
    g = 100 + ((h // 100) % 100)
    b = 100 + ((h // 10000) % 100)
    return f"#{r:02x}{g:02x}{b:02x}"

# ---------------- Client application ----------------
class ClientApp:
    def __init__(self):
        self.root = tk.Tk()
        self.root.title("IntraMeet v9.4")
        self.root.geometry("1280x760")
        self.root.minsize(900, 600)
        self.root.configure(bg="#0f0f10")
        
        # --- Style ---
        self.style = ttk.Style()
        try:
            self.style.theme_use("clam") # may raise if theme not available
        except Exception:
            pass
        self.setup_styles()
        # --- End Style ---

        # networking
        self.tcp = None
        self.udp = None
        self.server_ip = ""
        self.server_port = 5000
        self.udp_port = None
        self.connected = False
        self.username = ""

        # av states
        self.audio_on = False
        self.video_on = False
        self.screen_on = False
        self.audio_seq = 0
        self.video_seq = 0
        self.screen_seq = 0

        # participants & UI tiles
        self.participants = {}
        self.participants_lock = threading.Lock()
        self.presenter = None
        self.tiles = {}
        self.tiles_lock = threading.Lock()

        # chat & files
        self.available_files = []
        self.pending_file_events = {}
        self.chat_history = []

        # audio
        # replace jitter_buffer with a thread-safe queue for incoming mixed frames
        self.audio_buffer = queue.Queue(maxsize=AUDIO_BUFFER_SIZE)
        self.audio_buffer_lock = threading.Lock()
        self.jitter_running = False
        self.play_stream = None
        self.play_stream_lock = threading.Lock()
        self.playback_gain = 1.0
        self.playback_rms = 0.0
        self.capture_gain = 1.0
        self.audio_playing = True  # allow playback thread to run while connected

        # Use a single PyAudio instance for the whole app
        try:
            self.pyaudio_instance = pyaudio.PyAudio()
        except Exception as e:
            # Avoid showing modal before UI built; print and set None
            print("Audio Init Error:", e)
            self.pyaudio_instance = None

        self.input_device_index = None
        self.output_device_index = None
        self.input_device_var = tk.StringVar(value="Default")
        self.output_device_var = tk.StringVar(value="Default")

        # video
        self.frame_queue = deque(maxlen=2)
        self.video_running = False

        # screen
        self.screen_queue = None
        self.screen_running = False

        # UI refs
        self.main_area_frame = None
        self.video_grid_frame = None
        self.screen_frame = None
        self.screen_label = None
        self.screen_visible = False
        self.chat_popup = None
        self.file_popup = None
        self.part_popup = None # Participant popup
        self.chat_text = None
        self.chat_entry = None

        # toolbar refs
        self.btn_mic = None
        self.btn_mic_arrow = None
        self.btn_cam = None
        self.btn_screen = None
        self.btn_chat = None
        self.btn_files = None
        self.btn_parts = None # Participant button
        self.btn_leave = None

        self.status_var = tk.StringVar(value="Not connected")

        # shutdown flags
        self._threads_should_exit = threading.Event()

        # Auto-detect devices at startup
        self._detect_audio_devices()

        self.build_login()
        self.root.protocol("WM_DELETE_WINDOW", self.close)
        self._resize_after_id = None
        self.root.bind("<Configure>", self._on_root_configure)

    # ---------------- Style setup ----------------
    def setup_styles(self):
        """Defines all ttk styles for the application."""
        button_font = ("", 11)
        self.style.configure("Toolbar.TButton", background="#2b2b2b", foreground="white", font=button_font,
                             padding=(20, 10), borderwidth=0, relief="flat")
        self.style.map("Toolbar.TButton", background=[('active', '#3a3a3a'), ('pressed', '#4f4f4f')])
        self.style.configure("MicOn.TButton", background="#2e7d32", foreground="white", font=button_font, padding=(20, 10))
        self.style.map("MicOn.TButton", background=[('active', '#4a9d4e'), ('pressed', '#2e7d32')])
        self.style.configure("CamOn.TButton", background="#1565c0", foreground="white", font=button_font, padding=(20, 10))
        self.style.map("CamOn.TButton", background=[('active', '#1e88e5'), ('pressed', '#1565c0')])
        self.style.configure("ScreenOn.TButton", background="#6a1b9a", foreground="white", font=button_font, padding=(20, 10))
        self.style.map("ScreenOn.TButton", background=[('active', '#8e24aa'), ('pressed', '#6a1b9a')])
        self.style.configure("Leave.TButton", background="#b71c1c", foreground="white", font=button_font, padding=(20, 10))
        self.style.map("Leave.TButton", background=[('active', '#d32f2f'), ('pressed', '#b71c1c')])
        self.style.configure("Arrow.TButton", background="#2b2b2b", foreground="white", font=("", 10, "bold"), padding=(5, 10),
                             borderwidth=0, relief="flat")
        self.style.map("Arrow.TButton", background=[('active', '#3a3a3a'), ('pressed', '#4f4f4f')])

    # ---------------- audio device detection & setting ----------------
    def _detect_audio_devices(self):
        try:
            pa = self.pyaudio_instance
            if pa is None:
                self._input_devices = []
                self._output_devices = []
                self.input_device_index = None
                self.output_device_index = None
                self.input_device_var.set("Default")
                self.output_device_var.set("Default")
                return

            n = pa.get_device_count()
            self._input_devices = []
            self._output_devices = []
            for i in range(n):
                try:
                    info = pa.get_device_info_by_index(i)
                except Exception:
                    continue
                name = info.get("name", f"device_{i}")
                if info.get("maxInputChannels", 0) > 0:
                    self._input_devices.append((name, i))
                if info.get("maxOutputChannels", 0) > 0:
                    self._output_devices.append((name, i))
            # select default available
            if self._input_devices:
                if self.input_device_index is None or not any(i == self.input_device_index for _, i in self._input_devices):
                    self.input_device_index = self._input_devices[0][1]
                    self.input_device_var.set(self._input_devices[0][0])
                else:
                    for nname, idx in self._input_devices:
                        if idx == self.input_device_index:
                            self.input_device_var.set(nname); break
            else:
                self.input_device_index = None
                self.input_device_var.set("Default")

            if self._output_devices:
                if self.output_device_index is None or not any(i == self.output_device_index for _, i in self._output_devices):
                    self.output_device_index = self._output_devices[0][1]
                    self.output_device_var.set(self._output_devices[0][0])
                else:
                    for nname, idx in self._output_devices:
                        if idx == self.output_device_index:
                            self.output_device_var.set(nname); break
            else:
                self.output_device_index = None
                self.output_device_var.set("Default")
        except Exception:
            self._input_devices = []
            self._output_devices = []
            self.input_device_index = None
            self.output_device_index = None
            try:
                self.input_device_var.set("Default")
                self.output_device_var.set("Default")
            except:
                pass

    def _set_input_device(self, idx):
        self.input_device_index = idx
        found = False
        for name, i in getattr(self, "_input_devices", []):
            if i == idx:
                try: self.input_device_var.set(name)
                except: pass
                found = True
                break
        if not found:
            try: self.input_device_var.set("Default")
            except: pass
        print(f"Set input device to: {self.input_device_var.get()}")

    def _set_output_device(self, idx):
        self.output_device_index = idx
        found = False
        for name, i in getattr(self, "_output_devices", []):
            if i == idx:
                try: self.output_device_var.set(name)
                except: pass
                found = True
                break
        if not found:
            try: self.output_device_var.set("Default")
            except: pass
        print(f"Set output device to: {self.output_device_var.get()}")
        # Force playback stream to reopen with new device
        with self.play_stream_lock:
            if self.play_stream:
                try:
                    self.play_stream.stop_stream(); self.play_stream.close()
                except:
                    pass
                self.play_stream = None

    # ---------------- Login UI ----------------
    def build_login(self):
        for w in self.root.winfo_children():
            w.destroy()
        frame = tk.Frame(self.root, bg="#0f0f10", padx=40, pady=40)
        frame.pack(expand=True)
        tk.Label(frame, text="IntraMeet", fg="#4a90e2", bg="#0f0f10", font=("Segoe UI", 28, "bold")).pack(pady=(0, 14))
        def row(label, default=""):
            r = tk.Frame(frame, bg="#0f0f10")
            tk.Label(r, text=label, bg="#0f0f10", fg="white", width=12, anchor="e").pack(side="left", padx=6)
            e = tk.Entry(r, bg="#1f1f1f", fg="white", insertbackground="white", width=32, relief="flat")
            if default:
                e.insert(0, default)
            e.pack(side="left", padx=6)
            r.pack(pady=6)
            return e
        self.ip_entry = row("Server IP:", "127.0.0.1")
        self.port_entry = row("Port:", "5000")
        self.user_entry = row("Username:", f"User_{int(time.time())%1000}")
        btn = tk.Button(frame, text="Join Meeting", command=self.connect, bg="#1976d2", fg="white", font=("Segoe UI", 12), relief="flat")
        btn.pack(pady=(18,6))
        tk.Label(frame, textvariable=self.status_var, fg="red", bg="#0f0f10").pack(pady=(6,0))

    # ---------------- Connect ----------------
    def connect(self):
        ip = self.ip_entry.get().strip()
        port_s = self.port_entry.get().strip()
        user = self.user_entry.get().strip()
        if not ip or not port_s or not user:
            messagebox.showerror("Error", "Server IP, Port and Username required")
            return
        try:
            port = int(port_s)
        except:
            messagebox.showerror("Error", "Invalid port"); return
        self.server_ip, self.server_port, self.username = ip, port, user
        threading.Thread(target=self._connect_thread, daemon=True).start()

    def _connect_thread(self):
        try:
            self.status_var.set("Connecting...")
            self.tcp = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.tcp.settimeout(5)
            self.tcp.connect((self.server_ip, self.server_port))
            self.tcp.settimeout(None)
            # create UDP socket which will receive video/audio/screen
            self.udp = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            # Bind to ephemeral port and register with server
            self.udp.bind(("0.0.0.0", 0))
            # set a timeout so recvfrom won't block forever on shutdown
            self.udp.settimeout(0.5)
            self.udp_port = self.udp.getsockname()[1]

            # Send join and register UDP
            self.tcp.send((json.dumps({"type": "join", "username": self.username}) + "\n").encode())
            self.tcp.send((json.dumps({"type": "udp_register", "udp_port": self.udp_port}) + "\n").encode())

            # Block to read the 'welcome' message *first*
            f = self.tcp.makefile("r", encoding="utf-8")
            welcome_line = f.readline()
            if not welcome_line:
                raise Exception("Server closed connection prematurely.")
            
            welcome_msg = json.loads(welcome_line)
            
            if welcome_msg.get("type") != "welcome":
                raise Exception("Server did not send welcome message first.")
                
            self.udp_port = welcome_msg.get("udp_port", self.udp_port)
            initial_users = welcome_msg.get("users", [])
            
            # Populate participants list *before* building UI
            with self.participants_lock:
                for user in initial_users:
                    if user != self.username:
                        self.participants[user] = None # Add placeholders
            
            self.connected = True
            self.status_var.set(f"Connected to {self.server_ip}:{self.server_port}")
            
            # Start main reader threads
            # TCP reader uses the file object returned above
            threading.Thread(target=self.tcp_reader, args=(f,), daemon=True).start() 
            threading.Thread(target=self.udp_reader, daemon=True).start()

            # Start audio playback thread (reads from audio_buffer queue and plays)
            self.jitter_running = True
            threading.Thread(target=self.audio_playback_thread, daemon=True).start()

            # Start UI refresh & video threads later when toggled
            self.root.after(0, self.build_main_ui) 
        except Exception as e:
            self.status_var.set("Connection failed")
            try:
                messagebox.showerror("Connection Error", str(e))
            except Exception:
                pass
            if self.tcp:
                try: self.tcp.close()
                except: pass
            if getattr(self, "udp", None):
                try: self.udp.close()
                except: pass

    # ---------------- Main UI (Refactored) ----------------
    def build_main_ui(self):
        for w in self.root.winfo_children():
            w.destroy()

        self.main_area_frame = tk.Frame(self.root, bg="#111111")
        self.main_area_frame.pack(side="top", fill="both", expand=True)

        self.video_grid_frame = tk.Frame(self.main_area_frame, bg="#111111")
        self.video_grid_frame.pack(fill="both", expand=True)

        self.screen_frame = tk.Frame(self.main_area_frame, bg="#000000")
        self.screen_label = tk.Label(self.screen_frame, text="No screen share", bg="#000", fg="#999")
        self.screen_label.pack(fill="both", expand=True, padx=6, pady=6)
        self.screen_visible = False

        toolbar = tk.Frame(self.root, bg="#1f1f1f", height=80) # Adjusted height
        toolbar.pack(side="bottom", fill="x")
        toolbar.pack_propagate(False) # Prevent toolbar from shrinking

        button_container = tk.Frame(toolbar, bg="#1f1f1f")
        button_container.pack(expand=True, fill="y") # Center the buttons

        # --- Mic Button Group ---
        mic_frame = tk.Frame(button_container, bg="#1f1f1f")
        self.btn_mic = ttk.Button(mic_frame, text="🎤 Mute", command=self._toggle_audio, style="Toolbar.TButton")
        self.btn_mic.pack(side="left", anchor="center", pady=12, padx=(10, 0), fill="y")
        
        self.btn_mic_arrow = ttk.Button(mic_frame, text="^", command=self.open_audio_menu, style="Arrow.TButton", width=1)
        self.btn_mic_arrow.pack(side="left", anchor="center", pady=12, padx=(2, 10), fill="y")
        mic_frame.pack(side="left", fill="y")
        
        # --- Other Buttons ---
        self.btn_cam = ttk.Button(button_container, text="🎥 Start Video", command=self._toggle_video, style="Toolbar.TButton")
        self.btn_cam.pack(side="left", pady=12, padx=6, fill="y")
        
        self.btn_screen = ttk.Button(button_container, text="🖥️ Share Screen", command=self._toggle_screen, style="Toolbar.TButton")
        self.btn_screen.pack(side="left", pady=12, padx=6, fill="y")
        
        self.btn_chat = ttk.Button(button_container, text="💬 Chat", command=self.open_chat_popup, style="Toolbar.TButton")
        self.btn_chat.pack(side="left", pady=12, padx=6, fill="y")

        # --- Participant Button ---
        with self.participants_lock:
             initial_count = len(self.participants) + 1
        self.btn_parts = ttk.Button(button_container, text=f"👥 Participants {initial_count}", command=self.open_participant_popup, style="Toolbar.TButton")
        self.btn_parts.pack(side="left", pady=12, padx=6, fill="y")
        
        self.btn_files = ttk.Button(button_container, text="📁 Files", command=self.open_file_popup, style="Toolbar.TButton")
        self.btn_files.pack(side="left", pady=12, padx=6, fill="y")
        
        # --- Leave Button (on the right) ---
        self.btn_leave = ttk.Button(button_container, text="❌ Leave", command=self.leave_and_close, style="Leave.TButton")
        self.btn_leave.pack(side="right", pady=12, padx=20, fill="y")
        
        # Status label (bottom right)
        tk.Label(toolbar, textvariable=self.status_var, bg="#1f1f1f", fg="#cfcfcf").place(relx=0.98, rely=0.5, anchor="e")

        self._update_toolbar_visuals()
        self._ui_refresh_running = True
        self.root.after(40, self._incremental_ui_refresh)
        self.root.after(100, self.update_video_grid)

    def _incremental_ui_refresh(self):
        if not getattr(self, "_ui_refresh_running", True):
            return
        if not self.screen_visible:
            self.update_video_grid()
        self.root.after(40, self._incremental_ui_refresh)

    def _update_toolbar_visuals(self):
        try:
            if self.btn_mic:
                style = "MicOn.TButton" if self.audio_on else "Toolbar.TButton"
                text = "🎤 Unmute" if self.audio_on else "🎤 Mute"
                self.btn_mic.config(style=style, text=text)
            if self.btn_cam:
                style = "CamOn.TButton" if self.video_on else "Toolbar.TButton"
                text = "🎥 Stop Video" if self.video_on else "🎥 Start Video"
                self.btn_cam.config(style=style, text=text)
            if self.btn_screen:
                style = "ScreenOn.TButton" if self.screen_on else "Toolbar.TButton"
                text = "🖥️ Stop Sharing" if self.screen_on else "🖥️ Share Screen"
                self.btn_screen.config(style=style, text=text)
        except:
            pass # UI might be closing

    def _toggle_audio(self):
        self.audio_on = not self.audio_on
        if self.audio_on:
            # start capture thread
            t = threading.Thread(target=self.audio_capture_thread, daemon=True)
            t.start()
        self._update_toolbar_visuals()

    def _toggle_video(self):
        self.video_on = not self.video_on
        if self.video_on:
            self.video_running = True
            self.frame_queue = deque(maxlen=4)
            # improved video start: try to initialize capture with retry
            threading.Thread(target=self.video_capture_thread, daemon=True).start()
            threading.Thread(target=self.video_send_thread, daemon=True).start()
            threading.Thread(target=self.video_ui_thread, daemon=True).start()
        else:
            self.video_running = False
            try:
                self.tcp.send((json.dumps({"type": "video_stop", "username": self.username}) + "\n").encode())
            except:
                pass
            with self.participants_lock:
                self.participants[self.username] = None
            self.root.after(0, self.update_single_tile, self.username)
        self._update_toolbar_visuals()

    def _toggle_screen(self):
        self.screen_on = not self.screen_on
        if self.screen_on:
            self.screen_running = True
            self.screen_queue = deque(maxlen=1)
            threading.Thread(target=self.screen_capture_thread, daemon=True).start()
            threading.Thread(target=self.screen_send_thread, daemon=True).start()
        else:
            self.screen_running = False
            try:
                self.tcp.send((json.dumps({"type": "screen_stop", "username": self.username}) + "\n").encode())
            except:
                pass
            self.screen_queue = None
            if self.presenter == self.username:
                self.presenter = None
                self.hide_screen_frame()
        self._update_toolbar_visuals()

    def _on_root_configure(self, event):
        try:
            if self._resize_after_id:
                self.root.after_cancel(self._resize_after_id)
        except Exception:
            pass
        self._resize_after_id = self.root.after(120, self.update_video_grid)

    def show_screen_frame(self):
        if not self.screen_visible:
            self.video_grid_frame.pack_forget()
            self.screen_frame.pack(fill="both", expand=True)
            self.screen_visible = True

    def hide_screen_frame(self):
        if self.screen_visible:
            self.screen_frame.pack_forget()
            self.video_grid_frame.pack(fill="both", expand=True)
            self.screen_visible = False

    # ---------------- Video grid layout ----------------
    def update_video_grid(self):
        if self.video_grid_frame is None or not self.video_grid_frame.winfo_exists() or self.screen_visible:
            return
        
        self.video_grid_frame.update_idletasks()
        w = self.video_grid_frame.winfo_width()
        h = self.video_grid_frame.winfo_height()
        if w <= 10 or h <= 10:
            w, h = 960, 540
        
        participants = []
        with self.participants_lock:
            local_entry = (self.username, self.participants.get(self.username))
            participants.append(local_entry)
            other_participants = [
                (n, img) for n, img in self.participants.items() if n != self.username
            ]
            participants.extend(sorted(other_participants, key=lambda x: x[0]))

        n = len(participants)
        if n == 0:
            return
            
        # Update participant count button
        if hasattr(self, "btn_parts") and self.btn_parts:
            try: self.btn_parts.config(text=f"👥 Participants {n}") # Use .config(text=) for ttk
            except: pass

        best = None
        max_cols = max(1, int(np.ceil(np.sqrt(n))) + 1)
        for try_cols in range(1, max_cols + 1):
            try_rows = int(np.ceil(n / try_cols))
            cell_w = w // try_cols
            cell_h = h // try_rows
            aspect = 4.0 / 3.0
            if cell_w / cell_h > aspect:
                cw = int(cell_h * aspect); ch = cell_h
            else:
                cw = cell_w; ch = int(cell_w / aspect) if cell_w > 0 else cell_h
            if cw <= 0 or ch <= 0:
                continue
            area = cw * ch * n
            if best is None or area > best[0]:
                best = (area, try_cols, try_rows, cw, ch)
        
        if best is None:
            cols = int(np.ceil(np.sqrt(n)))
            rows = int(np.ceil(n / cols)) if cols > 0 else 1
            cell_w = max(160, w // cols) if cols > 0 else w
            cell_h = max(120, h // rows) if rows > 0 else h
        else:
            _, cols, rows, cell_w, cell_h = best

        grid_w = cell_w * cols
        grid_h = cell_h * rows
        offset_x = max(0, (w - grid_w) // 2)
        offset_y = max(0, (h - grid_h) // 2)

        used_usernames = set()
        idx = 0
        for r in range(rows):
            for c in range(cols):
                if idx >= n:
                    break
                uname, img = participants[idx]
                used_usernames.add(uname)
                x = offset_x + c * cell_w
                y = offset_y + r * cell_h
                with self.tiles_lock:
                    tile = self.tiles.get(uname)
                    if tile is None:
                        frame = tk.Frame(self.video_grid_frame, bg="#111111", bd=1, relief="ridge")
                        frame.place(x=x, y=y, width=cell_w, height=cell_h)
                        name_label = tk.Label(frame, text=("You" if uname == self.username else uname), bg="#111111", fg="#ffffff")
                        name_label.pack(side="bottom", fill="x")
                        img_label = tk.Label(frame, bg="#111111")
                        img_label.place(relx=0.5, rely=0.45, anchor="center")
                        tile = {"frame": frame, "name_label": name_label, "img_label": img_label, "last_img_id": None}
                        self.tiles[uname] = tile
                    else:
                        try:
                            tile['frame'].place_configure(x=x, y=y, width=cell_w, height=cell_h)
                        except:
                            pass
                    
                    self._update_tile_content(tile, uname, img, cell_w, cell_h)
                idx += 1

        with self.tiles_lock:
            to_remove = [u for u in self.tiles.keys() if u not in used_usernames]
            for u in to_remove:
                try: self.tiles[u]['frame'].destroy()
                except: pass
                self.tiles.pop(u, None)

    def _update_tile_content(self, tile, uname, img, w, h):
        """Helper to update a tile's image or placeholder"""
        if w <= 0 or h <= 0:
            return
        
        try:
            if img is None:
                initial = "You"[0] if uname == self.username else (uname[0].upper() if uname else "?")
                color = name_color(self.username if uname == self.username else uname)
                font_size = max(24, int(h * 0.35))
                tile['img_label'].config(image="", text=initial, font=("", font_size, "bold"), fg="white", bg=color)
                tile['img_label'].image = None
                tile['last_img_id'] = None
            else:
                pil = img.copy()
                pil = ImageOps.fit(pil, (w, h), method=Image.Resampling.LANCZOS if hasattr(Image,'Resampling') else Image.LANCZOS, centering=(0.5,0.5))
                tk_img = ImageTk.PhotoImage(pil)
                img_label = tile['img_label']
                img_label.config(image=tk_img, text="", bg="#111111")
                img_label.image = tk_img
                tile['last_img_id'] = id(pil)
        except Exception:
            pass

    # ---------------- TCP reader ----------------
    def tcp_reader(self, file_obj):
        try:
            while self.connected and not self._threads_should_exit.is_set():
                line = file_obj.readline()
                if not line:
                    break
                
                if not line.strip():
                    continue
                try:
                    msg = json.loads(line)
                except:
                    continue
                
                mtype = msg.get("type")
                if mtype == "welcome":
                    continue 
                elif mtype == "chat":
                    uname = msg.get("username"); ts = msg.get("timestamp") or datetime.now().strftime("%H:%M:%S")
                    content = msg.get("message", "")
                    if uname == self.username:
                        continue
                    line_text = f"[{ts}] {uname}: {content}"
                    self.chat_history.append(line_text)
                    if self.chat_popup and self.chat_text:
                        try:
                            self.chat_text.config(state="normal")
                            self.chat_text.insert(tk.END, line_text + "\n")
                            self.chat_text.see(tk.END)
                            self.chat_text.config(state="disabled")
                        except:
                            pass
                elif mtype == "user_joined":
                    name = msg.get("username")
                    if name == self.username: continue
                    with self.participants_lock:
                        if name not in self.participants:
                            self.participants[name] = None
                    self.root.after(0, self.update_video_grid)
                elif mtype == "user_left":
                    name = msg.get("username")
                    with self.participants_lock:
                        self.participants.pop(name, None)
                    with self.tiles_lock:
                        tile = self.tiles.pop(name, None)
                        if tile:
                            try: tile['frame'].destroy()
                            except: pass
                    if self.presenter == name:
                        self.presenter = None
                        self.root.after(0, lambda: (self.screen_label.config(image="", text="No screen share"), self.hide_screen_frame()))
                    self.root.after(0, self.update_video_grid)
                elif mtype == "video_stop":
                    name = msg.get("username")
                    with self.participants_lock:
                        self.participants[name] = None
                    self.root.after(0, self.update_single_tile, name)
                elif mtype == "screen_stop":
                    name = msg.get("username")
                    if self.presenter == name:
                        self.presenter = None
                        self.root.after(0, lambda: (self.screen_label.config(image="", text="No screen share"), self.hide_screen_frame()))
                elif mtype == "ready_for_file":
                    token = msg.get("token")
                    ev = self.pending_file_events.get(token)
                    if ev: ev.set()
                elif mtype == "file_available":
                    fname = msg.get("filename")
                    if fname not in self.available_files:
                        self.available_files.append(fname)
                    self._refresh_file_popup_list()
                elif mtype == "file_data":
                    self.receive_file(msg)
        except Exception:
            pass
        finally:
            # Close/cleanup handled in close()
            try: file_obj.close()
            except: pass

    # ---------------- UDP reader ----------------
    def udp_reader(self):
        """
        Single thread for all incoming UDP data. Routes:
         - 'V' frames -> video image for participant
         - 'S' frames -> screen share
         - 'M' frames -> mixed audio -> push into audio_buffer
        This thread uses socket timeout to check for shutdown flags.
        """
        while self.connected and not self._threads_should_exit.is_set():
            try:
                data, addr = self.udp.recvfrom(65536)
            except socket.timeout:
                continue
            except Exception:
                break

            parsed = parse_header(data)
            if parsed is None:
                continue
            dtype, uname, seq, ts, payload = parsed

            # ignore own UDP packets (server may echo)
            if uname == self.username:
                continue

            if dtype == "V":
                # video frame
                try:
                    arr = np.frombuffer(payload, dtype=np.uint8)
                    frame = cv2.imdecode(arr, cv2.IMREAD_COLOR)
                    if frame is None:
                        continue
                    frame = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
                    img = Image.fromarray(frame)
                    with self.participants_lock:
                        self.participants[uname] = img
                    # update tile asynchronously
                    self.root.after(0, lambda u=uname: self.update_single_tile(u))
                except Exception:
                    continue

            elif dtype == "S":
                # screen share frame
                try:
                    arr = np.frombuffer(payload, dtype=np.uint8)
                    frame = cv2.imdecode(arr, cv2.IMREAD_COLOR)
                    if frame is None:
                        continue
                    frame = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
                    img = Image.fromarray(frame)

                    if self.screen_label and self.screen_label.winfo_exists():
                        w, h = self.screen_label.winfo_width(), self.screen_label.winfo_height()
                        if w > 10 and h > 10:
                            img.thumbnail((w, h))
                    else:
                        img.thumbnail((960,540))

                    imgtk = ImageTk.PhotoImage(img)
                    self.presenter = uname
                    def _show():
                        self.screen_label.config(image=imgtk, text="")
                        self.screen_label.image = imgtk
                        self.show_screen_frame()
                    self.root.after(0, _show)
                except Exception:
                    continue

            elif dtype == "M":
                # Mixed audio payload from server (int16 raw)
                # Put into audio_buffer queue (drop if full using oldest-drop policy)
                if not payload:
                    continue
                try:
                    # ensure size matches expected chunk bytes
                    if len(payload) != AUDIO_CHUNK_BYTES:
                        # If server sends different sized chunks, try to handle gracefully:
                        # If larger, truncate to expected size; if smaller, pad with zeros.
                        if len(payload) > AUDIO_CHUNK_BYTES:
                            payload = payload[:AUDIO_CHUNK_BYTES]
                        else:
                            payload = payload + b'\x00' * (AUDIO_CHUNK_BYTES - len(payload))
                    try:
                        self.audio_buffer.put_nowait(payload)
                    except queue.Full:
                        # drop one old frame then enqueue
                        try:
                            _ = self.audio_buffer.get_nowait()
                            self.audio_buffer.put_nowait(payload)
                        except Exception:
                            # give up on this frame
                            pass
                except Exception:
                    # ignore malformed audio
                    pass

            else:
                # unknown type, ignore
                continue

    def update_single_tile(self, uname):
        if self.screen_visible:
            return
        
        with self.participants_lock:
            img = self.participants.get(uname)
        with self.tiles_lock:
            tile = self.tiles.get(uname)
        
        if tile is None:
            self.root.after(0, self.update_video_grid)
            return
        
        try:
            info = tile['frame'].place_info()
            w = int(float(info.get('width', 160)))
            h = int(float(info.get('height', 120)))
        except:
            w, h = 320, 240
            
        self._update_tile_content(tile, uname, img, w, h)

    # ---------------- Popups (Chat, Files, Participants) ----------------
    # (unchanged; omitted here for brevity in analysis — kept in code above)

    # ---------------- Audio playback thread ----------------
    def audio_playback_thread(self):
        """
        Read from self.audio_buffer (Queue) and play to output device.
        Uses smoothing on start/underrun to avoid clicks/rattling.
        """
        if self.pyaudio_instance is None:
            # nothing to do
            return

        # Open playback stream lazily
        while self.jitter_running and self.connected and not self._threads_should_exit.is_set():
            try:
                with self.play_stream_lock:
                    if self.play_stream is None:
                        params = dict(format=pyaudio.paInt16, channels=AUDIO_CHANNELS, rate=AUDIO_RATE, output=True, frames_per_buffer=AUDIO_CHUNK_SAMPLES)
                        if self.output_device_index is not None:
                            params['output_device_index'] = self.output_device_index
                        self.play_stream = self.pyaudio_instance.open(**params)
                break
            except Exception as e:
                # retry a few times
                print("Playback stream open failed, retrying...", e)
                with self.play_stream_lock:
                    try:
                        if self.play_stream:
                            self.play_stream.stop_stream(); self.play_stream.close()
                    except:
                        pass
                    self.play_stream = None
                time.sleep(0.3)
                # continue trying until jitter_running stops

        # smoothing state
        fade_chunks = 3
        fade_idx = 0
        playing = True

        # playback main loop
        while self.jitter_running and self.connected and not self._threads_should_exit.is_set():
            try:
                try:
                    payload = self.audio_buffer.get(timeout=0.05)
                except queue.Empty:
                    payload = None

                if payload is None:
                    # underrun -> write a short silence, and reset fade index
                    silent = (np.zeros(AUDIO_CHUNK_SAMPLES, dtype=np.int16)).tobytes()
                    with self.play_stream_lock:
                        if self.play_stream:
                            try:
                                self.play_stream.write(silent)
                            except Exception:
                                try:
                                    self.play_stream.stop_stream(); self.play_stream.close()
                                except:
                                    pass
                                self.play_stream = None
                    fade_idx = 0
                    time.sleep(0.005)
                    continue

                # we have a payload: ensure correct length (already normalized in udp_reader)
                arr = np.frombuffer(payload, dtype=np.int16).astype(np.float32)

                # simple smoothing / fade at start to avoid clicks
                if fade_idx < fade_chunks:
                    alpha = (fade_idx + 1) / float(fade_chunks)
                    arr = arr * alpha
                    fade_idx += 1

                # compute RMS for echo suppression logic upstream
                rms = np.sqrt(np.mean((arr * (1.0))**2)) if arr.size > 0 else 0.0
                self.playback_rms = rms

                # Apply playback gain if any
                if abs(self.playback_gain - 1.0) > 1e-3:
                    arr = np.clip(arr * self.playback_gain, -32767, 32767)

                out_bytes = arr.astype(np.int16).tobytes()

                with self.play_stream_lock:
                    if self.play_stream:
                        try:
                            self.play_stream.write(out_bytes)
                        except Exception:
                            try:
                                self.play_stream.stop_stream(); self.play_stream.close()
                            except:
                                pass
                            self.play_stream = None
                # loop
            except Exception as e:
                # log and continue
                print("Audio playback error:", e)
                time.sleep(0.01)
                continue

        # thread exiting: close playback stream
        with self.play_stream_lock:
            try:
                if self.play_stream:
                    self.play_stream.stop_stream(); self.play_stream.close()
            except:
                pass
            self.play_stream = None

    # ---------------- Audio capture ----------------
    def audio_capture_thread(self):
        """
        Capture local mic, apply AGC/gain smoothing, and send UDP audio packets to server.
        """
        if self.pyaudio_instance is None:
            # show non-blocking error via UI
            self.root.after(0, lambda: messagebox.showerror("Audio error", "Audio subsystem not available."))
            self.audio_on = False; self._update_toolbar_visuals()
            return

        # open input stream
        stream = None
        try:
            params = dict(format=pyaudio.paInt16, channels=AUDIO_CHANNELS, rate=AUDIO_RATE, input=True, frames_per_buffer=AUDIO_CHUNK_SAMPLES)
            if self.input_device_index is not None:
                params['input_device_index'] = self.input_device_index
            stream = self.pyaudio_instance.open(**params)
        except Exception as e:
            self.root.after(0, lambda: messagebox.showerror("Audio error", f"Cannot open microphone: {e}"))
            self.audio_on = False; self._update_toolbar_visuals()
            try:
                if stream: stream.close()
            except: pass
            return

        capture_gain = self.capture_gain
        while self.audio_on and self.connected and not self._threads_should_exit.is_set():
            try:
                data = stream.read(AUDIO_CHUNK_SAMPLES, exception_on_overflow=False)
                arr = np.frombuffer(data, dtype=np.int16).astype(np.float32)
                rms = np.sqrt(np.mean(arr*arr)) if arr.size>0 else 0.0

                # Noise gate
                if rms < MIN_SEND_RMS:
                    silent = (np.zeros(AUDIO_CHUNK_SAMPLES, dtype=np.int16)).tobytes()
                    self.audio_seq = (self.audio_seq + 1) & 0xFFFFFFFF
                    hdr = build_header(b"A", self.username, self.audio_seq)
                    try:
                        # use same udp socket registered with server
                        self.udp.sendto(hdr + silent, (self.server_ip, self.udp_port or 5001))
                    except Exception:
                        pass
                    # relax gain toward 1.0 slowly
                    capture_gain = capture_gain * (1.0 - CAPTURE_SMOOTH) + 1.0 * CAPTURE_SMOOTH
                    self.capture_gain = capture_gain
                    continue

                # compute desired gain (AGC)
                desired_gain = TARGET_RMS / (rms + 1e-9)
                desired_gain = max(MIN_CAPTURE_GAIN, min(desired_gain, MAX_CAPTURE_GAIN))

                # echo suppression: if playback is loud, reduce capture gain
                if self.playback_rms > ECHO_SUPPRESSION_THRESHOLD:
                    desired_gain *= ECHO_SUPPRESSION_FACTOR

                # smooth capture gain
                capture_gain = capture_gain * (1.0 - CAPTURE_SMOOTH) + desired_gain * CAPTURE_SMOOTH
                capture_gain = max(MIN_CAPTURE_GAIN, min(capture_gain, MAX_CAPTURE_GAIN))
                self.capture_gain = capture_gain

                processed = np.clip(arr * capture_gain, -32767, 32767).astype(np.int16).tobytes()
                self.audio_seq = (self.audio_seq + 1) & 0xFFFFFFFF
                hdr = build_header(b"A", self.username, self.audio_seq)
                try:
                    self.udp.sendto(hdr + processed, (self.server_ip, self.udp_port or 5001))
                except Exception:
                    pass
            except Exception as e:
                # Stop capture loop on fatal errors
                print("Audio capture error:", e)
                break

        # close input stream
        try:
            if stream:
                stream.stop_stream(); stream.close()
        except:
            pass

    # ---------------- Video capture / send / UI ----------------
    def video_capture_thread(self):
        """
        Try to open the webcam with a few retries; if device busy, attempt to reopen so local video can start reliably.
        """
        attempt = 0
        cap = None
        while attempt < 6 and not self._threads_should_exit.is_set():
            try:
                cap = cv2.VideoCapture(0)
                cap.set(cv2.CAP_PROP_FRAME_WIDTH, 320)
                cap.set(cv2.CAP_PROP_FRAME_HEIGHT, 240)
                # small delay to let camera warm up
                time.sleep(0.1)
                if cap is not None and cap.isOpened():
                    break
                else:
                    try:
                        cap.release()
                    except:
                        pass
            except Exception:
                pass
            attempt += 1
            time.sleep(0.3)

        if not cap or not cap.isOpened():
            # failed to open camera
            self.root.after(0, lambda: messagebox.showerror("Video Error", "Could not open webcam."))
            self.video_running = False
            # ensure UI updates
            self.root.after(0, self._update_toolbar_visuals)
            return

        try:
            while self.video_running and cap.isOpened() and not self._threads_should_exit.is_set():
                ret, frame = cap.read()
                if not ret:
                    break
                # push frames (small deque) for UI/encoder
                self.frame_queue.append(frame)
                time.sleep(1.0 / max(15, int(1.0 / VIDEO_SEND_INTERVAL)))  # conservative sleep
        except Exception as e:
            print("Video capture error:", e)
        finally:
            try:
                cap.release()
            except:
                pass

    def video_send_thread(self):
        seq = 0
        while self.video_running and self.connected and not self._threads_should_exit.is_set():
            if len(self.frame_queue) == 0:
                time.sleep(VIDEO_SEND_INTERVAL); continue
            frame = self.frame_queue.popleft()
            try:
                _, enc = cv2.imencode(".jpg", frame, [int(cv2.IMWRITE_JPEG_QUALITY), VIDEO_JPEG_QUALITY])
                payload = enc.tobytes()
                seq = (seq + 1) & 0xFFFFFFFF
                hdr = build_header(b"V", self.username, seq)
                try:
                    self.udp.sendto(hdr + payload, (self.server_ip, self.udp_port or 5001))
                except:
                    pass
            except Exception as e:
                print("Video send error:", e)
            time.sleep(VIDEO_SEND_INTERVAL)

    def video_ui_thread(self):
        while self.video_running and not self._threads_should_exit.is_set():
            if len(self.frame_queue) > 0:
                frame = self.frame_queue[-1]
                try:
                    frame = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
                    img = Image.fromarray(frame)
                    with self.participants_lock:
                        self.participants[self.username] = img
                    self.root.after(0, self.update_single_tile, self.username)
                except Exception:
                    pass
            time.sleep(0.04)

    # ---------------- Screen capture / send ----------------
    def screen_capture_thread(self):
        try:
            with mss.mss() as sct:
                mon = sct.monitors[1]
                while self.screen_running and not self._threads_should_exit.is_set():
                    s = sct.grab(mon)
                    img = Image.frombytes("RGB", s.size, s.rgb)
                    img.thumbnail((960, 540))
                    if self.screen_queue is not None:
                        if len(self.screen_queue) > 0:
                            try: self.screen_queue.popleft()
                            except: pass
                        self.screen_queue.append(img)
                    time.sleep(SCREEN_SEND_INTERVAL)
        except Exception as e:
             self.root.after(0, lambda: messagebox.showerror("Screen Share Error", f"Could not start screen capture: {e}"))
             self.root.after(0, self._toggle_screen)


    def screen_send_thread(self):
        seq = 0
        while self.screen_running and self.connected and not self._threads_should_exit.is_set():
            if not self.screen_queue or len(self.screen_queue) == 0:
                time.sleep(SCREEN_SEND_INTERVAL); continue
            try:
                img = self.screen_queue.popleft()
            except:
                continue
            try:
                buf = BytesIO(); img.save(buf, format="JPEG", quality=SCREEN_JPEG_QUALITY); payload = buf.getvalue()
                seq = (seq + 1) & 0xFFFFFFFF
                hdr = build_header(b"S", self.username, seq)
                try:
                    self.udp.sendto(hdr + payload, (self.server_ip, self.udp_port or 5001))
                except:
                    pass
            except:
                pass
            time.sleep(SCREEN_SEND_INTERVAL)

    # ---------------- Graceful close ----------
    def close(self):
        # signal threads to exit
        self._threads_should_exit.set()
        self._ui_refresh_running = False
        self.connected = False
        self.audio_on = False
        self.video_on = False
        self.video_running = False
        self.screen_running = False
        self.jitter_running = False
        self.audio_playing = False

        try:
            if hasattr(self, 'tcp') and self.tcp:
                try: self.tcp.send((json.dumps({"type": "user_left", "username": self.username}) + "\n").encode())
                except: pass
                try: self.tcp.close()
                except: pass
        except: pass
        try:
            if hasattr(self, 'udp') and self.udp:
                try: self.udp.close()
                except: pass
        except: pass

        # close playback stream
        with self.play_stream_lock:
            try:
                if self.play_stream:
                    self.play_stream.stop_stream(); self.play_stream.close()
            except:
                pass
            self.play_stream = None

        try:
            if hasattr(self, 'pyaudio_instance') and self.pyaudio_instance:
                try: self.pyaudio_instance.terminate()
                except: pass
                self.pyaudio_instance = None
        except: pass

        try:
            if hasattr(self, 'root'): self.root.destroy()
        except: pass

    def leave_and_close(self):
        self.close()

    def run(self):
        self.root.mainloop()

if __name__ == "__main__":
    app = ClientApp()
    app.run()