#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
LAN Chat & File Sharing (command line)
======================================

Peer-to-peer chat that uses BOTH transport protocols, each for what it is best at:

  * UDP  -> peer discovery + online status   (HELLO broadcast every 3 s, timeout 10 s)
  * TCP  -> chat messages + file transfer    (reliable, ordered, length-framed)

Only the native socket API of the standard library is used (no third-party package).

Run:   python lanchat.py --name Quan
       python lanchat.py --name Minh            (second instance / second computer)

Thread model
------------
  main thread      keyboard  -> read input, run commands, send messages
  udp-broadcast    timer     -> send presence message (HELLO) every 3 s
  udp-listen       UDP recv  -> update online-user list, expire silent peers (10 s)
  tcp-accept       accept()  -> start one receiver thread per incoming connection
  recv-<peer>      TCP recv  -> show messages, save incoming files
  send-file        (per transfer) -> push a file without blocking the chat

Wire protocol (see README.md for the full description)
-----------------------------------------------------
  UDP datagram   HELLO|<name>|<tcp_port>|<status>      (also BYE|<name>|<tcp_port>)
  TCP frames     ID|<name>|<tcp_port>|<chat|file>|     first frame on every connection
                 MSG|<length>|<utf-8 bytes>
                 FILE|<url-quoted filename>|<size>|<raw bytes>
                 BYE|
                 OK|                                   receiver -> sender, file saved
"""

from __future__ import annotations

import argparse
import codecs
import itertools
import os
import re
import shutil
import socket
import sys
import threading
import time
import unicodedata
from collections import deque
from dataclasses import dataclass
from typing import Callable, Dict, List, Optional, Tuple
from urllib.parse import quote, unquote

# --------------------------------------------------------------------------- #
# Constants
# --------------------------------------------------------------------------- #
UDP_PORT = 9999              # fixed discovery port
DEFAULT_TCP_PORT = 5000      # first TCP port tried when --port is not given
HELLO_INTERVAL = 3.0         # seconds between presence broadcasts
PEER_TIMEOUT = 10.0          # a peer not heard from for this long is "offline"
CONNECT_TIMEOUT = 5.0        # TCP connect / handshake timeout
FILE_STALL_TIMEOUT = 30.0    # abort a file transfer if no data moves for this long
CHUNK = 64 * 1024            # file transfer chunk size
MAX_MSG = 1024 * 1024        # largest accepted chat message (bytes)
MAX_FIELD = 4096             # largest accepted header field (bytes)
STATUSES = ("online", "away")

HELP_TEXT = """\
Commands:
  /list                    show online users (number, name, IP, status)
  /chat <name|number>      open a chat with a user (TCP connection)
  <any text>               send a message to the current chat partner
  /send <file>             send a file to the current chat partner
  /leave                   close the current chat
  /status <online|away>    change your status (sent via UDP)
  /help                    show this help
  /quit                    exit the program"""


# --------------------------------------------------------------------------- #
# Small helpers
# --------------------------------------------------------------------------- #
def clean_name(raw: str, maxlen: int = 20) -> str:
    """Names travel inside '|' separated headers: no separators / control chars."""
    raw = re.sub(r"[\s|]+", "_", raw.strip())
    return "".join(ch for ch in raw if ch.isprintable())[:maxlen]


def sanitize_text(text: str) -> str:
    """Strip control characters from remote text (prevents terminal escape injection)."""
    return "".join(ch if ch.isprintable() else "?" for ch in text)


def human_size(n: int) -> str:
    if n < 1024:
        return f"{n} B"
    size = float(n)
    for unit in ("KB", "MB", "GB", "TB"):
        size /= 1024.0
        if size < 1024 or unit == "TB":
            return f"{size:.1f} {unit}"
    return f"{n} B"


def shorten(text: str, limit: int = 40) -> str:
    return text if len(text) <= limit else text[: limit - 3] + "..."


def disp_width(text: str) -> int:
    """Number of terminal columns used by *text* (handles wide / combining chars)."""
    width = 0
    for ch in text:
        if unicodedata.combining(ch):
            continue
        width += 2 if unicodedata.east_asian_width(ch) in ("W", "F") else 1
    return width


def safe_filename(name: str) -> str:
    """Never trust a file name received from the network (path traversal etc.)."""
    name = os.path.basename(name.replace("\\", "/"))
    name = "".join(ch if ch.isprintable() and ch not in '<>:"/\\|?*' else "_" for ch in name)
    return name.strip(" .")[:200] or "file"


def open_unique(directory: str, name: str):
    """Create '<name>.part' for a destination that does not exist yet.
    Returns (file object, final path). Adds ' (1)', ' (2)', ... if needed."""
    base, ext = os.path.splitext(name)
    n = 0
    while True:
        candidate = name if n == 0 else f"{base} ({n}){ext}"
        dest = os.path.join(directory, candidate)
        if not os.path.exists(dest):
            try:
                return open(dest + ".part", "xb"), dest
            except FileExistsError:
                pass
        n += 1


def is_loopback(ip: str) -> bool:
    return ip.startswith("127.")


def local_broadcast_targets(extra: List[str]) -> List[str]:
    """Where HELLO datagrams are sent.

    * 255.255.255.255        limited broadcast (works on most single-NIC setups)
    * a.b.c.255 per local IP directed broadcast (more reliable with several NICs;
                             /24 is assumed)
    * 127.255.255.255        loopback broadcast: several instances on ONE machine
                             and no-network testing
    * anything given with --broadcast
    """
    targets: List[str] = ["255.255.255.255"]
    ips = set()
    try:
        probe = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try:
            probe.connect(("8.8.8.8", 9))     # UDP connect: nothing is sent
            ips.add(probe.getsockname()[0])
        finally:
            probe.close()
    except OSError:
        pass
    try:
        ips.update(socket.gethostbyname_ex(socket.gethostname())[2])
    except OSError:
        pass
    for ip in sorted(ips):
        parts = ip.split(".")
        if len(parts) == 4 and not is_loopback(ip) and ip != "0.0.0.0":
            targets.append(".".join(parts[:3] + ["255"]))
    targets.append("127.255.255.255")
    targets.extend(extra)
    seen, result = set(), []
    for t in targets:
        if t not in seen:
            seen.add(t)
            result.append(t)
    return result


# --------------------------------------------------------------------------- #
# TCP framing
# --------------------------------------------------------------------------- #
class ConnectionClosed(Exception):
    """The peer closed the connection (EOF while we still expected data)."""


class ProtocolError(Exception):
    """The peer sent something that is not valid protocol."""


def build_frame(ftype: str, *fields, payload: bytes = b"") -> bytes:
    """TYPE|field1|field2|<payload>   (every header field is terminated by '|')."""
    head = "|".join([ftype] + [str(f) for f in fields]) + "|"
    return head.encode("utf-8") + payload


class SocketReader:
    """Reads a TCP byte stream: header fields up to '|' and exact byte counts.

    TCP has no message boundaries: one recv() may return half a frame or several
    frames, so everything goes through an internal buffer and loops on recv()
    until the requested amount has arrived.
    """

    def __init__(self, sock: socket.socket):
        self.sock = sock
        self.buf = bytearray()

    def _fill(self) -> None:
        data = self.sock.recv(65536)
        if not data:
            raise ConnectionClosed("connection closed by peer")
        self.buf += data

    def read_field(self, maxlen: int = MAX_FIELD) -> str:
        """Return the text up to the next '|' (the '|' is consumed)."""
        while True:
            idx = self.buf.find(b"|")
            if idx >= 0:
                field = bytes(self.buf[:idx])
                del self.buf[: idx + 1]
                return field.decode("utf-8")
            if len(self.buf) > maxlen:
                raise ProtocolError("header field too long")
            self._fill()

    def read_exact(self, n: int) -> bytes:
        """Loop on recv() until exactly n bytes have arrived."""
        while len(self.buf) < n:
            self._fill()
        data = bytes(self.buf[:n])
        del self.buf[:n]
        return data

    def read_chunk(self, max_n: int) -> bytes:
        """Return between 1 and max_n bytes (used to stream big files to disk)."""
        if not self.buf:
            self._fill()
        data = bytes(self.buf[:max_n])
        del self.buf[:max_n]
        return data


class Connection:
    """One TCP connection to a peer (chat or single file transfer)."""

    def __init__(self, sock: socket.socket, peer: str, remote_ip: str, remote_port: int,
                 initiated_by_me: bool, kind: str = "chat"):
        self.sock = sock
        self.peer = peer
        self.remote_ip = remote_ip
        self.remote_port = remote_port      # the peer's *listening* TCP port
        self.initiated_by_me = initiated_by_me
        self.kind = kind
        self.send_lock = threading.Lock()   # frames from two threads never interleave
        self.closed = False
        self.superseded = False             # replaced by a duplicate connection
        self._close_lock = threading.Lock()

    def send(self, data: bytes) -> None:
        with self.send_lock:
            self.sock.sendall(data)

    def close(self) -> None:
        with self._close_lock:
            if self.closed:
                return
            self.closed = True
        try:
            self.sock.shutdown(socket.SHUT_RDWR)   # also wakes up a blocked recv()
        except OSError:
            pass
        try:
            self.sock.close()
        except OSError:
            pass


# --------------------------------------------------------------------------- #
# Console UI: input line is always the last line, history is above it
# --------------------------------------------------------------------------- #
def enable_ansi_on_windows() -> None:
    if os.name != "nt":
        return
    try:
        import ctypes
        kernel32 = ctypes.windll.kernel32
        handle = kernel32.GetStdHandle(-11)                 # STD_OUTPUT_HANDLE
        mode = ctypes.c_uint32()
        if kernel32.GetConsoleMode(handle, ctypes.byref(mode)):
            kernel32.SetConsoleMode(handle, mode.value | 0x0004)   # VT processing
    except Exception:
        os.system("")


class _UnixKeys:
    """Reads one key at a time (cbreak mode: no echo, no line buffering)."""

    def __init__(self):
        import select
        import termios
        import tty
        self._select, self._termios, self._tty = select, termios, tty
        self.fd = sys.stdin.fileno()
        self.old = None
        self.decoder = codecs.getincrementaldecoder("utf-8")(errors="ignore")

    def open(self) -> None:
        self.old = self._termios.tcgetattr(self.fd)
        self._tty.setcbreak(self.fd)          # keeps Ctrl+C -> KeyboardInterrupt

    def close(self) -> None:
        if self.old is not None:
            self._termios.tcsetattr(self.fd, self._termios.TCSADRAIN, self.old)
            self.old = None

    def _readable(self, timeout: float) -> bool:
        return bool(self._select.select([self.fd], [], [], timeout)[0])

    def _skip_escape(self) -> None:
        """Swallow arrow keys / function keys (ESC [ ... final-byte)."""
        if not self._readable(0.05):
            return                             # a lone ESC
        b = os.read(self.fd, 1)
        if b == b"[":
            while self._readable(0.05):
                c = os.read(self.fd, 1)
                if not c or 0x40 <= c[0] <= 0x7E:
                    break
        elif b == b"O" and self._readable(0.05):
            os.read(self.fd, 1)

    def read_key(self) -> str:
        while True:
            b = os.read(self.fd, 1)
            if not b:
                return "\x04"                  # EOF
            if b == b"\x1b":
                self._skip_escape()
                continue
            ch = self.decoder.decode(b)        # multi-byte UTF-8 (Vietnamese...)
            if ch:
                return ch


class _WindowsKeys:
    def __init__(self):
        import msvcrt
        self.msvcrt = msvcrt

    def open(self) -> None:
        pass

    def close(self) -> None:
        pass

    def read_key(self) -> str:
        while True:
            ch = self.msvcrt.getwch()
            if ch in ("\x00", "\xe0"):         # arrow / function key: 2-char code
                self.msvcrt.getwch()
                continue
            if "\ud800" <= ch <= "\udbff":     # first half of a surrogate pair
                low = self.msvcrt.getwch()
                try:
                    return (ch + low).encode("utf-16", "surrogatepass").decode("utf-16")
                except UnicodeError:
                    continue
            return ch


class ConsoleUI:
    """Thread-safe console.

    Every thread prints through print()/update_line(). While the user is typing,
    an incoming message is shown like this (all under one lock):
        1. erase the input line         (\\r + ESC[K, plus ESC[J if it wrapped)
        2. print the message + newline
        3. redraw "> " + whatever the user had typed so far
    """

    PROMPT = "> "

    def __init__(self):
        self.lock = threading.RLock()
        self.interactive = sys.stdin.isatty() and sys.stdout.isatty()
        self.buffer: List[str] = []         # characters typed so far
        self._prompt_shown = False
        self._drawn_width = 0               # columns currently used by the prompt
        self._line_key: Optional[str] = None  # id of the line right above the prompt
        self._line_rows = 0
        self._keys = None

    # -- lifecycle ---------------------------------------------------------
    def open(self) -> None:
        if not self.interactive:            # piped input/output (tests, scripts)
            for stream in (sys.stdout, sys.stdin):
                try:
                    stream.reconfigure(encoding="utf-8", errors="replace")
                except Exception:
                    pass
            return
        enable_ansi_on_windows()
        self._keys = _WindowsKeys() if os.name == "nt" else _UnixKeys()
        self._keys.open()

    def close(self) -> None:
        with self.lock:
            if self._keys is not None:
                self._keys.close()
                self._keys = None
            if self.interactive and self._prompt_shown:
                self._write(self._erase_seq())
            self._prompt_shown = False

    # -- low level ---------------------------------------------------------
    @staticmethod
    def _cols() -> int:
        return max(10, shutil.get_terminal_size((80, 24)).columns)

    def _rows_for(self, text: str) -> int:
        cols = self._cols()
        return sum(max(1, -(-disp_width(line) // cols)) for line in text.split("\n"))

    @staticmethod
    def _write(text: str) -> None:
        sys.stdout.write(text)
        sys.stdout.flush()

    def _erase_seq(self) -> str:
        """Escape sequence that erases the prompt (even if it wrapped on 2+ rows)."""
        width, cols = self._drawn_width, self._cols()
        up = (width - 1) // cols if width > 0 else 0
        self._drawn_width = 0
        return (f"\033[{up}A" if up else "") + "\r\033[K" + ("\033[J" if up else "")

    def _draw_seq(self) -> str:
        text = self.PROMPT + "".join(self.buffer)
        self._drawn_width = disp_width(text)
        return text

    # -- output (any thread) ----------------------------------------------
    def print(self, text: str = "") -> None:
        with self.lock:
            out = []
            show = self.interactive and self._prompt_shown
            if show:
                out.append(self._erase_seq())
            out.append(text + "\n")
            self._line_key = None
            if show:
                out.append(self._draw_seq())
            self._write("".join(out))

    def update_line(self, key: str, text: str, force_new: bool = False) -> None:
        """Show a status line (progress, unread counter).

        If the line with the same *key* is still the one directly above the prompt
        it is rewritten in place; otherwise a new line is printed only when
        *force_new* is true (so concurrent updates cannot flood the screen).
        """
        with self.lock:
            in_place = self.interactive and self._line_key == key and self._line_rows > 0
            if not in_place and not force_new:
                return
            show = self.interactive and self._prompt_shown
            out = []
            if show:
                out.append(self._erase_seq())
            if in_place:
                out.append(f"\033[{self._line_rows}A\r\033[J")
            out.append(text + "\n")
            self._line_key = key
            self._line_rows = self._rows_for(text)
            if show:
                out.append(self._draw_seq())
            self._write("".join(out))

    # -- input (main thread) ----------------------------------------------
    def readline(self) -> str:
        if not self.interactive:
            line = sys.stdin.readline()
            if not line:
                raise EOFError
            return line.rstrip("\r\n")
        with self.lock:
            self.buffer.clear()
            self._prompt_shown = True
            self._write(self._draw_seq())
        while True:
            ch = self._keys.read_key()          # blocks WITHOUT holding the lock
            with self.lock:
                if ch in ("\r", "\n"):
                    self._write(self._erase_seq())
                    self._prompt_shown = False
                    line = "".join(self.buffer)
                    self.buffer.clear()
                    return line
                if ch == "\x03":
                    raise KeyboardInterrupt
                if ch == "\x04":
                    if not self.buffer:
                        raise EOFError
                    continue
                if ch in ("\x7f", "\x08"):      # backspace
                    if self.buffer:
                        seq = self._erase_seq()
                        self.buffer.pop()
                        self._write(seq + self._draw_seq())
                elif ch == "\x15":              # Ctrl+U: clear the line
                    seq = self._erase_seq()
                    self.buffer.clear()
                    self._write(seq + self._draw_seq())
                elif ch and ch.isprintable():
                    self.buffer.append(ch)
                    self._drawn_width += disp_width(ch)
                    self._write(ch)


class Progress:
    """Percentage indicator for one transfer, rewritten in place when possible."""

    def __init__(self, ui: ConsoleUI, key: str, prefix: str, total: int):
        self.ui, self.key, self.prefix, self.total = ui, key, prefix, total
        self.last_pct = 0
        self.last_t = 0.0
        ui.update_line(key, f"{prefix} ... 0%", force_new=True)

    def update(self, done: int) -> None:
        pct = int(done * 100 / self.total) if self.total else 100
        if pct >= 100 or pct == self.last_pct:
            return
        now = time.monotonic()
        if now - self.last_t < 0.05:
            return
        milestone = pct // 25 > self.last_pct // 25
        self.last_pct, self.last_t = pct, now
        self.ui.update_line(self.key, f"{self.prefix} ... {pct}%", force_new=milestone)

    def finish(self, suffix: str) -> None:
        self.ui.update_line(self.key, f"{self.prefix} ... 100% {suffix}", force_new=True)


# --------------------------------------------------------------------------- #
# Online-user list (shared data, protected by a lock)
# --------------------------------------------------------------------------- #
@dataclass
class Peer:
    name: str
    ip: str
    port: int          # TCP port
    status: str
    last_seen: float


class PeerDirectory:
    def __init__(self, timeout: float):
        self.timeout = timeout
        self._peers: Dict[str, Peer] = {}
        self._lock = threading.Lock()

    def update(self, name: str, ip: str, port: int, status: str) -> Optional[str]:
        """Returns 'online' for a new peer, 'status' if the status changed, else None."""
        now = time.monotonic()
        with self._lock:
            peer = self._peers.get(name)
            if peer is None:
                self._peers[name] = Peer(name, ip, port, status, now)
                return "online"
            event = "status" if peer.status != status else None
            # same-machine peers are heard on 127.x and on the LAN IP: keep the LAN one
            if not (is_loopback(ip) and not is_loopback(peer.ip)):
                peer.ip = ip
            peer.port, peer.status, peer.last_seen = port, status, now
            return event

    def remove(self, name: str, port: int) -> Optional[Peer]:
        with self._lock:
            peer = self._peers.get(name)
            if peer is not None and peer.port == port:
                return self._peers.pop(name)
            return None

    def expire(self) -> List[Peer]:
        now = time.monotonic()
        with self._lock:
            dead = [p for p in self._peers.values() if now - p.last_seen > self.timeout]
            for p in dead:
                del self._peers[p.name]
            return dead

    def snapshot(self) -> List[Peer]:
        with self._lock:
            return sorted((Peer(**vars(p)) for p in self._peers.values()),
                          key=lambda p: p.name.lower())

    def get(self, name: str) -> Optional[Peer]:
        with self._lock:
            for p in self._peers.values():
                if p.name.lower() == name.lower():
                    return Peer(**vars(p))
            return None


# --------------------------------------------------------------------------- #
# The application
# --------------------------------------------------------------------------- #
class ChatApp:
    def __init__(self, name: str, tcp_port: Optional[int], udp_port: int,
                 extra_targets: List[str], download_dir: str):
        self.name = name
        self.status = "online"
        self.udp_port = udp_port
        self.download_dir = download_dir
        self.ui = ConsoleUI()
        self.peers = PeerDirectory(PEER_TIMEOUT)

        # --- shared chat state, protected by self.lock ------------------------
        self.lock = threading.RLock()
        self.conns: Dict[str, Connection] = {}              # peer name -> chat connection
        self.current: Optional[str] = None                  # current chat partner
        self.history: Dict[str, deque] = {}                 # peer -> (sender, text)
        self.unread: Dict[str, List[str]] = {}              # peer -> unread messages
        self._list_snapshot: List[str] = []                 # names shown by last /list

        self.stop = threading.Event()
        self.wake = threading.Event()                       # wakes the broadcaster early
        self._ids = itertools.count(1)
        self._closed = False
        self._bcast_warned = False
        self.targets = local_broadcast_targets(extra_targets)

        self.server = self._open_tcp_server(tcp_port)
        self.tcp_port = self.server.getsockname()[1]
        self.udp_rx = self._open_udp_listener()
        self.udp_tx = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.udp_tx.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
        self._bcast_thread: Optional[threading.Thread] = None

    # ------------------------------------------------------------------ sockets
    def _open_tcp_server(self, port: Optional[int]) -> socket.socket:
        candidates = ([port] if port is not None
                      else range(DEFAULT_TCP_PORT, DEFAULT_TCP_PORT + 100))
        last_error: Optional[OSError] = None
        for p in candidates:
            s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            if os.name != "nt":      # on Windows SO_REUSEADDR would allow port hijacking
                s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            try:
                s.bind(("", p))
                s.listen(16)
                s.settimeout(1.0)    # lets the acceptor thread notice shutdown
                return s
            except OSError as e:
                s.close()
                last_error = e
        raise SystemExit(f"Cannot listen on TCP port: {last_error}")

    def _open_udp_listener(self) -> socket.socket:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        # several instances on one machine must be able to share the discovery port
        s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        if hasattr(socket, "SO_REUSEPORT"):
            try:
                s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEPORT, 1)
            except OSError:
                pass
        try:
            s.bind(("", self.udp_port))
        except OSError as e:
            raise SystemExit(f"Cannot bind UDP port {self.udp_port}: {e}")
        s.settimeout(1.0)
        return s

    # ------------------------------------------------------------------ lifecycle
    def run(self) -> None:
        self.ui.open()
        try:
            self.ui.print(f"[*] Listening on TCP port {self.tcp_port}")
            self.ui.print(f"[*] Broadcasting presence on UDP port {self.udp_port}")
            self.ui.print(f"[*] You are '{self.name}'. Type /help for commands.")
            self._start_threads()
            while True:
                try:
                    line = self.ui.readline()
                except (EOFError, KeyboardInterrupt):
                    break
                if not self.handle_line(line):
                    break
        finally:
            self.shutdown()
            self.ui.close()

    def _start_threads(self) -> None:
        self._bcast_thread = threading.Thread(target=self._udp_broadcaster,
                                              name="udp-broadcast", daemon=True)
        self._bcast_thread.start()
        threading.Thread(target=self._udp_listener, name="udp-listen", daemon=True).start()
        threading.Thread(target=self._tcp_acceptor, name="tcp-accept", daemon=True).start()

    def shutdown(self) -> None:
        if self._closed:
            return
        self._closed = True
        self.stop.set()
        self.wake.set()
        if self._bcast_thread is not None:
            self._bcast_thread.join(1.0)
        for _ in range(2):                      # UDP may lose a packet: say goodbye twice
            self._broadcast(f"BYE|{self.name}|{self.tcp_port}", warn=False)
        with self.lock:
            conns = list(self.conns.values())
            self.conns.clear()
            self.current = None
        for c in conns:
            try:
                c.send(build_frame("BYE"))
            except OSError:
                pass
            c.close()
        for s in (self.server, self.udp_rx, self.udp_tx):
            try:
                s.close()
            except OSError:
                pass

    # ------------------------------------------------------------------ UDP side
    def _broadcast(self, text: str, warn: bool = True) -> None:
        data = text.encode("utf-8")
        ok, error = False, None
        for target in self.targets:
            try:
                self.udp_tx.sendto(data, (target, self.udp_port))
                ok = True
            except OSError as e:
                error = e
        if not ok and warn and not self._bcast_warned:
            self._bcast_warned = True
            self.ui.print(f"[!] UDP broadcast failed ({error}). Check network / firewall.")

    def _udp_broadcaster(self) -> None:
        """Thread: send HELLO|name|tcp_port|status every 3 seconds."""
        while not self.stop.is_set():
            self._broadcast(f"HELLO|{self.name}|{self.tcp_port}|{self.status}")
            self.wake.wait(HELLO_INTERVAL)      # woken early by /status
            self.wake.clear()

    def _udp_listener(self) -> None:
        """Thread: receive presence datagrams, keep the online list, expire peers."""
        last_check = 0.0
        while not self.stop.is_set():
            try:
                data, (ip, _port) = self.udp_rx.recvfrom(2048)
                self._handle_datagram(data, ip)
            except socket.timeout:
                pass
            except ConnectionResetError:        # Windows: ICMP "port unreachable"
                pass
            except OSError:
                if self.stop.is_set():
                    break
                time.sleep(0.2)
            now = time.monotonic()
            if now - last_check >= 1.0:
                last_check = now
                for peer in self.peers.expire():
                    self.ui.print(f"[*] {peer.name} went offline")

    def _handle_datagram(self, data: bytes, ip: str) -> None:
        try:
            parts = data.decode("utf-8").split("|")
        except UnicodeDecodeError:
            return
        if parts[0] == "HELLO" and len(parts) == 4:
            _, raw_name, raw_port, status = parts
            name = clean_name(raw_name)
            if not name or not raw_port.isdigit() or not 0 < int(raw_port) < 65536 \
                    or status not in STATUSES:
                return
            port = int(raw_port)
            if name == self.name and port == self.tcp_port:
                return                          # our own broadcast
            event = self.peers.update(name, ip, port, status)
            if event == "online":
                self.ui.print(f"[*] {name} is now online ({ip})")
            elif event == "status":
                self.ui.print(f"[*] {name} is now {status}")
        elif parts[0] == "BYE" and len(parts) == 3 and parts[2].isdigit():
            peer = self.peers.remove(clean_name(parts[1]), int(parts[2]))
            if peer is not None:
                self.ui.print(f"[*] {peer.name} went offline")

    # ------------------------------------------------------------------ TCP side
    def _tcp_acceptor(self) -> None:
        """Thread: accept connections, one receiver thread per connection."""
        while not self.stop.is_set():
            try:
                sock, addr = self.server.accept()
            except socket.timeout:
                continue
            except OSError:
                if self.stop.is_set():
                    break
                time.sleep(0.2)
                continue
            threading.Thread(target=self._serve_incoming, args=(sock, addr),
                             name="recv-incoming", daemon=True).start()

    def _tune(self, sock: socket.socket) -> None:
        sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_KEEPALIVE, 1)

    def _serve_incoming(self, sock: socket.socket, addr) -> None:
        reader = SocketReader(sock)
        try:
            sock.settimeout(CONNECT_TIMEOUT)    # a silent client must not hang us
            if reader.read_field() != "ID":
                raise ProtocolError("first frame must be ID")
            name = clean_name(reader.read_field())
            port_s = reader.read_field()
            kind = reader.read_field()
            if not name or not port_s.isdigit() or kind not in ("chat", "file") \
                    or name == self.name:
                raise ProtocolError("bad ID frame")
            sock.settimeout(None)
            self._tune(sock)
        except (ConnectionClosed, ProtocolError, OSError, ValueError):
            try:
                sock.close()
            except OSError:
                pass
            return
        conn = Connection(sock, name, addr[0], int(port_s), False, kind)
        if kind == "chat" and not self._register(conn):
            return
        threading.current_thread().name = f"recv-{name}"
        self._recv_loop(conn, reader)

    def _initiator(self, conn: Connection) -> str:
        return self.name if conn.initiated_by_me else conn.peer

    def _register(self, conn: Connection) -> bool:
        """Make *conn* the chat connection of its peer.

        Two peers may connect to each other at the same moment. Both sides then
        apply the same rule - keep the connection opened by the peer whose name
        sorts first - so they agree on which one survives.
        Returns False if *conn* itself was rejected.
        """
        to_close: Optional[Connection] = None
        with self.lock:
            old = self.conns.get(conn.peer)
            if old is not None and not old.closed:
                a, b = self._initiator(old), self._initiator(conn)
                if a == b or b < a:
                    old.superseded = True
                    self.conns[conn.peer] = conn
                    to_close = old
                else:
                    conn.superseded = True
                    to_close = conn
            else:
                self.conns[conn.peer] = conn
        if to_close is not None:
            to_close.close()
        return to_close is not conn

    def _recv_loop(self, conn: Connection, reader: SocketReader) -> None:
        """Receiver thread for one connection: MSG / FILE / BYE frames."""
        reason, graceful = "connection closed", False
        try:
            while not self.stop.is_set():
                ftype = reader.read_field()
                if ftype == "MSG":
                    length_s = reader.read_field()
                    if not length_s.isdigit():
                        raise ProtocolError("bad MSG length")
                    length = int(length_s)
                    if length > MAX_MSG:
                        raise ProtocolError("message too large")
                    text = reader.read_exact(length).decode("utf-8", "replace")
                    self._on_message(conn, text)
                elif ftype == "FILE":
                    raw_name = reader.read_field()
                    size_s = reader.read_field()
                    if not size_s.isdigit():
                        raise ProtocolError("bad FILE size")
                    self._receive_file(conn, reader, unquote(raw_name), int(size_s))
                elif ftype == "BYE":
                    reason, graceful = "left the chat", True
                    break
                else:
                    raise ProtocolError(f"unknown frame type {ftype[:20]!r}")
        except ConnectionClosed:
            reason = "connection closed by peer"
        except ProtocolError as e:
            reason = f"protocol error: {e}"
        except (OSError, ValueError) as e:      # reset, timeout, bad utf-8 header ...
            reason = str(e) or type(e).__name__
        if conn.kind == "chat":
            self._connection_lost(conn, reason, graceful)
        else:
            conn.close()

    def _connection_lost(self, conn: Connection, reason: str, graceful: bool = False) -> None:
        """A chat connection ended: remove it, tell the user, go back to the prompt."""
        with self.lock:
            if conn.superseded:
                removed, was_current = False, False
            else:
                removed = self.conns.get(conn.peer) is conn
                was_current = removed and self.current == conn.peer
                if removed:
                    del self.conns[conn.peer]
                if was_current:
                    self.current = None
        conn.close()
        if not removed:
            return                              # /leave, duplicate, or already reported
        if graceful:
            msg = f"[*] {conn.peer} closed the chat."
        else:
            msg = f"[*] {conn.peer} disconnected ({reason})."
            if was_current:
                msg += " Chat closed."
        self.ui.print(msg)

    def _on_message(self, conn: Connection, text: str) -> None:
        text = sanitize_text(text)
        peer = conn.peer
        with self.lock:
            self.history.setdefault(peer, deque(maxlen=500)).append((peer, text))
            is_current = self.current == peer
            if not is_current:
                pending = self.unread.setdefault(peer, [])
                pending.append(text)
                count = len(pending)
            no_partner = self.current is None
        if is_current:
            self.ui.print(f"[{peer}] {text}")
        else:
            note = f"[*] New message from {peer} ({count} unread)"
            if no_partner:
                note += f" - type /chat {peer}"
            self.ui.update_line(f"unread:{peer}", note, force_new=True)

    # ------------------------------------------------------------------ files
    def _receive_file(self, conn: Connection, reader: SocketReader, raw_name: str,
                      size: int) -> None:
        """Called by the receiver thread when a FILE frame header has arrived."""
        name = safe_filename(raw_name)
        key = f"recv:{next(self._ids)}"
        try:
            os.makedirs(self.download_dir, exist_ok=True)
            fh, dest = open_unique(self.download_dir, name)
        except OSError as e:
            self.ui.print(f"[!] Cannot save {name} from {conn.peer}: {e}")
            raise
        part = dest + ".part"
        prefix = f"[*] Receiving {shorten(name)} ({human_size(size)}) from {conn.peer}"
        progress = Progress(self.ui, key, prefix, size)
        received, ok = 0, False
        try:
            conn.sock.settimeout(FILE_STALL_TIMEOUT)
            with fh:
                while received < size:
                    chunk = reader.read_chunk(min(CHUNK, size - received))
                    fh.write(chunk)
                    received += len(chunk)
                    progress.update(received)
            os.replace(part, dest)
            ok = True
        except (ConnectionClosed, ProtocolError, OSError) as e:
            self.ui.print(f"[!] Receiving {name} from {conn.peer} failed after "
                          f"{human_size(received)}: {str(e) or type(e).__name__}. "
                          f"Partial file deleted.")
            raise
        finally:
            try:
                conn.sock.settimeout(None)
            except OSError:
                pass
            if not ok:
                try:
                    os.remove(part)             # never leave a partial file behind
                except OSError:
                    pass
        progress.finish(f"Done. Saved to {dest}")
        if conn.kind == "file":
            conn.send(b"OK|")                   # confirmation for the sender

    def _send_file(self, peer: str, addr: Tuple[str, int], path: str, size: int) -> None:
        """Thread: push a file over its OWN TCP connection so chat is never blocked."""
        name = os.path.basename(path)
        prefix = f"[*] Sending {shorten(name)} ({human_size(size)})"
        progress = Progress(self.ui, f"send:{next(self._ids)}", prefix, size)
        sock: Optional[socket.socket] = None
        try:
            sock = socket.create_connection(addr, timeout=CONNECT_TIMEOUT)
            sock.settimeout(FILE_STALL_TIMEOUT)
            self._tune(sock)
            sock.sendall(build_frame("ID", self.name, self.tcp_port, "file"))
            sock.sendall(build_frame("FILE", quote(name, safe=""), size))
            sent = 0
            with open(path, "rb") as fh:
                while sent < size:
                    chunk = fh.read(min(CHUNK, size - sent))
                    if not chunk:
                        raise ProtocolError("file changed while sending")
                    sock.sendall(chunk)
                    sent += len(chunk)
                    progress.update(sent)
            ack = b""
            while len(ack) < 3:                 # wait until the receiver saved it
                part = sock.recv(3 - len(ack))
                if not part:
                    raise ConnectionClosed("receiver closed the connection")
                ack += part
            if ack != b"OK|":
                raise ProtocolError("bad confirmation from receiver")
            sock.sendall(build_frame("BYE"))
            progress.finish("Done.")
        except (OSError, ConnectionClosed, ProtocolError) as e:
            self.ui.print(f"[!] Sending {name} to {peer} failed: "
                          f"{str(e) or type(e).__name__}")
        finally:
            if sock is not None:
                try:
                    sock.close()
                except OSError:
                    pass

    # ------------------------------------------------------------------ commands
    def handle_line(self, line: str) -> bool:
        """Returns False when the program should exit."""
        line = line.strip()
        if not line:
            return True
        if not line.startswith("/"):
            self.send_chat(line)
            return True
        self.ui.print(f"> {line}")
        cmd, _, arg = line[1:].partition(" ")
        cmd, arg = cmd.lower(), arg.strip()
        if cmd in ("quit", "exit"):
            return False
        handlers: Dict[str, Callable[[str], None]] = {
            "list": self.cmd_list, "chat": self.cmd_chat, "send": self.cmd_send,
            "leave": self.cmd_leave, "status": self.cmd_status, "help": self.cmd_help,
        }
        handler = handlers.get(cmd)
        if handler is None:
            self.ui.print(f"[!] Unknown command '/{cmd}'.\n{HELP_TEXT}")
        else:
            handler(arg)
        return True

    def cmd_help(self, _arg: str) -> None:
        self.ui.print(HELP_TEXT)

    def cmd_list(self, _arg: str) -> None:
        peers = self.peers.snapshot()
        with self.lock:
            self._list_snapshot = [p.name for p in peers]
            current = self.current
            unread = {p.name: len(self.unread.get(p.name, [])) for p in peers}
        if not peers:
            self.ui.print("[*] No other users online.")
            return
        lines = []
        for i, p in enumerate(peers, 1):
            line = f"{i:>2}. {p.name} ({p.ip}) {p.status}"
            if p.name == current:
                line += "  <- chatting"
            if unread[p.name]:
                line += f"  [{unread[p.name]} unread]"
            lines.append(line)
        self.ui.print("\n".join(lines))

    def cmd_status(self, arg: str) -> None:
        status = arg.lower()
        if status not in STATUSES:
            self.ui.print("[!] Usage: /status <online|away>")
            return
        self.status = status
        self.wake.set()                         # broadcast the change immediately
        self.ui.print(f"[*] Status set to {status}")

    def _resolve_peer(self, arg: str) -> Optional[Tuple[str, str, int]]:
        """name|number -> (name, ip, tcp_port); prints an error and returns None."""
        if arg.isdigit():
            with self.lock:
                names = list(self._list_snapshot)
            if not names:
                names = [p.name for p in self.peers.snapshot()]
            idx = int(arg)
            if not 1 <= idx <= len(names):
                self.ui.print(f"[!] No user number {idx}. Use /list.")
                return None
            arg = names[idx - 1]
        peer = self.peers.get(arg)
        if peer is not None:
            return peer.name, peer.ip, peer.port
        with self.lock:                          # offline for UDP but still connected
            for c in self.conns.values():
                if c.peer.lower() == arg.lower() and not c.closed:
                    return c.peer, c.remote_ip, c.remote_port
        self.ui.print(f"[!] User '{arg}' is not online. Use /list.")
        return None

    def cmd_chat(self, arg: str) -> None:
        if not arg:
            self.ui.print("[!] Usage: /chat <name|number>")
            return
        target = self._resolve_peer(arg)
        if target is None:
            return
        name, ip, port = target
        if name == self.name:
            self.ui.print("[!] You cannot chat with yourself.")
            return
        with self.lock:
            conn = self.conns.get(name)
            if conn is not None and conn.closed:
                conn = None
        is_new = conn is None
        if is_new:
            conn = self._connect(name, ip, port)
            if conn is None:
                return
        with self.lock:
            self.current = name
            pending = self.unread.pop(name, [])
        head = f"[*] Connected to {name} ({ip}:{port})" if is_new else f"[*] Switched to {name}"
        if pending:
            head += f" - {len(pending)} unread:"
        lines = [head] + [f"[{name}] {t}" for t in pending]
        self.ui.print("\n".join(lines))

    def _connect(self, name: str, ip: str, port: int) -> Optional[Connection]:
        sock: Optional[socket.socket] = None
        try:
            sock = socket.create_connection((ip, port), timeout=CONNECT_TIMEOUT)
            sock.sendall(build_frame("ID", self.name, self.tcp_port, "chat"))
            sock.settimeout(None)
            self._tune(sock)
        except OSError as e:
            if sock is not None:
                sock.close()
            self.ui.print(f"[!] Cannot connect to {name} ({ip}:{port}): "
                          f"{str(e) or type(e).__name__}. The user may have gone offline.")
            return None
        conn = Connection(sock, name, ip, port, True)
        self._register(conn)
        threading.Thread(target=self._recv_loop, args=(conn, SocketReader(sock)),
                         name=f"recv-{name}", daemon=True).start()
        with self.lock:
            winner = self.conns.get(name)       # may be the other side's connection
        if winner is None or winner.closed:
            self.ui.print(f"[!] Cannot connect to {name}.")
            return None
        return winner

    def send_chat(self, text: str) -> None:
        payload = text.encode("utf-8")
        if len(payload) > MAX_MSG:
            self.ui.print("[!] Message too long.")
            return
        with self.lock:
            conn = self.conns.get(self.current) if self.current else None
        if conn is None or conn.closed:
            self.ui.print("[!] No active chat. Use /chat <name|number> first (/list shows users).")
            return
        try:
            conn.send(build_frame("MSG", len(payload), payload=payload))
        except OSError as e:
            self._connection_lost(conn, str(e) or type(e).__name__)
            return
        with self.lock:
            self.history.setdefault(conn.peer, deque(maxlen=500)).append((self.name, text))
        self.ui.print(f"[{self.name}] {text}")

    def cmd_leave(self, _arg: str) -> None:
        with self.lock:
            name = self.current
            conn = self.conns.pop(name, None) if name else None
            self.current = None
        if name is None:
            self.ui.print("[!] No active chat.")
            return
        if conn is not None:
            try:
                conn.send(build_frame("BYE"))
            except OSError:
                pass
            conn.close()
        self.ui.print(f"[*] Left the chat with {name}.")

    def cmd_send(self, arg: str) -> None:
        path = arg.strip().strip("\"'")
        if not path:
            self.ui.print("[!] Usage: /send <file>")
            return
        with self.lock:
            conn = self.conns.get(self.current) if self.current else None
        if conn is None or conn.closed:
            self.ui.print("[!] No active chat. Use /chat <name|number> first.")
            return
        path = os.path.expanduser(path)
        if not os.path.isfile(path):
            self.ui.print(f"[!] File not found: {path}")
            return
        try:
            size = os.path.getsize(path)
            with open(path, "rb"):
                pass
        except OSError as e:
            self.ui.print(f"[!] Cannot read {path}: {e}")
            return
        threading.Thread(target=self._send_file, name="send-file", daemon=True,
                         args=(conn.peer, (conn.remote_ip, conn.remote_port), path, size)).start()


# --------------------------------------------------------------------------- #
def main() -> None:
    ap = argparse.ArgumentParser(description="LAN chat & file sharing (TCP + UDP sockets)")
    ap.add_argument("--name", help="your display name (default: host name)")
    ap.add_argument("--port", type=int, default=None,
                    help="TCP listening port (default: first free port from 5000)")
    ap.add_argument("--udp-port", type=int, default=UDP_PORT,
                    help=f"UDP discovery port (default {UDP_PORT})")
    ap.add_argument("--broadcast", action="append", default=[], metavar="ADDR",
                    help="extra broadcast address, e.g. 192.168.1.255 (repeatable)")
    ap.add_argument("--downloads", default="downloads",
                    help="folder for received files (default: downloads)")
    args = ap.parse_args()

    name = clean_name(args.name or socket.gethostname()) or "user"
    ChatApp(name, args.port, args.udp_port, args.broadcast, args.downloads).run()


if __name__ == "__main__":
    main()
