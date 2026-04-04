#!/usr/bin/env python3
"""
audio_manager.py — Recording workflow tool

Usage:
    python audio_manager.py [AUDIO_DIR] [WATCH_DIR]

    AUDIO_DIR  folder containing your .mp3 + .webp source files
               (defaults to current working directory)
    WATCH_DIR  folder where Audacity exports its output
               (defaults to AUDIO_DIR/output)

Workflow:
    1. Converts all .webp files in AUDIO_DIR to .png via ImageMagick
    2. Shows a grid UI: each mp3 with its matching .png as cover thumbnail
    3. Click a tile → opens that mp3 in Audacity; tile is marked "active"
    4. Watches WATCH_DIR for new audio files written by Audacity
    5. When the exported file stops changing for 3 s, embeds the active
       item's .png as ID3 cover art, then opens the file in Kid3
    6. Removes the tile from the UI and moves the source mp3 + png + webp
       to the system trash
"""

import os
import sys
import time
import subprocess
import threading
import tkinter as tk
from tkinter import ttk, messagebox
from pathlib import Path
from PIL import Image, ImageTk
from mutagen.id3 import ID3, APIC, error as ID3Error
from watchdog.observers import Observer
from watchdog.events import FileSystemEventHandler
import send2trash

# ── Configuration ──────────────────────────────────────────────────────────────

AUDIO_DIR    = Path(sys.argv[1]).expanduser() if len(sys.argv) > 1 else Path.cwd()
WATCH_DIR    = Path(sys.argv[2]).expanduser() if len(sys.argv) > 2 else AUDIO_DIR / "output"
STABLE_SECS  = 3.0          # seconds of silence before a file is considered done
THUMB_W      = 200          # thumbnail width  (px)
THUMB_H      = 200          # thumbnail height (px)
TILE_PAD     = 12           # padding around each tile
WATCH_EXTS   = {".mp3", ".wav", ".flac", ".ogg", ".aiff", ".m4a"}

# ── Colours ────────────────────────────────────────────────────────────────────
BG          = "#0d0d0d"
BG2         = "#161616"
BG3         = "#1f1f1f"
ACCENT      = "#c8a96e"       # warm gold
ACCENT2     = "#e8c98e"
FG          = "#e8e8e8"
FG_DIM      = "#666666"
HIGHLIGHT   = "#2a2010"       # selected tile background
BORDER_SEL  = "#c8a96e"


# ── File stabiliser ────────────────────────────────────────────────────────────

class FileStabilizer:
    """
    Calls on_stable(path) once a file stops receiving write events for
    STABLE_SECS seconds.  Thread-safe; timer resets on every new event.
    """

    def __init__(self, on_stable):
        self._on_stable = on_stable
        self._timers: dict[Path, threading.Timer] = {}
        self._lock = threading.Lock()

    def ping(self, path: Path):
        with self._lock:
            existing = self._timers.pop(path, None)
            if existing:
                existing.cancel()
            t = threading.Timer(STABLE_SECS, self._fire, args=[path])
            self._timers[path] = t
            t.start()

    def _fire(self, path: Path):
        with self._lock:
            self._timers.pop(path, None)
        if path.exists() and path.stat().st_size > 0:
            self._on_stable(path)

    def cancel_all(self):
        with self._lock:
            for t in self._timers.values():
                t.cancel()
            self._timers.clear()


# ── Watchdog handler ───────────────────────────────────────────────────────────

class ExportHandler(FileSystemEventHandler):
    def __init__(self, stabilizer: FileStabilizer):
        self._stab = stabilizer

    def _handle(self, src_path: str):
        p = Path(src_path)
        if p.suffix.lower() in WATCH_EXTS:
            self._stab.ping(p)

    def on_created(self, event):
        if not event.is_directory:
            self._handle(event.src_path)

    def on_modified(self, event):
        if not event.is_directory:
            self._handle(event.src_path)


# ── Main application ───────────────────────────────────────────────────────────

class AudioManager(tk.Tk):

    def __init__(self):
        super().__init__()
        self.title("audio manager")
        self.configure(bg=BG)
        self.geometry("960x720")
        self.minsize(400, 300)

        self._active: dict | None = None          # currently selected item
        self._items: dict[Path, dict] = {}         # mp3 → item dict
        self._photo_refs: list = []                # keep Tk PhotoImage refs alive
        self._observer: Observer | None = None
        self._stabilizer: FileStabilizer | None = None

        self._apply_style()
        self._build_header()
        self._build_canvas()
        self._build_statusbar()

        self._convert_webps()
        self._load_items()
        self._start_watcher()

        self.bind("<Configure>", lambda e: self.after_idle(self._reflow))
        self.protocol("WM_DELETE_WINDOW", self._on_close)

    # ── Style ──────────────────────────────────────────────────────────────────

    def _apply_style(self):
        style = ttk.Style(self)
        style.theme_use("clam")
        style.configure(
            "Vertical.TScrollbar",
            background=BG3, troughcolor=BG, bordercolor=BG,
            arrowcolor=FG_DIM, relief="flat",
        )

    # ── UI construction ────────────────────────────────────────────────────────

    def _build_header(self):
        hdr = tk.Frame(self, bg=BG2, pady=0)
        hdr.pack(fill="x", side="top")

        # thin accent line at very top
        tk.Frame(hdr, bg=ACCENT, height=2).pack(fill="x")

        inner = tk.Frame(hdr, bg=BG2, pady=14, padx=20)
        inner.pack(fill="x")

        tk.Label(
            inner, text="AUDIO MANAGER",
            bg=BG2, fg=ACCENT,
            font=("Courier", 13, "bold"),
        ).pack(side="left")

        self._active_var = tk.StringVar(value="— no file selected —")
        tk.Label(
            inner, textvariable=self._active_var,
            bg=BG2, fg=FG_DIM,
            font=("Courier", 10),
        ).pack(side="right")

    def _build_canvas(self):
        container = tk.Frame(self, bg=BG)
        container.pack(fill="both", expand=True)

        self._canvas = tk.Canvas(container, bg=BG, highlightthickness=0, bd=0)
        vsb = ttk.Scrollbar(container, orient="vertical",
                             command=self._canvas.yview,
                             style="Vertical.TScrollbar")
        self._canvas.configure(yscrollcommand=vsb.set)

        vsb.pack(side="right", fill="y")
        self._canvas.pack(side="left", fill="both", expand=True)

        self._grid_frame = tk.Frame(self._canvas, bg=BG)
        self._canvas_win = self._canvas.create_window(
            (0, 0), window=self._grid_frame, anchor="nw"
        )

        self._grid_frame.bind("<Configure>", self._on_frame_configure)
        self._canvas.bind("<Configure>", self._on_canvas_configure)
        self._canvas.bind_all("<MouseWheel>",  self._on_mousewheel)
        self._canvas.bind_all("<Button-4>",    self._on_mousewheel)
        self._canvas.bind_all("<Button-5>",    self._on_mousewheel)

    def _build_statusbar(self):
        bar = tk.Frame(self, bg=BG2, pady=0)
        bar.pack(fill="x", side="bottom")
        tk.Frame(bar, bg="#2a2a2a", height=1).pack(fill="x")
        inner = tk.Frame(bar, bg=BG2, pady=8, padx=20)
        inner.pack(fill="x")
        self._status_var = tk.StringVar(value="ready")
        tk.Label(
            inner, textvariable=self._status_var,
            bg=BG2, fg=FG_DIM, font=("Courier", 9),
        ).pack(side="left")
        self._watch_var = tk.StringVar(value=f"watching  {WATCH_DIR}")
        tk.Label(
            inner, textvariable=self._watch_var,
            bg=BG2, fg=FG_DIM, font=("Courier", 9),
        ).pack(side="right")

    # ── Canvas / scroll plumbing ───────────────────────────────────────────────

    def _on_frame_configure(self, _event=None):
        self._canvas.configure(scrollregion=self._canvas.bbox("all"))

    def _on_canvas_configure(self, _event=None):
        self._canvas.itemconfig(self._canvas_win, width=self._canvas.winfo_width())
        self.after_idle(self._reflow)

    def _on_mousewheel(self, event):
        if event.num == 4:
            self._canvas.yview_scroll(-1, "units")
        elif event.num == 5:
            self._canvas.yview_scroll(1, "units")
        else:
            self._canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")

    # ── WebP conversion ────────────────────────────────────────────────────────

    def _convert_webps(self):
        webps = [p for p in AUDIO_DIR.glob("*.webp")
                 if not p.with_suffix(".png").exists()]
        if not webps:
            return
        self._set_status(f"converting {len(webps)} webp file(s)…")
        failed = []
        for webp in webps:
            png = webp.with_suffix(".png")
            r = subprocess.run(
                ["magick", str(webp), str(png)],
                capture_output=True, text=True,
            )
            if r.returncode != 0:
                print(f"[magick] failed on {webp.name}: {r.stderr.strip()}")
                failed.append(webp.name)
            else:
                print(f"[magick] {webp.name} → {png.name}")
        if failed:
            self._set_status(f"conversion done (failed: {', '.join(failed)})")
        else:
            self._set_status("conversion complete")

    # ── Item grid ──────────────────────────────────────────────────────────────

    def _load_items(self):
        mp3s = sorted(AUDIO_DIR.glob("*.mp3"))
        found = 0
        for mp3 in mp3s:
            png  = mp3.with_suffix(".png")
            webp = mp3.with_suffix(".webp")
            if png.exists():
                self._add_item(mp3, png, webp if webp.exists() else None)
                found += 1
        self._set_status(f"{found} file(s) loaded — click a tile to open in Audacity")
        self._reflow()

    def _add_item(self, mp3: Path, png: Path, webp: Path | None):
        if mp3 in self._items:
            return

        # ── Outer tile frame ──
        tile = tk.Frame(
            self._grid_frame, bg=BG3,
            padx=0, pady=0, cursor="hand2",
        )

        # ── Image ──
        photo = self._load_thumb(png)

        img_frame = tk.Frame(tile, bg=BG3)
        img_frame.pack(fill="x")

        if photo:
            img_lbl = tk.Label(img_frame, image=photo, bg=BG3, cursor="hand2",
                                bd=0, highlightthickness=0)
            img_lbl.pack()
        else:
            placeholder = tk.Label(
                img_frame, text="?", bg="#222", fg=FG_DIM,
                width=THUMB_W // 10, height=THUMB_H // 20,
                font=("Courier", 24),
            )
            placeholder.pack(ipady=THUMB_H // 4)

        # ── Title label ──
        name = mp3.stem
        display_name = name if len(name) <= 28 else name[:25] + "…"
        lbl = tk.Label(
            tile, text=display_name,
            bg=BG3, fg=FG,
            font=("Courier", 8),
            wraplength=THUMB_W + 8,
            justify="center",
            pady=8, padx=6,
        )
        lbl.pack(fill="x")

        # ── Bind clicks on every child ──
        for widget in (tile, img_frame, lbl,
                       *(img_frame.winfo_children())):
            widget.bind("<Button-1>", lambda e, m=mp3: self._on_click(m))
            widget.bind("<Enter>",    lambda e, t=tile: self._hover(t, True))
            widget.bind("<Leave>",    lambda e, t=tile: self._hover(t, False))

        item = {
            "mp3": mp3, "png": png, "webp": webp,
            "tile": tile, "photo": photo, "lbl": lbl,
            "img_frame": img_frame,
        }
        self._items[mp3] = item

    def _load_thumb(self, png: Path) -> ImageTk.PhotoImage | None:
        try:
            img = Image.open(png).convert("RGB")
            img.thumbnail((THUMB_W, THUMB_H), Image.LANCZOS)
            # square-crop / pad to exact size
            canvas = Image.new("RGB", (THUMB_W, THUMB_H), (20, 20, 20))
            ox = (THUMB_W - img.width) // 2
            oy = (THUMB_H - img.height) // 2
            canvas.paste(img, (ox, oy))
            photo = ImageTk.PhotoImage(canvas)
            self._photo_refs.append(photo)
            return photo
        except Exception as e:
            print(f"[thumb] {png.name}: {e}")
            return None

    def _reflow(self):
        available = self._canvas.winfo_width() or 960
        col_w = THUMB_W + TILE_PAD * 2 + 4
        cols  = max(1, available // col_w)
        for idx, item in enumerate(self._items.values()):
            item["tile"].grid(
                row=idx // cols, column=idx % cols,
                padx=TILE_PAD, pady=TILE_PAD, sticky="n",
            )
        self._on_frame_configure()

    def _hover(self, tile: tk.Frame, entering: bool):
        # Don't override active item highlight
        mp3 = self._tile_to_mp3(tile)
        if mp3 and self._active and self._active["mp3"] == mp3:
            return
        colour = "#222222" if entering else BG3
        self._tint_tile(tile, colour)

    def _tint_tile(self, tile: tk.Frame, colour: str):
        try:
            tile.configure(bg=colour)
            for w in tile.winfo_children():
                w.configure(bg=colour)
                for ww in w.winfo_children():
                    try:
                        ww.configure(bg=colour)
                    except Exception:
                        pass
        except Exception:
            pass

    def _tile_to_mp3(self, tile: tk.Frame) -> Path | None:
        for mp3, item in self._items.items():
            if item["tile"] is tile:
                return mp3
        return None

    # ── Click handler ──────────────────────────────────────────────────────────

    def _on_click(self, mp3: Path):
        item = self._items.get(mp3)
        if not item:
            return

        # Deselect previous
        if self._active and self._active["mp3"] in self._items:
            self._tint_tile(self._active["tile"], BG3)

        self._active = item
        self._tint_tile(item["tile"], HIGHLIGHT)

        short = mp3.name if len(mp3.name) <= 52 else mp3.name[:49] + "…"
        self._active_var.set(f"active  ›  {short}")
        self._set_status(f"opening Audacity with {mp3.name} …")

        subprocess.Popen(["audacity", str(mp3)])
        self._set_status(f"Audacity launched  —  waiting for export in {WATCH_DIR}")

    # ── Export processing ──────────────────────────────────────────────────────

    def _on_file_stable(self, path: Path):
        """Called from watcher thread when exported file is stable."""
        print(f"[stable] {path.name}")
        if not self._active:
            print("[stable] no active item — skipping")
            return

        png = self._active["png"]
        self.after(0, lambda: self._set_status(f"embedding cover art into {path.name} …"))

        self._embed_cover(path, png)
        subprocess.Popen(["kid3", str(path)])

        self.after(0, self._finish_active_item)

    def _embed_cover(self, audio_path: Path, png_path: Path):
        print(f"[cover] {png_path.name} → {audio_path.name}")
        try:
            try:
                tags = ID3(str(audio_path))
            except ID3Error:
                tags = ID3()

            with open(png_path, "rb") as fh:
                img_data = fh.read()

            tags.delall("APIC")
            tags.add(APIC(
                encoding=3,        # UTF-8
                mime="image/png",
                type=3,            # Front cover
                desc="Cover",
                data=img_data,
            ))
            tags.save(str(audio_path))
            print("[cover] ✓ saved")
        except Exception as exc:
            print(f"[cover] ✗ {exc}")
            self.after(0, lambda: messagebox.showwarning(
                "Cover art failed",
                f"Could not embed cover into {audio_path.name}:\n{exc}",
            ))

    def _finish_active_item(self):
        """Remove tile from UI and trash source files (runs on main thread)."""
        if not self._active:
            return
        item = self._active
        self._active = None
        self._active_var.set("— no file selected —")

        # Remove tile
        item["tile"].destroy()
        self._items.pop(item["mp3"], None)
        self._reflow()

        # Trash originals
        for key in ("mp3", "png", "webp"):
            p = item.get(key)
            if p and p.exists():
                try:
                    send2trash.send2trash(str(p))
                    print(f"[trash] {p.name}")
                except Exception as exc:
                    print(f"[trash] failed on {p.name}: {exc}")

        remaining = len(self._items)
        self._set_status(
            f"done — {remaining} file(s) remaining"
            if remaining else "all files processed ✓"
        )

    # ── Watcher ────────────────────────────────────────────────────────────────

    def _start_watcher(self):
        WATCH_DIR.mkdir(parents=True, exist_ok=True)
        self._stabilizer = FileStabilizer(self._on_file_stable)
        handler = ExportHandler(self._stabilizer)
        self._observer = Observer()
        self._observer.schedule(handler, str(WATCH_DIR), recursive=False)
        self._observer.start()
        print(f"[watch] {WATCH_DIR}")

    # ── Helpers ────────────────────────────────────────────────────────────────

    def _set_status(self, msg: str):
        self._status_var.set(msg)
        self.update_idletasks()

    def _on_close(self):
        if self._stabilizer:
            self._stabilizer.cancel_all()
        if self._observer:
            self._observer.stop()
            self._observer.join(timeout=2)
        self.destroy()


# ── Entry point ────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    if not AUDIO_DIR.is_dir():
        print(f"error: AUDIO_DIR does not exist: {AUDIO_DIR}", file=sys.stderr)
        sys.exit(1)

    print(f"[init] audio dir : {AUDIO_DIR}")
    print(f"[init] watch dir : {WATCH_DIR}")

    app = AudioManager()
    app.mainloop()
