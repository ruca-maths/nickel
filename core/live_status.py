"""親機の進捗ページを配信する。GitHub の確保・提出は読み取り専用で監視する。"""
from __future__ import annotations

import argparse
import json
import sqlite3
import subprocess
import threading
import time
from contextlib import closing
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlsplit

from core.config import REPO_ROOT, load_config, resolve
from core.gitops import Git, GitError
from core.status_gen import configured_workers, remote_activity

LIVE_REFS = "refs/nickel-live/"


class LiveStatus:
    def __init__(self, cfg: dict, interval: float):
        self.cfg = cfg
        self.interval = interval
        self.root = resolve(cfg, cfg["project"].get("lean_root", ".")).resolve()
        self.db = resolve(cfg, cfg["project"]["db_path"]).resolve()
        g = cfg.get("git") or {}
        self.git = Git(self.root, g.get("remote", "origin"), g.get("base_branch", "main"))
        self.github = g.get("mode") == "github"
        self.ttl = float(g.get("claim_ttl_sec", 7200))
        self.remote = (None, None, "接続確認中" if self.github else "ローカルモード")

    def follow_remote(self, stop: threading.Event) -> None:
        while not stop.is_set():
            self.refresh_remote()
            stop.wait(self.interval)

    def refresh_remote(self) -> None:
        activity, published, _ = self.remote
        try:
            self.git.run(
                "fetch", "--no-write-fetch-head", "--prune", "--no-tags", "--refmap=", self.git.remote,
                f"+refs/heads/claim/*:{LIVE_REFS}claim/*", f"+refs/heads/proof/*:{LIVE_REFS}proof/*",
                f"+refs/heads/{self.git.base}:{LIVE_REFS}base",
                env={"GIT_TERMINAL_PROMPT": "0"}, timeout=15,
            )
            if not self.db.is_file():
                published = self.git.run("show", f"{LIVE_REFS}base:status/site.json", check=False) or published
            self.remote = (remote_activity(self.git, self.ttl, LIVE_REFS), published, "接続中")
        except (GitError, OSError, subprocess.TimeoutExpired):
            self.remote = (activity, published, "GitHub に接続できません。再接続中")

    def snapshot(self) -> dict:
        activity, published, connection = self.remote
        parent_db = self.db.is_file()
        source = published if published and not parent_db else (self.root / "status" / "site.json").read_text(encoding="utf-8")
        data = json.loads(source)
        if parent_db:
            with closing(sqlite3.connect(self.db.as_uri() + "?mode=ro", uri=True, timeout=1)) as db:
                db.row_factory = sqlite3.Row
                data["running"] = [dict(row) for row in db.execute(
                    "SELECT agent, task, node, expires_at FROM leases WHERE expires_at > ?", (time.time(),)
                )]
        data["workers"] = configured_workers(self.cfg)
        data["remote_activity"] = activity or data.get("remote_activity")
        data["live"] = {"interval": self.interval, "connection": connection, "parent_db": parent_db, "published": bool(published)}
        return data


def serve(status: LiveStatus, host: str, port: int) -> None:
    class Handler(BaseHTTPRequestHandler):
        def do_GET(self) -> None:
            path = urlsplit(self.path).path
            if path in ("/", "/index.html"):
                content = (REPO_ROOT / "index.html").read_bytes().replace(b"<body>", b"<body data-live>", 1)
                kind = "text/html; charset=utf-8"
            elif path == "/status/site.json":
                try:
                    content = json.dumps(status.snapshot(), ensure_ascii=False).encode()
                except (OSError, ValueError, sqlite3.Error):
                    self.send_error(503, "Status unavailable")
                    return
                kind = "application/json; charset=utf-8"
            else:
                self.send_error(404)
                return
            self.send_response(200)
            self.send_header("Content-Type", kind)
            self.send_header("Cache-Control", "no-store")
            self.send_header("Content-Length", str(len(content)))
            self.end_headers()
            self.wfile.write(content)

        def log_request(self, code="-", size="-") -> None:
            if str(code) != "200":
                super().log_request(code, size)

    stop = threading.Event()
    with ThreadingHTTPServer((host, port), Handler) as server:
        if status.github:
            threading.Thread(target=status.follow_remote, args=(stop,), daemon=True).start()
        print(f"進捗ページ http://{host}:{server.server_port}/", flush=True)
        try:
            server.serve_forever()
        finally:
            stop.set()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", type=int, default=8765)
    parser.add_argument("--interval", type=int, default=5, help="更新間隔（秒）")
    args = parser.parse_args()
    if args.interval < 1:
        parser.error("--interval は 1 秒以上にしてください")
    try:
        serve(LiveStatus(load_config(), args.interval), args.host, args.port)
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
