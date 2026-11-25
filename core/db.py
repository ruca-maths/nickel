"""SQLite (WAL) による AND-OR 証明グラフ・リース・予算・ビルド枠の管理。

ノード (L_xxxx) … 補題。命題は Specs/L_xxxx.lean の `Specs.L_xxxx.stmt`。
帰着 (R_xxxx) … 「子ノードすべて ⇒ 親ノード」という Lean 定理。親ノードの OR 分岐、
               子ノードの AND 結合を表す。
ノードの状態: proposed（帰着の受理待ち）/ open / checked / refuted / void
"""
from __future__ import annotations

import contextlib
import datetime as _dt
import json
import secrets
import sqlite3
import time
from pathlib import Path
from typing import Iterator

SCHEMA = """
CREATE TABLE IF NOT EXISTS meta(key TEXT PRIMARY KEY, value TEXT);
CREATE TABLE IF NOT EXISTS counters(name TEXT PRIMARY KEY, value INTEGER NOT NULL);
CREATE TABLE IF NOT EXISTS nodes(
  id TEXT PRIMARY KEY,
  origin TEXT NOT NULL,              -- goal / lemma
  goal_key TEXT,
  tier TEXT NOT NULL,
  stmt TEXT NOT NULL,                -- Lean の項（命題）
  informal TEXT,
  status TEXT NOT NULL DEFAULT 'open',
  depth INTEGER NOT NULL DEFAULT 0,
  both_sides INTEGER NOT NULL DEFAULT 0,
  lease_token TEXT,                  -- proposed 状態のときの提案元リース
  created_by TEXT,
  created_at REAL NOT NULL,
  closed_at REAL,
  closed_by TEXT
);
CREATE TABLE IF NOT EXISTS reductions(
  id TEXT PRIMARY KEY,
  parent TEXT NOT NULL,
  children TEXT NOT NULL,            -- JSON 配列（順序は帰着定理の仮定の順）
  status TEXT NOT NULL DEFAULT 'proposed',  -- proposed / live / done / dead / void
  lease_token TEXT,
  created_by TEXT,
  created_at REAL NOT NULL
);
CREATE TABLE IF NOT EXISTS artifacts(
  module TEXT PRIMARY KEY,           -- 例 Proofs.L_0001 / Specs.L_0001
  kind TEXT NOT NULL,                -- spec / proof / composed / reduction / refutation
  node TEXT,
  path TEXT NOT NULL,
  sha256 TEXT NOT NULL,
  axioms TEXT,
  agent TEXT,
  accepted_at REAL NOT NULL
);
CREATE TABLE IF NOT EXISTS attempts(
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  node TEXT NOT NULL,
  task TEXT NOT NULL,                -- prove / decompose / refute / audit
  agent TEXT,
  lease_token TEXT,
  outcome TEXT NOT NULL,             -- accepted / rejected / gave_up / expired / no_submission
  detail TEXT,
  created_at REAL NOT NULL
);
CREATE TABLE IF NOT EXISTS leases(
  token TEXT PRIMARY KEY,
  task_key TEXT NOT NULL UNIQUE,
  node TEXT NOT NULL,
  task TEXT NOT NULL,
  agent TEXT NOT NULL,
  role TEXT NOT NULL,
  acquired_at REAL NOT NULL,
  expires_at REAL NOT NULL,
  checks INTEGER NOT NULL DEFAULT 0
);
CREATE TABLE IF NOT EXISTS build_slots(slot INTEGER PRIMARY KEY, holder TEXT, expires_at REAL);
CREATE TABLE IF NOT EXISTS spend(
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  day TEXT NOT NULL, agent TEXT, node TEXT, tier TEXT,
  usd REAL NOT NULL, created_at REAL NOT NULL
);
CREATE TABLE IF NOT EXISTS events(
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  kind TEXT NOT NULL, agent TEXT, detail TEXT, created_at REAL NOT NULL
);
"""

TIER_ORDER = {"T0": 0, "T1": 1, "T2": 2, "T3": 3, "T4": 4, "Tinf": 9}


def today() -> str:
    return _dt.date.today().isoformat()


class DB:
    def __init__(self, path: str | Path):
        self.path = Path(path)
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.conn = sqlite3.connect(str(self.path), timeout=30, isolation_level=None)
        self.conn.row_factory = sqlite3.Row
        self.conn.execute("PRAGMA journal_mode=WAL")
        self.conn.execute("PRAGMA busy_timeout=30000")
        self.conn.executescript(SCHEMA)
        self._depth = 0

    def close(self) -> None:
        self.conn.close()

    @contextlib.contextmanager
    def tx(self) -> Iterator[sqlite3.Connection]:
        """書き込みトランザクション（入れ子可、外側だけが BEGIN IMMEDIATE）。"""
        if self._depth:
            self._depth += 1
            try:
                yield self.conn
            finally:
                self._depth -= 1
            return
        self.conn.execute("BEGIN IMMEDIATE")
        self._depth = 1
        try:
            yield self.conn
            self.conn.execute("COMMIT")
        except BaseException:
            self.conn.execute("ROLLBACK")
            raise
        finally:
            self._depth = 0

    def q(self, sql: str, args: tuple = ()) -> list[sqlite3.Row]:
        return self.conn.execute(sql, args).fetchall()

    def q1(self, sql: str, args: tuple = ()) -> sqlite3.Row | None:
        return self.conn.execute(sql, args).fetchone()

    # ---- meta / ids / events -------------------------------------------------
    def get_meta(self, key: str, default: str | None = None) -> str | None:
        r = self.q1("SELECT value FROM meta WHERE key=?", (key,))
        return r["value"] if r else default

    def set_meta(self, key: str, value: str) -> None:
        self.conn.execute("INSERT OR REPLACE INTO meta(key,value) VALUES(?,?)", (key, value))

    def next_id(self, prefix: str) -> str:
        with self.tx() as c:
            r = c.execute("SELECT value FROM counters WHERE name=?", (prefix,)).fetchone()
            v = (r["value"] if r else 0) + 1
            c.execute("INSERT OR REPLACE INTO counters(name,value) VALUES(?,?)", (prefix, v))
        return f"{prefix}_{v:04d}"

    def event(self, kind: str, agent: str | None, detail) -> None:
        if not isinstance(detail, str):
            detail = json.dumps(detail, ensure_ascii=False)
        self.conn.execute(
            "INSERT INTO events(kind,agent,detail,created_at) VALUES(?,?,?,?)",
            (kind, agent, detail, time.time()),
        )

    # ---- nodes ---------------------------------------------------------------
    def add_node(self, *, node_id: str, origin: str, tier: str, stmt: str, informal: str = "",
                 depth: int = 0, goal_key: str | None = None, both_sides: bool = False,
                 status: str = "open", created_by: str | None = None,
                 lease_token: str | None = None) -> None:
        self.conn.execute(
            "INSERT INTO nodes(id,origin,goal_key,tier,stmt,informal,status,depth,both_sides,"
            "lease_token,created_by,created_at) VALUES(?,?,?,?,?,?,?,?,?,?,?,?)",
            (node_id, origin, goal_key, tier, stmt, informal, status, depth, int(both_sides),
             lease_token, created_by, time.time()),
        )

    def node(self, node_id: str) -> sqlite3.Row | None:
        return self.q1("SELECT * FROM nodes WHERE id=?", (node_id,))

    def nodes(self, status: str | None = None) -> list[sqlite3.Row]:
        if status:
            return self.q("SELECT * FROM nodes WHERE status=? ORDER BY id", (status,))
        return self.q("SELECT * FROM nodes ORDER BY id")

    def count_nodes(self) -> int:
        return self.q1("SELECT COUNT(*) n FROM nodes WHERE status!='void'")["n"]

    def set_node_status(self, node_id: str, status: str, by: str | None = None) -> None:
        self.conn.execute(
            "UPDATE nodes SET status=?, closed_at=?, closed_by=? WHERE id=?",
            (status, time.time(), by, node_id),
        )

    # ---- reductions ----------------------------------------------------------
    def add_reduction(self, rid: str, parent: str, children: list[str], agent: str,
                      lease_token: str) -> None:
        self.conn.execute(
            "INSERT INTO reductions(id,parent,children,status,lease_token,created_by,created_at)"
            " VALUES(?,?,?,?,?,?,?)",
            (rid, parent, json.dumps(children), "proposed", lease_token, agent, time.time()),
        )

    def reduction(self, rid: str) -> sqlite3.Row | None:
        return self.q1("SELECT * FROM reductions WHERE id=?", (rid,))

    def reductions_of(self, parent: str, statuses: tuple[str, ...] | None = None) -> list[sqlite3.Row]:
        rows = self.q("SELECT * FROM reductions WHERE parent=? ORDER BY id", (parent,))
        return [r for r in rows if statuses is None or r["status"] in statuses]

    def reductions_with_child(self, child: str) -> list[sqlite3.Row]:
        return [r for r in self.q("SELECT * FROM reductions WHERE status='live'")
                if child in json.loads(r["children"])]

    def set_reduction_status(self, rid: str, status: str) -> None:
        self.conn.execute("UPDATE reductions SET status=? WHERE id=?", (status, rid))

    # ---- artifacts -----------------------------------------------------------
    def add_artifact(self, *, module: str, kind: str, node: str | None, path: str, sha256: str,
                     axioms: list[str] | None, agent: str | None) -> None:
        self.conn.execute(
            "INSERT OR REPLACE INTO artifacts(module,kind,node,path,sha256,axioms,agent,accepted_at)"
            " VALUES(?,?,?,?,?,?,?,?)",
            (module, kind, node, path, sha256, json.dumps(axioms or []), agent, time.time()),
        )

    def artifact(self, module: str) -> sqlite3.Row | None:
        return self.q1("SELECT * FROM artifacts WHERE module=?", (module,))

    def artifacts(self) -> list[sqlite3.Row]:
        return self.q("SELECT * FROM artifacts ORDER BY module")

    def checked_proof_modules(self) -> set[str]:
        return {r["module"] for r in self.q("SELECT module FROM artifacts WHERE kind!='spec'")}

    # ---- attempts ------------------------------------------------------------
    def add_attempt(self, node: str, task: str, agent: str | None, token: str | None,
                    outcome: str, detail: str = "") -> None:
        self.conn.execute(
            "INSERT INTO attempts(node,task,agent,lease_token,outcome,detail,created_at)"
            " VALUES(?,?,?,?,?,?,?)",
            (node, task, agent, token, outcome, detail[:4000], time.time()),
        )

    def count_attempts(self, node: str, task: str, failed_only: bool = True) -> int:
        sql = "SELECT COUNT(*) n FROM attempts WHERE node=? AND task=?"
        if failed_only:
            sql += " AND outcome!='accepted'"
        return self.q1(sql, (node, task))["n"]

    def lease_had_success(self, token: str) -> bool:
        return self.q1("SELECT COUNT(*) n FROM attempts WHERE lease_token=? AND outcome='accepted'",
                       (token,))["n"] > 0

    # ---- leases --------------------------------------------------------------
    def acquire_lease(self, *, task_key: str, node: str, task: str, agent: str, role: str,
                      ttl: float) -> str | None:
        """task_key が空いていればリースを取る。取れなければ None。"""
        now = time.time()
        token = secrets.token_hex(12)
        with self.tx() as c:
            if c.execute("SELECT 1 FROM leases WHERE task_key=? AND expires_at>?",
                         (task_key, now)).fetchone():
                return None
            c.execute("DELETE FROM leases WHERE task_key=?", (task_key,))
            c.execute(
                "INSERT INTO leases(token,task_key,node,task,agent,role,acquired_at,expires_at)"
                " VALUES(?,?,?,?,?,?,?,?)",
                (token, task_key, node, task, agent, role, now, now + ttl),
            )
        return token

    def lease(self, token: str) -> sqlite3.Row | None:
        r = self.q1("SELECT * FROM leases WHERE token=?", (token,))
        if r and r["expires_at"] <= time.time():
            return None
        return r

    def active_leases(self) -> list[sqlite3.Row]:
        return self.q("SELECT * FROM leases WHERE expires_at>? ORDER BY acquired_at", (time.time(),))

    def leases_of_agent(self, agent: str) -> list[sqlite3.Row]:
        return self.q("SELECT * FROM leases WHERE agent=? AND expires_at>?", (agent, time.time()))

    def beat(self, token: str, ttl: float) -> bool:
        cur = self.conn.execute("UPDATE leases SET expires_at=? WHERE token=? AND expires_at>?",
                                (time.time() + ttl, token, time.time()))
        return cur.rowcount == 1

    def bump_checks(self, token: str) -> int:
        self.conn.execute("UPDATE leases SET checks=checks+1 WHERE token=?", (token,))
        r = self.q1("SELECT checks FROM leases WHERE token=?", (token,))
        return r["checks"] if r else 0

    def drop_lease(self, token: str) -> None:
        self.conn.execute("DELETE FROM leases WHERE token=?", (token,))

    def expired_leases(self) -> list[sqlite3.Row]:
        return self.q("SELECT * FROM leases WHERE expires_at<=?", (time.time(),))

    # ---- build slots (プロセス間セマフォ) ------------------------------------
    def acquire_slot(self, holder: str, n_slots: int, ttl: float, wait: float = 3600,
                     poll: float = 2.0) -> int:
        deadline = time.time() + wait
        while True:
            now = time.time()
            with self.tx() as c:
                for s in range(n_slots):
                    r = c.execute("SELECT holder, expires_at FROM build_slots WHERE slot=?",
                                  (s,)).fetchone()
                    if r is None or r["holder"] is None or r["expires_at"] <= now:
                        c.execute("INSERT OR REPLACE INTO build_slots(slot,holder,expires_at)"
                                  " VALUES(?,?,?)", (s, holder, now + ttl))
                        return s
            if time.time() > deadline:
                raise TimeoutError("ビルド枠を確保できませんでした")
            time.sleep(poll)

    def release_slot(self, slot: int, holder: str) -> None:
        self.conn.execute("UPDATE build_slots SET holder=NULL, expires_at=NULL"
                          " WHERE slot=? AND holder=?", (slot, holder))

    # ---- spend ---------------------------------------------------------------
    def add_spend(self, usd: float, agent: str | None, node: str | None, tier: str | None) -> None:
        self.conn.execute(
            "INSERT INTO spend(day,agent,node,tier,usd,created_at) VALUES(?,?,?,?,?,?)",
            (today(), agent, node, tier, float(usd), time.time()),
        )

    def spent_today(self, tier: str | None = None) -> float:
        if tier is None:
            r = self.q1("SELECT COALESCE(SUM(usd),0) s FROM spend WHERE day=?", (today(),))
        else:
            r = self.q1("SELECT COALESCE(SUM(usd),0) s FROM spend WHERE day=? AND tier=?",
                        (today(), tier))
        return float(r["s"])
