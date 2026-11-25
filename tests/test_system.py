"""実際の Lean 4 を使う結合テスト（Mathlib 不要の玩具フィクスチャで実行）。

正常証明・チート証明（命題すり替え / sorry / axiom）・Targets 改竄・競合リース・
帰着と機械的合成・反証と本題停止・オーケストレータ・受理後改竄検出を順に検査する。
"""
import json
import shutil
import sys
import tempfile
import time
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO))

from core import static_filter, verifier as verifier_mod  # noqa: E402
from core.config import load_config  # noqa: E402
from core.desk import Desk  # noqa: E402
from core.orchestrator import Orchestrator  # noqa: E402
from core.verifier import InfraError  # noqa: E402

HAVE_LAKE = shutil.which("lake") is not None


def make_env() -> Path:
    tmp = Path(tempfile.mkdtemp(prefix="mresearch-test-"))
    shutil.copytree(REPO / "tests" / "fixture_lean", tmp, dirs_exist_ok=True)
    shutil.copytree(REPO / "prompts", tmp / "prompts")
    cfg = {
        "project": {"lean_root": ".", "db_path": "state/research.db",
                    "failures_log": "memory/failures.jsonl", "audits_dir": "memory/audits",
                    "work_dir": "work"},
        "lean": {"lake": "lake", "spec_imports": ["Targets"], "spec_opens": [],
                 "allowed_import_prefixes": ["Targets", "Specs"],
                 "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
                 "build_timeout_sec": 300, "check_timeout_sec": 300,
                 "max_heartbeats_cap": 1000000, "build_slots": 1},
        "limits": {"max_attempts_per_task": 5, "decompose_after_failures": 2,
                   "refute_after_failures": 2, "max_nodes": 50, "max_depth": 4,
                   "max_reductions_per_node": 3, "max_children_per_reduction": 6,
                   "lease_ttl_sec": 600, "max_checks_per_lease": 30},
        "budget": {"daily_usd": 10.0, "session_reserve_usd": 0.1},
        "circuit_breaker": {"max_consecutive_failures": 4, "cooldown_sec": 60, "max_infra_errors": 3},
        "runner": {"cmd": [sys.executable, str(REPO / "tests" / "fake_agent.py")],
                   "cost_field": "total_cost_usd", "session_timeout_sec": 300, "idle_sleep_sec": 1},
        "agents": [{"id": "prover-1", "role": "prover", "model": "x", "max_turns": 1}],
        "git": {"autocommit": False},
    }
    (tmp / "config.yaml").write_text(json.dumps(cfg, ensure_ascii=False, indent=2), encoding="utf-8")
    return tmp


def write(d: Desk, agent: str, name: str, text: str) -> str:
    p = d.agent_dir(agent) / name
    p.write_text(text, encoding="utf-8")
    return str(p)


def proof_src(mod: str, spec: str, body: str, extra_imports: str = "") -> str:
    return (f"import Specs.{spec}\n{extra_imports}\nnamespace Proofs.{mod}\n\n"
            f"{body}\n\nend Proofs.{mod}\n")


@unittest.skipUnless(HAVE_LAKE, "lake が見つからない")
class TestSystem(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = make_env()
        cls.cfg = load_config(cls.tmp / "config.yaml")
        cls.d = Desk(cls.cfg)

    def lease(self, task, node, agent, role):
        tok = self.d.db.acquire_lease(task_key=f"{task}:{node}", node=node, task=task,
                                      agent=agent, role=role, ttl=600)
        self.assertIsNotNone(tok)
        return tok

    def test_01_approve_and_init(self):
        with self.assertRaises(InfraError):  # 未承認では検証しない
            self.d.v.assert_targets_locked()
        self.d.approve_targets("tester")
        res = self.d.init()
        self.assertEqual([a["goal"] for a in res["added"]], ["G1", "G2", "G3", "G4"])
        self.assertEqual(self.d.init()["added"], [])  # 冪等
        self.assertTrue((self.tmp / "Specs" / "L_0001.lean").exists())
        self.assertTrue((self.tmp / "STATUS.md").exists())

    def test_02_statement_substitution_rejected(self):
        t = self.d.lease_next("prover-1", "prover")
        self.assertEqual((t["task"], t["context"]["node"]), ("prove", "L_0001"))
        f = write(self.d, "prover-1", "L_0001.lean",
                  proof_src("L_0001", "L_0001", "theorem main : True := trivial"))
        r = self.d.submit(f, "cheat", t["lease_token"])
        self.assertFalse(r["ok"])
        self.assertIn("型", r["reason"])
        self.assertFalse((self.tmp / "Proofs" / "L_0001.lean").exists())

    def _without_filter(self, src: str):
        orig = static_filter.check_proof
        verifier_mod.static_filter.check_proof = lambda *a, **k: static_filter.FilterResult(True)
        try:
            tok = self.lease("prove", "L_0001", "prover-1", "prover")
            f = write(self.d, "prover-1", "L_0001.lean", src)
            return self.d.submit(f, "cheat", tok)
        finally:
            verifier_mod.static_filter.check_proof = orig

    def test_03_sorry_caught_by_axiom_check(self):
        r = self._without_filter(proof_src("L_0001", "L_0001",
                                           "theorem main : Specs.L_0001.stmt := by sorry"))
        self.assertFalse(r["ok"])
        self.assertIn("sorryAx", r["reason"])

    def test_04_custom_axiom_caught(self):
        r = self._without_filter(proof_src("L_0001", "L_0001",
                                           "axiom cheat : False\ntheorem main : Specs.L_0001.stmt := cheat.elim"))
        self.assertFalse(r["ok"])
        self.assertIn("cheat", r["reason"])

    def test_05_static_filter_rejects_before_build(self):
        tok = self.lease("prove", "L_0001", "prover-1", "prover")
        f = write(self.d, "prover-1", "L_0001.lean",
                  proof_src("L_0001", "L_0001", "theorem main : Specs.L_0001.stmt := by native_decide"))
        r = self.d.submit(f, "", tok)
        self.assertFalse(r["ok"])
        self.assertIn("静的フィルタ", r["reason"])

    def test_06_correct_proof_accepted(self):
        tok = self.lease("prove", "L_0001", "prover-1", "prover")
        f = write(self.d, "prover-1", "L_0001.lean", proof_src(
            "L_0001", "L_0001",
            "theorem main : Specs.L_0001.stmt := by\n  unfold Specs.L_0001.stmt Toy.Goals.G1\n  intro n\n  rfl"))
        chk = self.d.check(f, tok)
        self.assertTrue(chk["ok"], chk)
        r = self.d.submit(f, "ok", tok)
        self.assertTrue(r["ok"], r)
        self.assertEqual(self.d.db.node("L_0001")["status"], "checked")
        self.assertIn("✅", (self.tmp / "STATUS.md").read_text(encoding="utf-8"))

    def test_07_outside_workdir_rejected(self):
        tok = self.lease("prove", "L_0002", "prover-1", "prover")
        with self.assertRaises(Exception):
            self.d.submit(str(self.tmp / "Targets" / "Defs.lean"), "", tok)
        self.d.release("test", "", tok)

    def test_08_targets_tamper_detected(self):
        p = self.tmp / "Targets" / "Defs.lean"
        orig = p.read_text(encoding="utf-8")
        p.write_text(orig + "\n-- tampered\n", encoding="utf-8")
        try:
            with self.assertRaises(InfraError):
                self.d.v.assert_targets_locked()
        finally:
            p.write_text(orig, encoding="utf-8")
        self.d.v.assert_targets_locked()

    def test_09_lease_conflict_and_expiry(self):
        a = self.d.lease_next("prover-1", "prover")
        b = self.d.lease_next("prover-2", "prover")
        self.assertNotEqual(a["context"]["node"], b["context"]["node"])
        # 同じエージェントがもう一度 next しても同じリースが返る
        self.assertEqual(self.d.lease_next("prover-1", "prover")["lease_token"], a["lease_token"])
        key = f"prove:{a['context']['node']}"
        self.assertIsNone(self.d.db.acquire_lease(task_key=key, node="x", task="prove",
                                                  agent="prover-3", role="prover", ttl=600))
        self.d.db.conn.execute("UPDATE leases SET expires_at=0 WHERE token=?", (a["lease_token"],))
        self.assertEqual(self.d.sweep()["expired"], 1)
        c = self.d.lease_next("prover-3", "prover")
        self.assertEqual(c["context"]["node"], a["context"]["node"])
        for t in (b, c):
            self.d.release("test", "", t["lease_token"])
        with self.assertRaises(Exception):
            self.d.submit("x", "", a["lease_token"])  # 期限切れトークンは無効

    def test_10_reduction_and_composition(self):
        # L_0003 は T3 の目標なので失敗回数に関係なく分解対象になる
        self.assertIn(("decompose", "L_0003"),
                      [(task, nid) for _, task, nid in self.d.candidates("architect")])
        t = self.d.task_info(self.lease("decompose", "L_0003", "architect-1", "architect"))
        cj = write(self.d, "architect-1", "children.json", json.dumps({"children": [
            {"stmt": "∀ n : Nat, 0 + n = n", "informal": "左単位元"},
            {"existing": "L_0001"}]}))
        pr = self.d.propose(cj, t["lease_token"])
        self.assertEqual(pr["children"], ["L_0005", "L_0001"])
        self.assertEqual(self.d.db.node("L_0005")["status"], "proposed")
        rid = pr["reduction"]
        f = write(self.d, "architect-1", f"{rid}.lean",
                  "import Specs.L_0005\nimport Specs.L_0001\nimport Specs.L_0003\n"
                  f"namespace Proofs.{rid}\n"
                  "theorem main : Specs.L_0005.stmt → Specs.L_0001.stmt → Specs.L_0003.stmt := by\n"
                  "  intro h1 h2\n  unfold Specs.L_0003.stmt Toy.Goals.G3\n"
                  "  unfold Specs.L_0001.stmt Toy.Goals.G1 at h2\n  unfold Specs.L_0005.stmt at h1\n"
                  f"  exact ⟨h1, h2⟩\nend Proofs.{rid}\n")
        r = self.d.submit(f, "split", t["lease_token"])
        self.assertTrue(r["ok"], r)
        self.assertEqual(self.d.db.node("L_0005")["status"], "open")
        self.assertEqual(self.d.db.node("L_0003")["status"], "open")
        tok = self.lease("prove", "L_0005", "prover-2", "prover")
        f = write(self.d, "prover-2", "L_0005.lean", proof_src(
            "L_0005", "L_0005",
            "theorem main : Specs.L_0005.stmt := by\n  unfold Specs.L_0005.stmt\n  intro n\n  exact Nat.zero_add n"))
        r = self.d.submit(f, "", tok)
        self.assertTrue(r["ok"], r)
        # 子がすべて Checked になったので親が機械的に合成される
        self.assertEqual(self.d.db.node("L_0003")["status"], "checked")
        self.assertIn("機械生成", (self.tmp / "Proofs" / "L_0003.lean").read_text(encoding="utf-8"))
        self.assertEqual(self.d.db.reduction(rid)["status"], "done")

    def test_11_audit_and_refutation_stops_on_main_problem(self):
        t = self.d.lease_next("redteam-1", "redteam")
        self.assertEqual(t["task"], "audit")
        f = write(self.d, "redteam-1", "audit.md", "# 監査\n問題なし（テスト）\n")
        self.assertTrue(self.d.audit(f, t["lease_token"])["ok"])
        # 本題（both_sides）は失敗回数に関係なく反証対象になる
        self.assertIn(("refute", "L_0004"), [(task, nid) for _, task, nid in self.d.candidates("redteam")])
        t = self.d.task_info(self.lease("refute", "L_0004", "redteam-1", "redteam"))
        f = write(self.d, "redteam-1", "N_0004.lean", proof_src(
            "N_0004", "L_0004",
            "theorem main : ¬ Specs.L_0004.stmt := by\n  unfold Specs.L_0004.stmt Toy.Goals.G4\n"
            "  intro h\n  exact absurd (h 1) (by decide)"))
        r = self.d.submit(f, "counterexample n=1", t["lease_token"])
        self.assertTrue(r["ok"], r)
        self.assertEqual(self.d.db.node("L_0004")["status"], "refuted")
        stop = self.tmp / "STOP"
        self.assertTrue(stop.exists())
        self.assertIn("RESULT", stop.read_text(encoding="utf-8"))
        stop.unlink()

    def test_12_orchestrator_with_fake_agent(self):
        o = Orchestrator(self.cfg, log=lambda *a: None)
        reason = o.run(max_sessions=1)
        self.assertEqual(reason, "完了")
        self.assertEqual(self.d.db.node("L_0002")["status"], "checked")
        self.assertAlmostEqual(self.d.db.spent_today(), 0.05)

    def test_13_budget_stop(self):
        self.d.db.add_spend(20.0, "x", None, None)
        o = Orchestrator(self.cfg, log=lambda *a: None)
        self.assertIn("予算", o.run(once=True))

    def test_14_post_accept_tamper_detected(self):
        self.assertEqual(self.d.v.audit_artifacts(), [])
        p = self.tmp / "Proofs" / "L_0001.lean"
        orig = p.read_text(encoding="utf-8")
        p.write_text(orig + "\n", encoding="utf-8")
        self.assertEqual(len(self.d.v.audit_artifacts()), 1)
        p.write_text(orig, encoding="utf-8")


if __name__ == "__main__":
    unittest.main(verbosity=2)
