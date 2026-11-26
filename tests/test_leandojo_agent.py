"""LeanDojo-v2 子機エージェント（tools/leandojo_agent.py）の結合テスト。

生成モデルの代わりに fixed バックエンド（LEANDOJO_FIXED の文字列を返す）を使い、
オーケストレータ → エージェント → desk check → submit の経路と、失敗時の release を確かめる。
"""
import json
import os
import shutil
import sys
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO))

from core.config import load_config  # noqa: E402
from core.desk import Desk  # noqa: E402
from core.orchestrator import Orchestrator  # noqa: E402
from tests.test_system import make_env  # noqa: E402

HAVE_LAKE = shutil.which("lake") is not None


def use_leandojo(tmp: Path) -> None:
    p = tmp / "config.yaml"
    cfg = json.loads(p.read_text(encoding="utf-8"))
    cfg["runner"]["cmd"] = [sys.executable, str(REPO / "tools" / "leandojo_agent.py")]
    p.write_text(json.dumps(cfg, ensure_ascii=False, indent=2), encoding="utf-8")


class TestCleanProof(unittest.TestCase):
    def setUp(self):
        os.environ.setdefault("RESEARCH_CONFIG", str(REPO / "config.yaml"))
        sys.path.insert(0, str(REPO / "tools"))
        import leandojo_agent
        self.m = leandojo_agent

    def test_extracts_tactics(self):
        text = "Here:\n```lean4\ntheorem main : P := by\n  intro n\n  rfl\n```\n"
        self.assertEqual(self.m.clean_proof(text), "  intro n\n  rfl")

    def test_rejects_cheats(self):
        self.assertEqual(self.m.clean_proof("  sorry"), "")
        self.assertEqual(self.m.clean_proof("  exact (by native_decide)"), "")

    def test_defs_imports(self):
        self.assertEqual(self.m.defs_imports("∃ y : Defs.D_0007.Y, ¬ Defs.D_0001.P y"),
                         ["Defs.D_0001", "Defs.D_0007"])


@unittest.skipUnless(HAVE_LAKE, "lake が見つからない")
class TestLeanDojoAgent(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = make_env()
        use_leandojo(cls.tmp)
        cls.cfg = load_config(cls.tmp / "config.yaml")
        cls.d = Desk(cls.cfg)
        cls.d.approve_targets("tester")
        cls.d.init()
        os.environ["LEANDOJO_BACKEND"] = "fixed"
        os.environ["LEANDOJO_SAMPLES"] = "2"

    def test_1_wrong_proof_is_released(self):
        os.environ["LEANDOJO_FIXED"] = "exact trivial"
        o = Orchestrator(self.cfg, log=lambda *a: None)
        o.run(max_sessions=1)
        self.assertEqual(self.d.db.node("L_0001")["status"], "open")
        fails = (self.tmp / "memory" / "failures.jsonl").read_text(encoding="utf-8")
        self.assertIn("LeanDojo-v2", fails)

    def test_2_correct_proof_is_submitted(self):
        os.environ["LEANDOJO_FIXED"] = "```lean4\ntheorem x := by\n  unfold Toy.Goals.G1\n  intro n\n  rfl\n```"
        o = Orchestrator(self.cfg, log=lambda *a: None)
        o.run(max_sessions=1)
        self.assertEqual(self.d.db.node("L_0001")["status"], "checked")


if __name__ == "__main__":
    unittest.main(verbosity=2)
