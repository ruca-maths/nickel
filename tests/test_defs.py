"""定義モジュール（Defs.D_xxxx）と反証側の帰着（negate）の結合テスト。実際の Lean を使う。

本題役の G4（∀ n, n = 0、Tinf・both_sides）を、定義モジュールで導入した対象を使った
「子補題 ⇒ ¬親」の帰着で反証し、子補題の証明で ¬親 が機械的に合成されることを確かめる。
"""
import json
import shutil
import sys
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO))

from core.config import load_config  # noqa: E402
from core.desk import Desk  # noqa: E402
from tests.test_system import make_env, proof_src, write  # noqa: E402

HAVE_LAKE = shutil.which("lake") is not None


@unittest.skipUnless(HAVE_LAKE, "lake が見つからない")
class TestDefsAndNegate(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = make_env()
        cls.d = Desk(load_config(cls.tmp / "config.yaml"))
        cls.d.approve_targets("tester")
        cls.d.init()

    def lease(self, task, node, agent, role):
        tok = self.d.db.acquire_lease(task_key=f"{task}:{node}", node=node, task=task,
                                      agent=agent, role=role, ttl=600)
        self.assertIsNotNone(tok)
        return tok

    def test_1_define_rejects_cheats(self):
        tok = self.lease("decompose", "L_0004", "architect-1", "architect")
        bad = write(self.d, "architect-1", "bad.lean",
                    "namespace Defs.NEW\naxiom cheat : False\nend Defs.NEW\n")
        self.assertFalse(self.d.define(bad, tok)["ok"])
        bad2 = write(self.d, "architect-1", "bad2.lean",
                     "namespace Defs.NEW\ndef x : Nat := sorry\nend Defs.NEW\n")
        self.assertFalse(self.d.define(bad2, tok)["ok"])
        self.d.release("test", "", tok)

    def test_2_negate_reduction_with_defs(self):
        tok = self.lease("decompose", "L_0004", "architect-1", "architect")
        f = write(self.d, "architect-1", "defs.lean",
                  "namespace Defs.NEW\n/-- 反例の値 -/\ndef witness : Nat := 1\nend Defs.NEW\n")
        r = self.d.define(f, tok)
        self.assertTrue(r["ok"], r)
        dmod = r["module"]  # Defs.D_0002（D_0001 は test_1 で番号だけ消費）
        cj = write(self.d, "architect-1", "children.json", json.dumps({"negate": True, "children": [
            {"stmt": f"{dmod}.witness ≠ 0", "informal": "反例の値は 0 でない", "imports": [dmod]}]}))
        pr = self.d.propose(cj, tok)
        child, rid = pr["children"][0], pr["reduction"]
        self.assertIn("¬ Specs.L_0004.stmt", pr["required_shape"])
        rf = write(self.d, "architect-1", f"{rid}.lean",
                   f"import Specs.{child}\nimport Specs.L_0004\nnamespace Proofs.{rid}\n"
                   f"theorem main : Specs.{child}.stmt → ¬ Specs.L_0004.stmt := by\n"
                   f"  intro h hall\n  unfold Specs.L_0004.stmt Toy.Goals.G4 at hall\n"
                   f"  unfold Specs.{child}.stmt at h\n  exact h (hall _)\nend Proofs.{rid}\n")
        r = self.d.submit(rf, "negate", tok)
        self.assertTrue(r["ok"], r)
        self.assertEqual(self.d.db.node("L_0004")["status"], "open")
        # 子補題を証明すると、親の反証が機械的に合成される
        tok2 = self.lease("prove", child, "prover-1", "prover")
        pf = write(self.d, "prover-1", f"{child}.lean", proof_src(
            child, child, f"theorem main : Specs.{child}.stmt := by\n  unfold Specs.{child}.stmt {dmod}.witness\n"
            f"  decide", extra_imports=f"import {dmod}"))
        r = self.d.submit(pf, "", tok2)
        self.assertTrue(r["ok"], r)
        self.assertEqual(self.d.db.node("L_0004")["status"], "refuted")
        self.assertIn("機械生成", (self.tmp / "Proofs" / "N_0004.lean").read_text(encoding="utf-8"))
        stop = self.tmp / "STOP"
        self.assertIn("RESULT", stop.read_text(encoding="utf-8"))  # 本題役が閉じたら停止
        g = json.loads((self.tmp / "status" / "graph.json").read_text(encoding="utf-8"))
        self.assertTrue(next(x for x in g["reductions"] if x["id"] == rid)["negate"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
