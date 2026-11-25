"""静的フィルタの単体テスト（Lean 不要）。"""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from core import static_filter as sf  # noqa: E402

ALLOWED = dict(allowed_prefixes=["Mathlib", "Targets", "Specs"], allowed_modules={"Proofs.L_0002"})


def proof(body: str, mid: str = "L_0001", imports: str = "import Specs.L_0001") -> str:
    return f"{imports}\n\nnamespace Proofs.{mid}\n\n{body}\n\nend Proofs.{mid}\n"


GOOD = proof("theorem main : Specs.L_0001.stmt := by\n  intro n\n  rfl")


class TestProofFilter(unittest.TestCase):
    def ok(self, src, mid="L_0001"):
        return sf.check_proof(src, mid, **ALLOWED)

    def test_good(self):
        r = self.ok(GOOD)
        self.assertTrue(r.ok, r.violations)

    def test_sorry_in_comment_and_string_is_fine(self):
        src = proof('-- sorry\n/- nested /- sorry -/ axiom -/\ntheorem main : Specs.L_0001.stmt := by\n'
                    '  have : "sorry" = "sorry" := rfl\n  intro n; rfl')
        r = self.ok(src)
        self.assertTrue(r.ok, r.violations)

    def test_rejects_cheats(self):
        cheats = {
            "sorry": "theorem main : Specs.L_0001.stmt := by sorry",
            "admit": "theorem main : Specs.L_0001.stmt := by admit",
            "axiom": "axiom cheat : False\ntheorem main : Specs.L_0001.stmt := cheat.elim",
            "native": "theorem main : Specs.L_0001.stmt := by native_decide",
            "decide+native": "theorem main : Specs.L_0001.stmt := by decide +native",
            "guillemet": "theorem main : Specs.L_0001.stmt := by exact «sorry»",
            "macro": 'macro "magic" : tactic => `(tactic| sorry)\ntheorem main : Specs.L_0001.stmt := by magic',
            "eval": "#eval 1\ntheorem main : Specs.L_0001.stmt := by intro n; rfl",
            "open Lean": "open Lean in\ntheorem main : Specs.L_0001.stmt := by intro n; rfl",
            "heartbeats0": "set_option maxHeartbeats 0 in\ntheorem main : Specs.L_0001.stmt := by intro n; rfl",
            "debug": "set_option debug.skipKernelTC true in\ntheorem main : Specs.L_0001.stmt := by intro n; rfl",
            "implemented_by": "@[implemented_by foo] def bar : Nat := 0\ntheorem main : Specs.L_0001.stmt := by intro n; rfl",
            "root": "theorem _root_.Proofs.L_0009.main : True := trivial\ntheorem main : Specs.L_0001.stmt := by intro n; rfl",
        }
        for name, body in cheats.items():
            with self.subTest(name):
                self.assertFalse(self.ok(proof(body)).ok, name)

    def test_namespace_escape(self):
        src = ("import Specs.L_0001\nnamespace Proofs.L_0001\nend L_0001\n"
               "theorem Proofs.L_0002.main : True := trivial\nnamespace L_0001\n"
               "theorem main : Specs.L_0001.stmt := by intro n; rfl\nend Proofs.L_0001\n")
        self.assertFalse(self.ok(src).ok)

    def test_wrong_namespace(self):
        self.assertFalse(self.ok(GOOD, mid="L_0003").ok)

    def test_imports(self):
        self.assertTrue(self.ok(proof("theorem main : Specs.L_0001.stmt := by intro n; rfl",
                                      imports="import Mathlib\nimport Specs.L_0001\nimport Proofs.L_0002")).ok)
        for bad in ["import Proofs.L_0005", "import Lean", "import Std.Tactic", "import Mathlib.Foo\nimport Proofs.R_0001"]:
            with self.subTest(bad):
                self.assertFalse(self.ok(proof("theorem main : Specs.L_0001.stmt := by intro n; rfl",
                                               imports=bad)).ok)

    def test_forbidden_full_mathlib(self):
        src = proof("theorem main : Specs.L_0001.stmt := by intro n; rfl",
                    imports="import Mathlib\nimport Specs.L_0001")
        self.assertFalse(sf.check_proof(src, "L_0001", forbidden_imports=["Mathlib"], **ALLOWED).ok)
        src = proof("theorem main : Specs.L_0001.stmt := by intro n; rfl",
                    imports="import Mathlib.Topology.Bases\nimport Specs.L_0001")
        self.assertTrue(sf.check_proof(src, "L_0001", forbidden_imports=["Mathlib"], **ALLOWED).ok)

    def test_late_import(self):
        src = GOOD + "\nimport Mathlib\n"
        self.assertFalse(self.ok(src).ok)


class TestSpecFilter(unittest.TestCase):
    def test_good(self):
        for s in ["∀ (X : Type) [TopologicalSpace X], MSpace.IsM3 X → NormalSpace X",
                  "∀ s : Set ℕ, {x | x ∈ s} = s", "Toy.Goals.G1"]:
            with self.subTest(s):
                r = sf.check_spec_text(s)
                self.assertTrue(r.ok, r.violations)

    def test_injection(self):
        for s in ["True\ntheorem x : False := sorry", "True\nend Specs.L_0001\naxiom bad : False",
                  "True -- comment", "(by trivial : True)", "let x := 1; x = x", "",
                  'True ∧ "a" = "a"', "True\nset_option maxHeartbeats 1 in", "True\n#eval 1"]:
            with self.subTest(s):
                self.assertFalse(sf.check_spec_text(s).ok, s)


if __name__ == "__main__":
    unittest.main()
