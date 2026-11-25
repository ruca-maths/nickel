import Targets.Defs
namespace Toy.Goals
def G1 : Prop := ∀ n : Nat, n + 0 = n
def G2 : Prop := ∀ n : Nat, Toy.Double n = n + n
def G3 : Prop := (∀ n : Nat, 0 + n = n) ∧ (∀ n : Nat, n + 0 = n)
def G4 : Prop := ∀ n : Nat, n = 0
end Toy.Goals
