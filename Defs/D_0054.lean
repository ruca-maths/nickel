import Mathlib.Order.Zorn
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Equiv.List
import Mathlib.Order.Filter.AtTopBot.Basic
import Defs.D_0053

namespace Defs.D_0054

/-!
Chen–Wang Prop 9.1 の補修: **≤*-非有界な mad family の存在**。

論文は「𝒜 = ⋃ 𝒜_i なら非有界な 𝒜_i がある」を 𝒜 の非有界性から導くが、mad family の非有界性は
示していない。ここでは関数 f の枝 b_f = {encode (f の長さ n の初期部分) : n} を使う。
* `branch_infinite`, `branch_ad` : b_f は無限、f ≠ g なら b_f ∩ b_g は有限。
* `BoundedBy a g` : 「a の k 番目の元 ≤ g k が十分大きい k で成り立つ」を数え上げで表したもの
  （a ∩ [0, g k] が k+1 個以上の元を持つ）。
* `branch_not_bounded` : 任意の g に対し、ある f の枝は g で抑えられない。
* `exists_unbounded_mad` : どの g にも抑えられない元を持つ mad family が存在する
  （枝全体は IsAD で、それを `Defs.D_0053.exists_mad_extending` で延長する）。
-/

open Filter Defs.D_0053

/-- f の長さ n の初期部分のコード。 -/
def iseg (f : ℕ → ℕ) (n : ℕ) : ℕ := Encodable.encode (List.ofFn (fun i : Fin n => f i))

/-- f の枝。 -/
def branch (f : ℕ → ℕ) : Set ℕ := Set.range (iseg f)

theorem iseg_inj {f g : ℕ → ℕ} {n n' : ℕ} (h : iseg f n = iseg g n') :
    n = n' ∧ ∀ i < n, f i = g i := by
  have h' := Encodable.encode_injective h
  have hlen := congrArg List.length h'
  simp only [List.length_ofFn] at hlen
  subst hlen
  refine ⟨rfl, fun i hi => ?_⟩
  have := congrArg (fun l => l[i]?) h'
  simpa [hi] using this

theorem branch_infinite (f : ℕ → ℕ) : (branch f).Infinite :=
  Set.infinite_range_of_injective (fun n n' h => (iseg_inj h).1)

theorem branch_ad {f g : ℕ → ℕ} (hfg : f ≠ g) : (branch f ∩ branch g).Finite := by
  obtain ⟨d, hd⟩ : ∃ d, f d ≠ g d := by
    by_contra h; push_neg at h; exact hfg (funext h)
  apply (Set.finite_lt_nat (d + 1)).image (iseg f) |>.subset
  rintro x ⟨⟨n, rfl⟩, ⟨n', hn'⟩⟩
  obtain ⟨rfl, hagree⟩ := iseg_inj hn'.symm
  refine ⟨n, ?_, rfl⟩
  show n < d + 1
  by_contra hlt
  exact hd (hagree d (by omega))

theorem branch_isAD : IsAD (Set.range branch) := by
  refine ⟨?_, ?_⟩
  · rintro a ⟨f, rfl⟩; exact branch_infinite f
  · rintro a ⟨f, rfl⟩ b ⟨g, rfl⟩ hab
    exact branch_ad (fun h => hab (h ▸ rfl))

/-- a の k 番目の元 ≤ g k（十分大きい k）。 -/
def BoundedBy (a : Set ℕ) (g : ℕ → ℕ) : Prop :=
  ∀ᶠ k in atTop, ∃ s : Finset ℕ, ↑s ⊆ a ∧ k + 1 ≤ s.card ∧ ∀ x ∈ s, x ≤ g k

theorem le_iseg (f : ℕ → ℕ) (n : ℕ) (i : ℕ) (hi : i < n) : f i ≤ iseg f n := by
  unfold iseg
  induction n generalizing f i with
  | zero => omega
  | succ n ih =>
    rw [List.ofFn_succ]
    show f i ≤ Encodable.encode (f 0 :: List.ofFn fun j : Fin n => f j.succ)
    simp only [Encodable.encode_list_cons, Encodable.encode_nat]
    rcases i with _ | i
    · exact le_trans (Nat.left_le_pair _ _) (Nat.le_succ _)
    · have := ih (fun j => f (j + 1)) i (by omega)
      simp only [Fin.val_succ] at this ⊢
      exact le_trans this (le_trans (Nat.right_le_pair _ _) (Nat.le_succ _))

/-- 速く増える f の枝は g で抑えられない。 -/
theorem branch_not_bounded (g : ℕ → ℕ) : ¬ BoundedBy (branch (fun i => g (i + 2) + 1)) g := by
  intro hb
  obtain ⟨K, hK⟩ := eventually_atTop.mp hb
  obtain ⟨s, hs, hcard, hle⟩ := hK (K + 2) (by omega)
  -- s の元は iseg n の形で、n ≥ K+2 なら iseg n ≥ g (K+2) + 1 > g (K+2)
  have hsub : s ⊆ (Finset.range (K + 2)).image (iseg (fun i => g (i + 2) + 1)) := by
    intro x hx
    obtain ⟨n, rfl⟩ := hs hx
    rw [Finset.mem_image]
    refine ⟨n, Finset.mem_range.mpr ?_, rfl⟩
    by_contra hn
    push_neg at hn
    have h1 := le_iseg (fun i => g (i + 2) + 1) n K (by omega)
    have h2 := hle _ hx
    omega
  have := Finset.card_le_card hsub
  have h3 := Finset.card_image_le (s := Finset.range (K + 2))
    (f := iseg (fun i => g (i + 2) + 1))
  rw [Finset.card_range] at h3
  omega

/-- どの g にも抑えられない元を持つ mad family が存在する。 -/
theorem exists_unbounded_mad :
    ∃ F, IsMAD F ∧ ∀ g : ℕ → ℕ, ∃ a ∈ F, ¬ BoundedBy a g := by
  obtain ⟨F, hsub, hF⟩ := exists_mad_extending branch_isAD
  exact ⟨F, hF, fun g => ⟨_, hsub ⟨_, rfl⟩, branch_not_bounded g⟩⟩

end Defs.D_0054
