import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Zorn
import Mathlib.Basic.Countable.Basic
import Mathlib.Data.Nat.Pairing

/-!
# ZFC Repair of Chen–Wang Proposition 9.1 (Unbounded MAD Families)

While `work/research/ChenWang_Audit2_BoundedMAD.lean` showed that not *every*
MAD family on `ℕ` is unbounded in `(ℕ^ℕ, ≤*)`, Chen–Wang's Proposition 9.1
is completely repaired in ZFC by choosing an **unbounded** MAD family:

1. `exists_unbounded_AD`: Using an injection `enc : List ℕ ↪ ℕ`, the family of
   branches `A_f := {enc (f.take (k+1)) | k : ℕ}` (`f : ℕ → ℕ`) forms an
   almost disjoint family on `ℕ` of size `2^ℵ₀` that is unbounded in `(ℕ^ℕ, ≤*)`.
2. `exists_unbounded_MAD`: Extending `A_f` via Zorn's Lemma yields a maximal
   almost disjoint (MAD) family `ℳ` on `ℕ` that is unbounded in `(ℕ^ℕ, ≤*)`.
3. `prop_9_1_repaired`: For any unbounded family `ℳ` (in particular, the MAD
   family from (2)), if `ℳ ⊆ ⋃ i : ℕ, ℳ_i`, then some `ℳ_i` is unbounded.
-/

namespace Research.ChenWangUnboundedMAD

open Set Filter
open scoped Classical

/-- An infinite subset family `𝒜` on `ℕ` is pairwise almost disjoint if distinct
members have finite intersection. -/
def IsAlmostDisjoint (𝒜 : Set (Set ℕ)) : Prop :=
  (∀ A ∈ 𝒜, A.Infinite) ∧
  (∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → (A ∩ B).Finite)

/-- A MAD (maximal almost disjoint) family on `ℕ`. -/
def IsMAD (𝒜 : Set (Set ℕ)) : Prop :=
  IsAlmostDisjoint 𝒜 ∧
  ∀ X : Set ℕ, X.Infinite → ∃ A ∈ 𝒜, (X ∩ A).Infinite

/-- `𝒜` is bounded in `(ℕ^ℕ, ≤*)` via strictly increasing enumerations `Nat.nth (· ∈ A)`. -/
def IsBoundedFamily (𝒜 : Set (Set ℕ)) : Prop :=
  ∃ g : ℕ → ℕ, ∀ A ∈ 𝒜, ∀ᶠ k in atTop, Nat.nth (· ∈ A) k ≤ g k

/-- Explicit injective encoding `List ℕ → ℕ` using `Nat.pair`. -/
def encodeList : List ℕ → ℕ
  | [] => 0
  | a :: l => Nat.pair a (encodeList l) + 1

theorem encodeList_injective : Function.Injective encodeList := by
  intro l₁ l₂ h
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons b bs => simp [encodeList] at h
  | cons a as ih =>
    cases l₂ with
    | nil => simp [encodeList] at h
    | cons b bs =>
      simp only [encodeList, Nat.succ.injEq] at h
      have hp := Nat.pair_eq_pair.mp h
      rw [hp.1, ih hp.2]

/-- Prefix of length `k + 1` of a sequence `f : ℕ → ℕ`. -/
def prefixList (f : ℕ → ℕ) : ℕ → List ℕ
  | 0 => [f 0]
  | k + 1 => f (k + 1) :: prefixList f k

theorem prefixList_length (f : ℕ → ℕ) (k : ℕ) : (prefixList f k).length = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [prefixList, ih]

theorem prefixList_eq_iff (f g : ℕ → ℕ) (k : ℕ) :
    prefixList f k = prefixList g k ↔ ∀ j ≤ k, f j = g j := by
  induction k with
  | zero =>
    simp only [prefixList, List.cons.injEq, and_true, Nat.le_zero]
    exact ⟨fun h j hj => hj ▸ h, fun h => h 0 rfl⟩
  | succ k ih =>
    simp only [prefixList, List.cons.injEq, ih]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.eq_or_lt_of_le hj with rfl | hlt
      · exact h1
      · exact h2 j (Nat.lt_succ_iff.mp hlt)
    · intro h
      exact ⟨h (k + 1) le_rfl, fun j hj => h j (Nat.le_succ_of_le hj)⟩

/-- Branch associated to `f : ℕ → ℕ` in `ℕ`. -/
def branch (f : ℕ → ℕ) : Set ℕ :=
  Set.range (fun k : ℕ => encodeList (prefixList f k))

theorem branch_infinite (f : ℕ → ℕ) : (branch f).Infinite := by
  refine Set.infinite_range_of_injective fun k₁ k₂ h => ?_
  have hlen := congrArg List.length (encodeList_injective h)
  rw [prefixList_length, prefixList_length] at hlen
  omega

theorem branch_inter_finite {f g : ℕ → ℕ} (hfg : f ≠ g) :
    (branch f ∩ branch g).Finite := by
  have hex : ∃ m : ℕ, f m ≠ g m := by
    by_contra hall; push Not at hall; exact hfg (funext hall)
  obtain ⟨m, hm⟩ := hex
  refine ((Set.finite_Iio m).image (fun k => encodeList (prefixList f k))).subset ?_
  rintro n ⟨⟨k₁, rfl⟩, ⟨k₂, hk₂⟩⟩
  have hpeq : prefixList g k₂ = prefixList f k₁ := encodeList_injective hk₂
  have hkeq : k₂ = k₁ := by
    have hlen := congrArg List.length hpeq
    rw [prefixList_length, prefixList_length] at hlen
    omega
  subst hkeq
  have hlt : k₂ < m := by
    by_contra hge
    have hle : m ≤ k₂ := not_lt.mp hge
    exact hm (((prefixList_eq_iff g f k₂).mp hpeq m hle).symm)
  exact ⟨k₂, hlt, rfl⟩

/-- Helper: for any `l : List ℕ` and bound `M : ℕ`, there exists `a : ℕ` with
`encodeList (a :: l) > M`. -/
theorem exists_gt_encodeList_cons (l : List ℕ) (M : ℕ) :
    ∃ a : ℕ, M < encodeList (a :: l) := by
  have hinj : Function.Injective (fun a : ℕ => encodeList (a :: l)) := fun a₁ a₂ h => by
    have := encodeList_injective h
    exact (List.cons.inj this).1
  have hfin : { a : ℕ | encodeList (a :: l) ≤ M }.Finite :=
    (Set.finite_Iic M).preimage hinj.injOn
  obtain ⟨a, ha⟩ := hfin.exists_notMem
  exact ⟨a, not_le.mp ha⟩

/-- Theorem 1: The branch family `𝒜₀ := {branch f | f : ℕ → ℕ}` is an almost
disjoint family on `ℕ` that is **unbounded** in `(ℕ^ℕ, ≤*)`. -/
theorem exists_unbounded_AD :
    ∃ 𝒜₀ : Set (Set ℕ), IsAlmostDisjoint 𝒜₀ ∧ ¬ IsBoundedFamily 𝒜₀ := by
  let 𝒜₀ : Set (Set ℕ) := Set.range branch
  refine ⟨𝒜₀, ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨f, rfl⟩
    exact branch_infinite f
  · rintro _ ⟨f, rfl⟩ _ ⟨g, rfl⟩ hne
    exact branch_inter_finite (fun h => hne (h ▸ rfl))
  · rintro ⟨g, hg⟩
    -- Build f recursively via Nat.rec so k ↦ encodeList (prefixList f k) is strictly increasing and > g k
    let build : ℕ → List ℕ :=
      Nat.rec [(exists_gt_encodeList_cons [] (g 0)).choose]
        (fun k prev =>
          (exists_gt_encodeList_cons prev (max (g (k + 1)) (encodeList prev))).choose :: prev)
    have hbuild_ne : ∀ k, build k ≠ [] := fun k => by cases k <;> simp [build]
    let f : ℕ → ℕ := fun k => (build k).head (hbuild_ne k)
    have hbuild_eq : ∀ k, build k = prefixList f k := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        dsimp only [prefixList]
        rw [← ih]
        rfl
    let u : ℕ → ℕ := fun k => encodeList (prefixList f k)
    have hgt_g : ∀ k, g k < u k := by
      intro k
      dsimp only [u]
      rw [← hbuild_eq k]
      cases k with
      | zero => exact (exists_gt_encodeList_cons [] (g 0)).choose_spec
      | succ k =>
        exact lt_of_le_of_lt (le_max_left _ _)
          (exists_gt_encodeList_cons (build k) (max (g (k + 1)) (encodeList (build k)))).choose_spec
    have hstrict : StrictMono u := by
      refine strictMono_nat_of_lt_succ fun k => ?_
      dsimp only [u]
      rw [← hbuild_eq k, ← hbuild_eq (k + 1)]
      exact lt_of_le_of_lt (le_max_right _ _)
        (exists_gt_encodeList_cons (build k) (max (g (k + 1)) (encodeList (build k)))).choose_spec
    have hv_mem : ∀ k, ∃ j, u j = Nat.nth (· ∈ branch f) k := fun k =>
      Nat.nth_mem_of_infinite (branch_infinite f) k
    choose j hj_eq using hv_mem
    have hj_strict : StrictMono j := by
      intro m n hmn
      have hv_lt : Nat.nth (· ∈ branch f) m < Nat.nth (· ∈ branch f) n :=
        Nat.nth_strictMono (branch_infinite f) hmn
      rw [← hj_eq m, ← hj_eq n] at hv_lt
      exact hstrict.lt_iff_lt.mp hv_lt
    have hbd := hg (branch f) ⟨f, rfl⟩
    rw [Filter.eventually_atTop] at hbd
    obtain ⟨N, hN⟩ := hbd
    have h1 : Nat.nth (· ∈ branch f) N ≤ g N := hN N le_rfl
    have h2 : g N < Nat.nth (· ∈ branch f) N := by
      rw [← hj_eq N]
      exact lt_of_lt_of_le (hgt_g N) (hstrict.monotone (hj_strict.id_le N))
    exact not_lt_of_ge h1 h2

/-- Theorem 2 (ZFC): There exists an **unbounded** MAD family on `ℕ`. -/
theorem exists_unbounded_MAD :
    ∃ ℳ : Set (Set ℕ), IsMAD ℳ ∧ ¬ IsBoundedFamily ℳ := by
  obtain ⟨𝒜₀, hAD₀, hunb₀⟩ := exists_unbounded_AD
  let P : Set (Set (Set ℕ)) := { ℱ | 𝒜₀ ⊆ ℱ ∧ IsAlmostDisjoint ℱ }
  have hchain : ∀ c ⊆ P, IsChain (· ⊆ ·) c → c.Nonempty → ∃ ub ∈ P, ∀ s ∈ c, s ⊆ ub := by
    intro c hcP hc _
    refine ⟨𝒜₀ ∪ ⋃₀ c, ⟨subset_union_left, ?_, ?_⟩,
      fun s hs => (subset_sUnion_of_mem hs).trans subset_union_right⟩
    · intro A hA
      rcases hA with hA0 | ⟨ℱ, hℱc, hAℱ⟩
      · exact hAD₀.1 A hA0
      · exact (hcP hℱc).2.1 A hAℱ
    · intro A hA B hB hne
      rcases hA with hA0 | ⟨ℱ₁, hℱ₁c, hAℱ₁⟩
      · rcases hB with hB0 | ⟨ℱ₂, hℱ₂c, hBℱ₂⟩
        · exact hAD₀.2 A hA0 B hB0 hne
        · exact (hcP hℱ₂c).2.2 A ((hcP hℱ₂c).1 hA0) B hBℱ₂ hne
      · rcases hB with hB0 | ⟨ℱ₂, hℱ₂c, hBℱ₂⟩
        · exact (hcP hℱ₁c).2.2 A hAℱ₁ B ((hcP hℱ₁c).1 hB0) hne
        · rcases hc.total hℱ₁c hℱ₂c with h12 | h21
          · exact (hcP hℱ₂c).2.2 A (h12 hAℱ₁) B hBℱ₂ hne
          · exact (hcP hℱ₁c).2.2 A hAℱ₁ B (h21 hBℱ₂) hne
  obtain ⟨ℳ, hℳsub, hmax⟩ := zorn_subset_nonempty P hchain 𝒜₀ ⟨Subset.rfl, hAD₀⟩
  have hℳP : ℳ ∈ P := hmax.prop
  refine ⟨ℳ, ⟨hℳP.2, ?_⟩, fun ⟨g, hg⟩ => hunb₀ ⟨g, fun A hA => hg A (hℳP.1 hA)⟩⟩
  intro X hXinf
  by_contra hno
  push Not at hno
  have hX_not_mem : X ∉ ℳ := by
    intro hXℳ
    have hinf : (X ∩ X).Infinite := by simpa using hXinf
    exact hinf (hno X hXℳ)
  have hins : insert X ℳ ∈ P := by
    refine ⟨hℳP.1.trans (subset_insert X ℳ), ?_, ?_⟩
    · intro A hA
      rcases mem_insert_iff.mp hA with rfl | hAℳ
      · exact hXinf
      · exact hℳP.2.1 A hAℳ
    · intro A hA B hB hne
      rcases mem_insert_iff.mp hA with rfl | hAℳ
      · rcases mem_insert_iff.mp hB with rfl | hBℳ
        · exact (hne rfl).elim
        · exact hno B hBℳ
      · rcases mem_insert_iff.mp hB with rfl | hBℳ
        · rw [inter_comm]; exact hno A hAℳ
        · exact hℳP.2.2 A hAℳ B hBℳ hne
  have hEq : insert X ℳ = ℳ := (hmax.eq_of_subset hins (subset_insert X ℳ)).symm
  exact hX_not_mem (hEq ▸ mem_insert X ℳ)

/-- Theorem 3 (Repaired Chen–Wang Proposition 9.1):
If `ℳ` is an unbounded family on `ℕ` (such as the ZFC unbounded MAD family from
`exists_unbounded_MAD`) and `ℳ ⊆ ⋃ i : ℕ, ℳ_i`, then some `ℳ_i` is unbounded. -/
theorem prop_9_1_repaired (ℳ : Set (Set ℕ)) (hunb : ¬ IsBoundedFamily ℳ)
    (ℳ_i : ℕ → Set (Set ℕ)) (hcov : ℳ ⊆ ⋃ i, ℳ_i i) :
    ∃ i : ℕ, ¬ IsBoundedFamily (ℳ_i i) := by
  by_contra hall
  push Not at hall
  choose g hg using hall
  let G : ℕ → ℕ := fun k => (Finset.range (k + 1)).sup (fun i => g i k)
  refine hunb ⟨G, fun A hA => ?_⟩
  obtain ⟨i, hAi⟩ := mem_iUnion.mp (hcov hA)
  have hbd := hg i A hAi
  rw [Filter.eventually_atTop] at hbd ⊢
  obtain ⟨N, hN⟩ := hbd
  refine ⟨max N i, fun k hk => ?_⟩
  have h1 : Nat.nth (· ∈ A) k ≤ g i k := hN k (le_trans (le_max_left N i) hk)
  have h2 : g i k ≤ G k :=
    Finset.le_sup (f := fun j => g j k)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (le_trans (le_max_right N i) hk)))
  exact le_trans h1 h2

end Research.ChenWangUnboundedMAD
