import Mathlib.Topology.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Order.Filter.CountableInter
import Targets.Defs
import Defs.D_0001

/-!
# Heath (1966): Nagata Spaces = First-Countable Stratifiable Spaces

We formalize **Heath's (1966) characterization of Nagata spaces**:
1. `IsNagataSpace X`: a `T₁` space `X` admitting a `g`-function `g : ℕ → X → Set X` of open
   neighborhoods such that for every `x : X` and open `U ∋ x`, there exists `n : ℕ` with
   `∀ y, (g n y ∩ g n x).Nonempty → y ∈ U`.
2. `isNagataSpace_iff_firstCountable_and_isStratifiable` (**Heath 1966**):
   `IsNagataSpace X ↔ FirstCountableTopology X ∧ MSpace.IsStratifiable X`.
3. `isNagataSpace_of_metricSpace`: every metric space is a Nagata space.
4. `hasCPOuterBase_of_isNagataSpace`: every point of a Nagata space has a closure-preserving
   open outer base (`Defs.D_0001.HasCPOuterBase x`), showing that no Nagata space can witness
   `Specs.L_0020` / `Specs.L_0030` / `Specs.L_0031`.
5. `isNagataSpace_subtype` & `isNagataSpace_prod`: permanence of Nagata spaces under arbitrary
   subspaces and finite products.
-/

namespace Research.HeathNagata

open Set Topology Filter

/-- **Nagata space** (Heath 1966): a `T₁` space with open neighborhoods `g n x ∋ x` such that
for every open `U ∋ x`, there is `n` with `g n y ∩ g n x ≠ ∅ → y ∈ U`. -/
def IsNagataSpace (X : Type*) [TopologicalSpace X] : Prop :=
  T1Space X ∧
  ∃ g : ℕ → X → Set X,
    (∀ n x, IsOpen (g n x)) ∧
    (∀ n x, x ∈ g n x) ∧
    (∀ x U, IsOpen U → x ∈ U → ∃ n, ∀ y, (g n y ∩ g n x).Nonempty → y ∈ U)

/-- Every Nagata space has an antitone Nagata `g`-function. -/
theorem exists_antitone_nagata_g {X : Type*} [TopologicalSpace X] (hNag : IsNagataSpace X) :
    T1Space X ∧ ∃ g : ℕ → X → Set X,
      (∀ n x, IsOpen (g n x)) ∧
      (∀ n x, x ∈ g n x) ∧
      (∀ m n x, m ≤ n → g n x ⊆ g m x) ∧
      (∀ x U, IsOpen U → x ∈ U → ∃ n, ∀ y, (g n y ∩ g n x).Nonempty → y ∈ U) := by
  rcases hNag with ⟨hT1, g₀, hopen, hmem, hnag⟩
  let g : ℕ → X → Set X := fun n x => Nat.rec (g₀ 0 x) (fun k ih => ih ∩ g₀ (k + 1) x) n
  have hg_open : ∀ n x, IsOpen (g n x) := by
    intro n x; induction n with
    | zero => exact hopen 0 x
    | succ k ih => exact ih.inter (hopen (k + 1) x)
  have hg_mem : ∀ n x, x ∈ g n x := by
    intro n x; induction n with
    | zero => exact hmem 0 x
    | succ k ih => exact ⟨ih, hmem (k + 1) x⟩
  have hg_le : ∀ n x, g n x ⊆ g₀ n x := fun n x => by
    cases n with
    | zero => exact Subset.rfl
    | succ _ => exact inter_subset_right
  have hg_anti : ∀ m n x, m ≤ n → g n x ⊆ g m x := by
    intro m n x hmn; induction hmn with
    | refl => exact Subset.rfl
    | step _ ih => exact inter_subset_left.trans ih
  refine ⟨hT1, g, hg_open, hg_mem, hg_anti, ?_⟩
  intro x U hUo hxU
  obtain ⟨n, hn⟩ := hnag x U hUo hxU
  exact ⟨n, fun y ⟨z, hzy, hzx⟩ => hn y ⟨z, hg_le n y hzy, hg_le n x hzx⟩⟩

/-- Every first-countable space has a decreasing countable open local base at every point. -/
private theorem exists_decreasing_open_base {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] (x : X) :
    ∃ b : ℕ → Set X,
      (∀ n, IsOpen (b n)) ∧
      (∀ n, x ∈ b n) ∧
      (∀ m n, m ≤ n → b n ⊆ b m) ∧
      (∀ U, IsOpen U → x ∈ U → ∃ n, b n ⊆ U) := by
  obtain ⟨s, hs_basis, hs_anti⟩ := (nhds x).exists_antitone_basis
  let b : ℕ → Set X := fun n => interior (s n)
  refine ⟨b, fun _ => isOpen_interior, ?_, ?_, ?_⟩
  · intro n
    have hmem : s n ∈ 𝓝 x := hs_basis.mem_of_mem (by simp)
    exact mem_interior_iff_mem_nhds.mpr hmem
  · intro m n hmn
    exact interior_mono (hs_anti hmn)
  · intro U hUo hxU
    have hU_nhds : U ∈ 𝓝 x := hUo.mem_nhds hxU
    obtain ⟨n, -, hsn⟩ := hs_basis.mem_iff.mp hU_nhds
    exact ⟨n, interior_subset.trans hsn⟩

/-- Every stratifiable space has an antitone stratification. -/
private theorem exists_antitone_stratification {X : Type*} [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X) :
    T1Space X ∧ ∃ G : ℕ → Set X → Set X,
      MSpace.IsStratification G ∧ ∀ m n C, m ≤ n → G n C ⊆ G m C := by
  rcases hStrat with ⟨hT1, G₀, hopen, hsub, hinter, hmono⟩
  let G : ℕ → Set X → Set X := fun n C => Nat.rec (G₀ 0 C) (fun k ih => ih ∩ G₀ (k + 1) C) n
  have hG_open : ∀ n C, IsClosed C → IsOpen (G n C) := by
    intro n C hC; induction n with
    | zero => exact hopen 0 C hC
    | succ k ih => exact ih.inter (hopen (k + 1) C hC)
  have hG_sub : ∀ n C, IsClosed C → C ⊆ G n C := by
    intro n C hC; induction n with
    | zero => exact hsub 0 C hC
    | succ k ih => exact subset_inter ih (hsub (k + 1) C hC)
  have hG_le_G0 : ∀ n C, G n C ⊆ G₀ n C := fun n C => by
    cases n with
    | zero => exact Subset.rfl
    | succ _ => exact inter_subset_right
  have hG_anti : ∀ m n C, m ≤ n → G n C ⊆ G m C := by
    intro m n C hmn; induction hmn with
    | refl => exact Subset.rfl
    | step _ ih => exact inter_subset_left.trans ih
  refine ⟨hT1, G, ⟨hG_open, hG_sub, ?_, ?_⟩, hG_anti⟩
  · intro C hC
    apply Subset.antisymm
    · intro x hx
      rw [← hinter C hC, mem_iInter]
      intro n
      exact closure_mono (hG_le_G0 n C) (mem_iInter.mp hx n)
    · intro x hxC
      exact mem_iInter.mpr fun n => subset_closure (hG_sub n C hC hxC)
  · intro n C₁ C₂ hC₁ hC₂ hC₁₂
    induction n with
    | zero => exact hmono 0 C₁ C₂ hC₁ hC₂ hC₁₂
    | succ k ih => exact inter_subset_inter ih (hmono (k + 1) C₁ C₂ hC₁ hC₂ hC₁₂)

/-- **Heath (1966), forward direction**:
Every first-countable stratifiable space is a Nagata space. -/
theorem isNagataSpace_of_firstCountable_isStratifiable {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] (hStrat : MSpace.IsStratifiable X) :
    IsNagataSpace X := by
  obtain ⟨hT1, G, ⟨hGopen, hGsub, hGinter, hGmono⟩, hGanti⟩ :=
    exists_antitone_stratification hStrat
  have : T1Space X := hT1
  choose b hb_open hb_mem hb_anti hb_base using fun x : X => exists_decreasing_open_base x
  let g : ℕ → X → Set X := fun n x => G n {x} ∩ b x n
  refine ⟨hT1, g, ?_, ?_, ?_⟩
  · intro n x
    exact (hGopen n {x} isClosed_singleton).inter (hb_open x n)
  · intro n x
    exact ⟨hGsub n {x} isClosed_singleton (mem_singleton x), hb_mem x n⟩
  · intro x U hUo hxU
    obtain ⟨m, hbmU⟩ := hb_base x U hUo hxU
    have hx_not_compl : x ∉ (b x m)ᶜ := fun h => h (hb_mem x m)
    rw [← hGinter (b x m)ᶜ (hb_open x m).isClosed_compl, mem_iInter] at hx_not_compl
    push Not at hx_not_compl
    obtain ⟨n, hn⟩ := hx_not_compl
    let O : Set X := (closure (G n (b x m)ᶜ))ᶜ
    have hOo : IsOpen O := isClosed_closure.isOpen_compl
    have hxO : x ∈ O := hn
    obtain ⟨k, hbkO⟩ := hb_base x O hOo hxO
    let N := max n k
    refine ⟨N, fun y hne => ?_⟩
    obtain ⟨z, ⟨hzGy, _⟩, ⟨_, hzbx⟩⟩ := hne
    have hzO : z ∈ O := hbkO (hb_anti x k N (le_max_right n k) hzbx)
    have hzy : y ∈ b x m := by
      by_contra hyNot
      have hsub : ({y} : Set X) ⊆ (b x m)ᶜ := Set.singleton_subset_iff.mpr hyNot
      have hzGn : z ∈ G n {y} := hGanti n N {y} (le_max_left n k) hzGy
      have hzGm : z ∈ G n (b x m)ᶜ :=
        hGmono n {y} (b x m)ᶜ isClosed_singleton (hb_open x m).isClosed_compl hsub hzGn
      exact hzO (subset_closure hzGm)
    exact hbmU hzy

/-- Every Nagata space is first-countable. -/
theorem firstCountable_of_isNagataSpace {X : Type*} [TopologicalSpace X]
    (hNag : IsNagataSpace X) : FirstCountableTopology X := by
  obtain ⟨_, g, hg_open, hg_mem, hg_anti, hg_nag⟩ := exists_antitone_nagata_g hNag
  refine ⟨fun x => ?_⟩
  have hbasis : (𝓝 x).HasBasis (fun _ : ℕ => True) (fun n => g n x) := by
    refine Filter.hasBasis_iff.mpr fun U => ?_
    constructor
    · intro hU
      obtain ⟨V, hVU, hVo, hxV⟩ := mem_nhds_iff.mp hU
      obtain ⟨n, hn⟩ := hg_nag x V hVo hxV
      exact ⟨n, trivial, fun y hy => hVU (hn y ⟨y, hg_mem n y, hy⟩)⟩
    · rintro ⟨n, -, hn⟩
      exact Filter.mem_of_superset ((hg_open n x).mem_nhds (hg_mem n x)) hn
  exact hbasis.isCountablyGenerated

/-- Every Nagata space is stratifiable. -/
theorem isStratifiable_of_isNagataSpace {X : Type*} [TopologicalSpace X]
    (hNag : IsNagataSpace X) : MSpace.IsStratifiable X := by
  rcases hNag with ⟨hT1, g, hg_open, hg_mem, hg_nag⟩
  let G : ℕ → Set X → Set X := fun n F => ⋃ y ∈ F, g n y
  refine ⟨hT1, G, ?_, ?_, ?_, ?_⟩
  · intro n F _
    exact isOpen_biUnion fun y _ => hg_open n y
  · intro n F _ y hyF
    exact mem_biUnion hyF (hg_mem n y)
  · intro F hF
    apply Subset.antisymm
    · intro x hx
      by_contra hxF
      obtain ⟨n, hn⟩ := hg_nag x Fᶜ hF.isOpen_compl hxF
      obtain ⟨z, hzgx, hzGF⟩ := mem_closure_iff.mp (mem_iInter.mp hx n) (g n x) (hg_open n x) (hg_mem n x)
      obtain ⟨y, hyF, hzgy⟩ := mem_iUnion₂.mp hzGF
      exact (hn y ⟨z, hzgy, hzgx⟩) hyF
    · intro x hxF
      exact mem_iInter.mpr fun n => subset_closure (mem_biUnion hxF (hg_mem n x))
  · intro n F₁ F₂ _ _ hF₁₂
    exact biUnion_subset_biUnion_left hF₁₂

/-- **Heath (1966), Theorem 1**:
A topological space is a Nagata space if and only if it is first-countable and stratifiable. -/
theorem isNagataSpace_iff_firstCountable_and_isStratifiable {X : Type*} [TopologicalSpace X] :
    IsNagataSpace X ↔ FirstCountableTopology X ∧ MSpace.IsStratifiable X :=
  ⟨fun h => ⟨firstCountable_of_isNagataSpace h, isStratifiable_of_isNagataSpace h⟩,
   fun ⟨hFC, hStrat⟩ =>
     @isNagataSpace_of_firstCountable_isStratifiable X _ hFC hStrat⟩

/-- Every metric space is a Nagata space. -/
theorem isNagataSpace_of_metricSpace {X : Type*} [MetricSpace X] : IsNagataSpace X := by
  refine ⟨inferInstance, fun n x => Metric.ball x (1 / (2 * ((n : ℝ) + 1))),
    fun _ _ => Metric.isOpen_ball, ?_, ?_⟩
  · intro n x
    rw [Metric.mem_ball, dist_self]
    positivity
  · intro x U hUo hxU
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUo x hxU
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
    refine ⟨n, fun y ⟨z, hzy, hzx⟩ => ?_⟩
    rw [Metric.mem_ball] at hzy hzx
    have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hdist : dist y x < ε := by
      have h1 : dist y x ≤ dist y z + dist z x := dist_triangle y z x
      have h2 : dist y z < 1 / (2 * ((n : ℝ) + 1)) := by rwa [dist_comm]
      have h3 : 1 / (2 * ((n : ℝ) + 1)) + 1 / (2 * ((n : ℝ) + 1)) = 1 / ((n : ℝ) + 1) := by
        field_simp; ring
      have h4 : 1 / ((n : ℝ) + 1) < ε := by
        rw [div_lt_iff₀ hnpos]
        have h1ε : 1 < ε * (n : ℝ) := by
          have := (div_lt_iff₀ hε).mp hn
          linarith
        nlinarith
      linarith
    exact hball (Metric.mem_ball.mpr hdist)

/-- Every point of a Nagata space has a closure-preserving open outer base (`HasCPOuterBase`),
showing no Nagata space can witness `Specs.L_0020` / `Specs.L_0030` / `Specs.L_0031`. -/
theorem hasCPOuterBase_of_isNagataSpace {X : Type*} [TopologicalSpace X]
    (hNag : IsNagataSpace X) (x : X) : Defs.D_0001.HasCPOuterBase x := by
  obtain ⟨hT1, g, hg_open, hg_mem, hg_anti, hg_nag⟩ := exists_antitone_nagata_g hNag
  refine ⟨Set.range (fun n => g n x), ?_, ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact ⟨hg_open n x, hg_mem n x⟩
  · intro U hUo hxU
    obtain ⟨n, hn⟩ := hg_nag x U hUo hxU
    exact ⟨g n x, ⟨n, rfl⟩, fun y hy => hn y ⟨y, hg_mem n y, hy⟩⟩
  · intro 𝓖 h𝓖
    apply Subset.antisymm
    · intro z hz
      by_cases hGne : 𝓖.Nonempty
      · let S : Set ℕ := { n | g n x ∈ 𝓖 }
        have hSne : S.Nonempty := by
          obtain ⟨B, hBG⟩ := hGne
          obtain ⟨n, rfl⟩ := h𝓖 hBG
          exact ⟨n, hBG⟩
        classical
        let n₀ := Nat.find hSne
        have hn₀ : g n₀ x ∈ 𝓖 := Nat.find_spec hSne
        have hsub : ⋃₀ 𝓖 ⊆ g n₀ x := by
          rintro y ⟨B, hBG, hyB⟩
          obtain ⟨n, rfl⟩ := h𝓖 hBG
          have hle : n₀ ≤ n := Nat.find_min' hSne hBG
          exact hg_anti n₀ n x hle hyB
        exact ⟨closure (g n₀ x), ⟨g n₀ x, hn₀, rfl⟩, closure_mono hsub hz⟩
      · rw [Set.not_nonempty_iff_eq_empty.mp hGne, sUnion_empty, closure_empty] at hz
        exact hz.elim
    · rintro z ⟨_, ⟨B, hBG, rfl⟩, hzB⟩
      exact closure_mono (Set.subset_sUnion_of_mem hBG) hzB

/-- Nagata spaces are hereditary (every subspace of a Nagata space is a Nagata space). -/
theorem isNagataSpace_subtype {X : Type*} [TopologicalSpace X] (S : Set X)
    (hNag : IsNagataSpace X) : IsNagataSpace S := by
  rcases hNag with ⟨hT1, g, hg_open, hg_mem, hg_nag⟩
  have : T1Space X := hT1
  refine ⟨inferInstance, fun n x => (Subtype.val : S → X) ⁻¹' g n x.1,
    fun n x => (hg_open n x.1).preimage continuous_subtype_val,
    fun n x => hg_mem n x.1, ?_⟩
  intro x U hUo hxU
  rw [isOpen_induced_iff] at hUo
  obtain ⟨V, hVo, rfl⟩ := hUo
  obtain ⟨n, hn⟩ := hg_nag x.1 V hVo hxU
  exact ⟨n, fun y ⟨z, hzy, hzx⟩ => hn y.1 ⟨z.1, hzy, hzx⟩⟩

/-- Finite products of Nagata spaces are Nagata spaces. -/
theorem isNagataSpace_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (hX : IsNagataSpace X) (hY : IsNagataSpace Y) : IsNagataSpace (X × Y) := by
  obtain ⟨hT1X, gX, hgXo, hgXm, hgXa, hgXn⟩ := exists_antitone_nagata_g hX
  obtain ⟨hT1Y, gY, hgYo, hgYm, hgYa, hgYn⟩ := exists_antitone_nagata_g hY
  have : T1Space X := hT1X
  have : T1Space Y := hT1Y
  refine ⟨inferInstance, fun n p => gX n p.1 ×ˢ gY n p.2,
    fun n p => (hgXo n p.1).prod (hgYo n p.2),
    fun n p => ⟨hgXm n p.1, hgYm n p.2⟩, ?_⟩
  intro p U hUo hpU
  obtain ⟨A, B, hAo, hBo, hpA, hpB, hABU⟩ := isOpen_prod_iff.mp hUo p.1 p.2 hpU
  obtain ⟨n₁, hn₁⟩ := hgXn p.1 A hAo hpA
  obtain ⟨n₂, hn₂⟩ := hgYn p.2 B hBo hpB
  let n := max n₁ n₂
  refine ⟨n, fun q ⟨z, ⟨hzq1, hzq2⟩, ⟨hzp1, hzp2⟩⟩ => ?_⟩
  have h1 : q.1 ∈ A :=
    hn₁ q.1 ⟨z.1, hgXa n₁ n q.1 (le_max_left _ _) hzq1, hgXa n₁ n p.1 (le_max_left _ _) hzp1⟩
  have h2 : q.2 ∈ B :=
    hn₂ q.2 ⟨z.2, hgYa n₂ n q.2 (le_max_right _ _) hzq2, hgYa n₂ n p.2 (le_max_right _ _) hzp2⟩
  exact hABU ⟨h1, h2⟩

end Research.HeathNagata
