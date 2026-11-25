import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Data.Nat.Pairing
import Specs.L_0011

namespace Proofs.L_0011

open MSpace Set Topology

section Helpers

variable {X : Type} [TopologicalSpace X]

/-- `n`-step iteration of a neighbornet `g : X → Set X` applied to a set `S`. -/
private def iterNet (g : X → Set X) : ℕ → Set X → Set X
  | 0, S => S
  | k + 1, S => ⋃ y ∈ iterNet g k S, g y

private lemma mem_iterNet_succ {g : X → Set X} {k : ℕ} {S : Set X} {x : X} :
    x ∈ iterNet g (k + 1) S ↔ ∃ y ∈ iterNet g k S, x ∈ g y := by
  simp only [iterNet, mem_iUnion, exists_prop]

private lemma iterNet_mono_set {g : X → Set X} {k : ℕ} {S T : Set X} (hST : S ⊆ T) :
    iterNet g k S ⊆ iterNet g k T := by
  induction k with
  | zero => exact hST
  | succ k ih =>
    intro x hx
    simp only [iterNet, mem_iUnion] at hx ⊢
    obtain ⟨y, hy, hxy⟩ := hx
    exact ⟨y, ih hy, hxy⟩

private lemma iterNet_mono_fun {g₁ g₂ : X → Set X} (hg : ∀ y, g₁ y ⊆ g₂ y) {k : ℕ} {S : Set X} :
    iterNet g₁ k S ⊆ iterNet g₂ k S := by
  induction k with
  | zero => exact Subset.rfl
  | succ k ih =>
    intro x hx
    simp only [iterNet, mem_iUnion] at hx ⊢
    obtain ⟨y, hy, hxy⟩ := hx
    exact ⟨y, ih hy, hg y hxy⟩

/-- Monotone decreasing stratification helper structure. -/
private structure DecStrat (X : Type) [TopologicalSpace X] where
  G : ℕ → Set X → Set X
  isOpen : ∀ n H, IsClosed H → IsOpen (G n H)
  subset : ∀ n H, IsClosed H → H ⊆ G n H
  iInter_closure : ∀ H, IsClosed H → ⋂ n, closure (G n H) = H
  mono : ∀ n H K, IsClosed H → IsClosed K → H ⊆ K → G n H ⊆ G n K
  anti : ∀ n m H, n ≤ m → G m H ⊆ G n H

private def mkDecStrat (G : ℕ → Set X → Set X) (hG : IsStratification G) : DecStrat X := by
  obtain ⟨hGopen, hGsub, hGint, hGmono⟩ := hG
  let G' : ℕ → Set X → Set X := fun n H => ⋂ k ∈ Finset.range (n + 1), G k H
  refine ⟨G', ?_, ?_, ?_, ?_, ?_⟩
  · intro n H hH
    exact isOpen_biInter_finset fun k _ => hGopen k H hH
  · intro n H hH x hx
    simp only [G', mem_iInter]
    intro k _
    exact hGsub k H hH hx
  · intro H hH
    apply Subset.antisymm
    · calc ⋂ n, closure (G' n H)
          ⊆ ⋂ n, closure (G n H) := iInter_mono fun n => closure_mono
              (biInter_subset_of_mem (Finset.mem_range.2 (Nat.lt_succ_self n)))
        _ = H := hGint H hH
    · intro x hx
      simp only [mem_iInter]
      intro n
      refine subset_closure ?_
      simp only [G', mem_iInter]
      intro k _
      exact hGsub k H hH hx
  · intro n H K hH hK hHK x hx
    simp only [G', mem_iInter] at hx ⊢
    intro k hk
    exact hGmono k H K hH hK hHK (hx k hk)
  · intro n m H hnm x hx
    simp only [G', mem_iInter, Finset.mem_range] at hx ⊢
    intro k hk
    exact hx k (by omega)

/-- `k`-step convergence bound for `g n y = S.G n {y}`. -/
private lemma exists_notMem_closure_iterNet [T1Space X] (S : DecStrat X) :
    ∀ (k : ℕ) (H : Set X), IsClosed H → ∀ x, x ∉ H →
      ∃ N : ℕ, x ∉ closure (iterNet (fun y => S.G N {y}) k H) := by
  intro k
  induction k with
  | zero =>
    intro H hH x hx
    exact ⟨0, by simpa [iterNet, hH.closure_eq] using hx⟩
  | succ k ih =>
    intro H hH x hx
    obtain ⟨m, hm⟩ := ih H hH x hx
    let K : Set X := closure (iterNet (fun y => S.G m {y}) k H)
    have hK_closed : IsClosed K := isClosed_closure
    have hxK : x ∉ ⋂ n, closure (S.G n K) := by
      rw [S.iInter_closure K hK_closed]
      exact hm
    rw [mem_iInter] at hxK
    obtain ⟨n0, hn0⟩ := not_forall.1 hxK
    let N := max m n0
    refine ⟨N, fun hxcl => hn0 ?_⟩
    have hsub1 : iterNet (fun y => S.G N {y}) k H ⊆ K :=
      (iterNet_mono_fun (fun y => S.anti m N {y} (le_max_left m n0))).trans subset_closure
    have hsub2 : iterNet (fun y => S.G N {y}) (k + 1) H ⊆ S.G n0 K := by
      intro z hz
      simp only [iterNet, mem_iUnion] at hz
      obtain ⟨y, hy, hzy⟩ := hz
      have hyK : ({y} : Set X) ⊆ K := singleton_subset_iff.2 (hsub1 hy)
      exact S.anti n0 N K (le_max_right m n0)
        (S.mono N {y} K isClosed_singleton hK_closed hyK hzy)
    exact closure_mono hsub2 hxcl

/-- Every stratifiable space has a σ-discrete closed network (Heath 1969). -/
private lemma exists_sigmaDiscrete_closed_network [T1Space X] (S : DecStrat X) :
    ∃ N : ℕ → X → Set X,
      (∀ r y, IsClosed (N r y)) ∧
      (∀ r, LocallyFinite (N r)) ∧
      (∀ r y₁ y₂, y₁ ≠ y₂ → Disjoint (N r y₁) (N r y₂)) ∧
      (∀ x U, IsOpen U → x ∈ U → ∃ r y, x ∈ N r y ∧ N r y ⊆ U) := by
  let g : ℕ → X → Set X := fun n y => S.G n {y}
  have hg_open : ∀ n y, IsOpen (g n y) := fun n y => S.isOpen n {y} isClosed_singleton
  have hg_self : ∀ n y, y ∈ g n y := fun n y => S.subset n {y} isClosed_singleton (mem_singleton y)
  have hg_anti : ∀ n m y, n ≤ m → g m y ⊆ g n y := fun n m y hnm => S.anti n m {y} hnm
  -- Dual closed sets F j U = (S.G j Uᶜ)ᶜ
  let F : ℕ → Set X → Set X := fun j U => (S.G j Uᶜ)ᶜ
  have hF_closed : ∀ j U, IsOpen U → IsClosed (F j U) := fun j U hU =>
    (S.isOpen j Uᶜ hU.isClosed_compl).isClosed_compl
  have hF_sub : ∀ j U, IsOpen U → F j U ⊆ U := by
    intro j U hU z hz
    by_contra hzu
    exact hz (S.subset j Uᶜ hU.isClosed_compl hzu)
  have hF_mono : ∀ j U V, IsOpen U → IsOpen V → U ⊆ V → F j U ⊆ F j V :=
    fun j U V hU hV hUV =>
      compl_subset_compl.2
        (S.mono j Vᶜ Uᶜ hV.isClosed_compl hU.isClosed_compl (compl_subset_compl.2 hUV))
  have hF_cov : ∀ U, IsOpen U → ∀ x ∈ U, ∃ j, x ∈ F j U := by
    intro U hU x hx
    have hx' : x ∉ ⋂ j, closure (S.G j Uᶜ) := by
      rw [S.iInter_closure Uᶜ hU.isClosed_compl]
      exact fun h => h hx
    rw [mem_iInter] at hx'
    obtain ⟨j, hj⟩ := not_forall.1 hx'
    exact ⟨j, fun h => hj (subset_closure h)⟩
  -- Well-order X
  obtain ⟨lin, wf⟩ := exists_wellFoundedLT X
  let _ : LinearOrder X := lin
  have _ : WellFoundedLT X := wf
  -- For each m, construct a σ-discrete closed refinement C m j y of {g m y}
  let Wlt (m : ℕ) (y : X) : Set X := ⋃ (z : X) (_ : z < y), g m z
  have hWlt_open (m : ℕ) (y : X) : IsOpen (Wlt m y) :=
    isOpen_iUnion fun z => isOpen_iUnion fun _ => hg_open m z
  let C (m j : ℕ) (y : X) : Set X := F j (g m y) \ Wlt m y
  have hC_closed (m j : ℕ) (y : X) : IsClosed (C m j y) :=
    (hF_closed j (g m y) (hg_open m y)).sdiff (hWlt_open m y)
  have hC_sub (m j : ℕ) (y : X) : C m j y ⊆ g m y :=
    diff_subset.trans (hF_sub j (g m y) (hg_open m y))
  have hC_disj (m j : ℕ) {y₁ y₂ : X} (hne : y₁ ≠ y₂) : Disjoint (C m j y₁) (C m j y₂) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hx2.2 (mem_iUnion₂.2 ⟨y₁, hlt, hC_sub m j y₁ hx1⟩)
    · exact hx1.2 (mem_iUnion₂.2 ⟨y₂, hgt, hC_sub m j y₂ hx2⟩)
  have hC_cov (m : ℕ) (x : X) : ∃ j y, x ∈ C m j y := by
    have hne : {y : X | x ∈ g m y}.Nonempty := ⟨x, hg_self m x⟩
    let y0 := wellFounded_lt.min {y : X | x ∈ g m y} hne
    have hy0 : x ∈ g m y0 := wellFounded_lt.min_mem {y : X | x ∈ g m y} hne
    obtain ⟨j, hj⟩ := hF_cov (g m y0) (hg_open m y0) x hy0
    refine ⟨j, y0, hj, ?_⟩
    simp only [Wlt, mem_iUnion, not_exists]
    exact fun z hlt hxz => wellFounded_lt.not_lt_min {y : X | x ∈ g m y} hxz hlt
  have hC_lf (m j : ℕ) : LocallyFinite (C m j) := by
    intro x
    have hne : {y : X | x ∈ g m y}.Nonempty := ⟨x, hg_self m x⟩
    let y0 := wellFounded_lt.min {y : X | x ∈ g m y} hne
    have hy0 : x ∈ g m y0 := wellFounded_lt.min_mem {y : X | x ∈ g m y} hne
    let O : Set X := g m y0 \ F j (Wlt m y0)
    have hO_open : IsOpen O := (hg_open m y0).sdiff (hF_closed j (Wlt m y0) (hWlt_open m y0))
    have hxO : x ∈ O := by
      refine ⟨hy0, fun h => ?_⟩
      have hW := hF_sub j (Wlt m y0) (hWlt_open m y0) h
      simp only [Wlt, mem_iUnion] at hW
      obtain ⟨z, hlt, hxz⟩ := hW
      exact wellFounded_lt.not_lt_min {y : X | x ∈ g m y} hxz hlt
    refine ⟨O, hO_open.mem_nhds hxO, (Set.finite_singleton y0).subset ?_⟩
    intro y hy
    rw [mem_singleton_iff]
    by_contra hne'
    obtain ⟨w, hwC, hwO⟩ := hy
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · have hsub : g m y ⊆ Wlt m y0 := fun z hz => mem_iUnion₂.2 ⟨y, hlt, hz⟩
      exact hwO.2 (hF_mono j (g m y) (Wlt m y0) (hg_open m y) (hWlt_open m y0) hsub hwC.1)
    · exact hwC.2 (mem_iUnion₂.2 ⟨y0, hgt, hwO.1⟩)
  -- Define Heath's network sets N3 n m j y = closure {z ∈ C m j y | y ∈ g n z}
  let E (n m j : ℕ) (y : X) : Set X := {z ∈ C m j y | y ∈ g n z}
  let N3 (n m j : ℕ) (y : X) : Set X := closure (E n m j y)
  have hN3_sub_C (n m j : ℕ) (y : X) : N3 n m j y ⊆ C m j y :=
    closure_minimal (fun _ hz => hz.1) (hC_closed m j y)
  -- Encode (n, m, j) ∈ ℕ³ into ℕ via Nat.unpair
  let N (r : ℕ) (y : X) : Set X :=
    let p := Nat.unpair r
    let q := Nat.unpair p.2
    N3 p.1 q.1 q.2 y
  refine ⟨N, ?_, ?_, ?_, ?_⟩
  · intro r y
    exact isClosed_closure
  · intro r
    let p := Nat.unpair r
    let q := Nat.unpair p.2
    exact (hC_lf q.1 q.2).subset fun y => hN3_sub_C p.1 q.1 q.2 y
  · intro r y₁ y₂ hne
    let p := Nat.unpair r
    let q := Nat.unpair p.2
    exact (hC_disj q.1 q.2 hne).mono (hN3_sub_C p.1 q.1 q.2 y₁) (hN3_sub_C p.1 q.1 q.2 y₂)
  · intro x U hU hxU
    let H : Set X := Uᶜ
    have hH_closed : IsClosed H := hU.isClosed_compl
    have hxH : x ∉ H := fun h => h hxU
    obtain ⟨n, hn⟩ := exists_notMem_closure_iterNet S 3 H hH_closed x hxH
    have hn' : x ∉ iterNet (g n) 3 H := fun h => hn (subset_closure h)
    -- Pick m ≥ n so that x ∈ g m y → y ∈ g n x
    have hxgn : x ∉ (g n x)ᶜ := fun h => h (hg_self n x)
    obtain ⟨m0, hm0⟩ := exists_notMem_closure_iterNet S 1 (g n x)ᶜ (hg_open n x).isClosed_compl x hxgn
    let m := max n m0
    obtain ⟨j, y, hxyC⟩ := hC_cov m x
    have hxy_gm : x ∈ g m y := hC_sub m j y hxyC
    have hy_gnx : y ∈ g n x := by
      by_contra hyn
      have h1 : x ∈ iterNet (g m0) 1 (g n x)ᶜ := by
        simp only [iterNet, mem_iUnion]
        exact ⟨y, hyn, hg_anti m0 m y (le_max_right n m0) hxy_gm⟩
      exact hm0 (subset_closure h1)
    let r := Nat.pair n (Nat.pair m j)
    refine ⟨r, y, ?_, ?_⟩
    · have hr : N r y = N3 n m j y := by
        simp only [N, r, Nat.unpair_pair]
      rw [hr]
      exact subset_closure ⟨hxyC, hy_gnx⟩
    · have hr : N r y = N3 n m j y := by
        simp only [N, r, Nat.unpair_pair]
      rw [hr]
      intro w hw
      by_contra hwu
      have hwH : w ∈ H := hwu
      have hne : (E n m j y ∩ g n w).Nonempty := by
        rw [mem_closure_iff] at hw
        have h := hw (g n w) (hg_open n w) (hg_self n w)
        exact h.imp fun z hz => ⟨hz.2, hz.1⟩
      obtain ⟨z, ⟨_, hyz⟩, hzw⟩ := hne
      have hz1 : z ∈ iterNet (g n) 1 H := mem_iterNet_succ.2 ⟨w, hwH, hzw⟩
      have hy2 : y ∈ iterNet (g n) 2 H := mem_iterNet_succ.2 ⟨z, hz1, hyz⟩
      have hx3 : x ∈ iterNet (g n) 3 H :=
        mem_iterNet_succ.2 ⟨y, hy2, hg_anti n m y (le_max_left n m0) hxy_gm⟩
      exact hn' hx3

/-- Given a σ-discrete closed network and a decreasing stratification,
    for every open neighbornet `U` there exists a transitive open neighbornet `V`
    such that `∀ z, V z ⊆ iterNet U 3 {z}`. -/
private lemma exists_transitive_neighbornet_cubed [T1Space X] (S : DecStrat X)
    (N : ℕ → X → Set X)
    (hN_closed : ∀ r y, IsClosed (N r y))
    (hN_lf : ∀ r, LocallyFinite (N r))
    (hN_disj : ∀ r y₁ y₂, y₁ ≠ y₂ → Disjoint (N r y₁) (N r y₂))
    (hN_net : ∀ x U, IsOpen U → x ∈ U → ∃ r y, x ∈ N r y ∧ N r y ⊆ U)
    (U : X → Set X) (hU_open : ∀ x, IsOpen (U x)) (hU_self : ∀ x, x ∈ U x) :
    ∃ V : X → Set X,
      (∀ x, IsOpen (V x)) ∧
      (∀ x, x ∈ V x) ∧
      (∀ x y, y ∈ V x → V y ⊆ V x) ∧
      (∀ x, V x ⊆ iterNet U 3 {x}) := by
  -- Step 1: Pairwise disjoint open expansion W r y of N r y via monotone normality
  let K (r : ℕ) (y : X) : Set X := ⋃ (y' : X) (_ : y' ≠ y), N r y'
  have hK_closed (r : ℕ) (y : X) : IsClosed (K r y) := by
    have hEq : K r y = ⋃ y' : {y' : X // y' ≠ y}, N r y'.1 := by
      ext z; simp [K]
    rw [hEq]
    exact ((hN_lf r).comp_injective Subtype.val_injective).isClosed_iUnion fun y' => hN_closed r y'.1
  let W (r : ℕ) (y : X) : Set X := ⋃ k : ℕ, (S.G k (N r y) \ closure (S.G k (K r y)))
  have hW_open (r : ℕ) (y : X) : IsOpen (W r y) :=
    isOpen_iUnion fun k => (S.isOpen k (N r y) (hN_closed r y)).sdiff isClosed_closure
  have hN_sub_W (r : ℕ) (y : X) : N r y ⊆ W r y := by
    intro z hz
    have hzK : z ∉ K r y := by
      simp only [K, mem_iUnion]
      rintro ⟨y', hne, hzy'⟩
      exact Set.disjoint_left.1 (hN_disj r y y' hne.symm) hz hzy'
    have hz' : z ∉ ⋂ k, closure (S.G k (K r y)) := by
      rw [S.iInter_closure (K r y) (hK_closed r y)]
      exact hzK
    rw [mem_iInter] at hz'
    obtain ⟨k, hk⟩ := not_forall.1 hz'
    exact mem_iUnion.2 ⟨k, S.subset k (N r y) (hN_closed r y) hz, hk⟩
  have hW_disj (r : ℕ) {y₁ y₂ : X} (hne : y₁ ≠ y₂) : Disjoint (W r y₁) (W r y₂) := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    obtain ⟨k1, hk1, hnk1⟩ := mem_iUnion.1 hz1
    obtain ⟨k2, hk2, hnk2⟩ := mem_iUnion.1 hz2
    rcases le_total k1 k2 with h12 | h21
    · have hsub : N r y₂ ⊆ K r y₁ := fun w hw => mem_iUnion₂.2 ⟨y₂, hne.symm, hw⟩
      exact hnk1 (subset_closure
        (S.mono k1 (N r y₂) (K r y₁) (hN_closed r y₂) (hK_closed r y₁) hsub
          (S.anti k1 k2 (N r y₂) h12 hk2)))
    · have hsub : N r y₁ ⊆ K r y₂ := fun w hw => mem_iUnion₂.2 ⟨y₁, hne, hw⟩
      exact hnk2 (subset_closure
        (S.mono k2 (N r y₁) (K r y₂) (hN_closed r y₁) (hK_closed r y₂) hsub
          (S.anti k2 k1 (N r y₁) h21 hk1)))
  -- Step 2: Define E', H, O, and closed cover A r
  let E' (r : ℕ) (y : X) : Set X := {x ∈ N r y | N r y ⊆ U x}
  let H (r : ℕ) (y : X) : Set X := closure (E' r y)
  have hH_closed (r : ℕ) (y : X) : IsClosed (H r y) := isClosed_closure
  have hH_sub_N (r : ℕ) (y : X) : H r y ⊆ N r y :=
    closure_minimal (fun _ hx => hx.1) (hN_closed r y)
  let O (r : ℕ) (y : X) : Set X := W r y ∩ ⋃ a ∈ N r y, U a
  have hO_open (r : ℕ) (y : X) : IsOpen (O r y) :=
    (hW_open r y).inter (isOpen_iUnion fun a => isOpen_iUnion fun _ => hU_open a)
  have hH_sub_O (r : ℕ) (y : X) : H r y ⊆ O r y := fun z hz =>
    ⟨hN_sub_W r y (hH_sub_N r y hz), mem_iUnion₂.2 ⟨z, hH_sub_N r y hz, hU_self z⟩⟩
  have hO_disj (r : ℕ) {y₁ y₂ : X} (hne : y₁ ≠ y₂) : Disjoint (O r y₁) (O r y₂) :=
    (hW_disj r hne).mono inter_subset_left inter_subset_left
  have hO_unique (r : ℕ) {y₁ y₂ : X} {z : X} (h1 : z ∈ O r y₁) (h2 : z ∈ O r y₂) : y₁ = y₂ := by
    by_contra hne
    exact Set.disjoint_left.1 (hO_disj r hne) h1 h2
  let A (r : ℕ) : Set X := ⋃ y, H r y
  have hA_closed (r : ℕ) : IsClosed (A r) :=
    ((hN_lf r).subset (hH_sub_N r)).isClosed_iUnion (hH_closed r)
  have hA_cov (z : X) : ∃ r, z ∈ A r := by
    obtain ⟨r, y, hzy, hsub⟩ := hN_net z (U z) (hU_open z) (hU_self z)
    exact ⟨r, mem_iUnion.2 ⟨y, subset_closure ⟨hzy, hsub⟩⟩⟩
  have hO_bound (r : ℕ) (y : X) {z : X} (hz : z ∈ H r y) : O r y ⊆ iterNet U 3 {z} := by
    intro t ht
    have hne : (E' r y ∩ U z).Nonempty := by
      rw [mem_closure_iff] at hz
      exact (hz (U z) (hU_open z) (hU_self z)).imp fun x hx => ⟨hx.2, hx.1⟩
    obtain ⟨x, ⟨_, hNsubUx⟩, hxz⟩ := hne
    obtain ⟨_, hta⟩ := ht
    simp only [mem_iUnion] at hta
    obtain ⟨a, haN, htaU⟩ := hta
    have haUx : a ∈ U x := hNsubUx haN
    have hx1 : x ∈ iterNet U 1 {z} := mem_iterNet_succ.2 ⟨z, mem_singleton z, hxz⟩
    have ha2 : a ∈ iterNet U 2 {z} := mem_iterNet_succ.2 ⟨x, hx1, haUx⟩
    exact mem_iterNet_succ.2 ⟨a, ha2, htaU⟩
  -- Step 3: Transitive open neighbornet T r for each r
  classical
  let T (r : ℕ) (z : X) : Set X :=
    if h : ∃ y, z ∈ H r y then O r h.choose
    else if h' : ∃ y, z ∈ O r y then O r h'.choose \ A r
    else (A r)ᶜ
  have hT_eq_of_H (r : ℕ) {z y : X} (hz : z ∈ H r y) : T r z = O r y := by
    have hex : ∃ y', z ∈ H r y' := ⟨y, hz⟩
    simp only [T, dif_pos hex]
    have heq : hex.choose = y := hO_unique r (hH_sub_O r hex.choose hex.choose_spec) (hH_sub_O r y hz)
    rw [heq]
  have hT_eq_of_O_notA (r : ℕ) {z y : X} (hzO : z ∈ O r y) (hzA : z ∉ A r) :
      T r z = O r y \ A r := by
    have hnoH : ¬ ∃ y', z ∈ H r y' := fun ⟨y', hy'⟩ => hzA (mem_iUnion.2 ⟨y', hy'⟩)
    have hexO : ∃ y', z ∈ O r y' := ⟨y, hzO⟩
    simp only [T, dif_neg hnoH, dif_pos hexO]
    have heq : hexO.choose = y := hO_unique r hexO.choose_spec hzO
    rw [heq]
  have hT_eq_of_notO (r : ℕ) {z : X} (hznotO : ¬ ∃ y, z ∈ O r y) : T r z = (A r)ᶜ := by
    have hnoH : ¬ ∃ y, z ∈ H r y := fun ⟨y, hy⟩ => hznotO ⟨y, hH_sub_O r y hy⟩
    simp only [T, dif_neg hnoH, dif_neg hznotO]
  have hT_open (r : ℕ) (z : X) : IsOpen (T r z) := by
    by_cases hH : ∃ y, z ∈ H r y
    · obtain ⟨y, hy⟩ := hH
      rw [hT_eq_of_H r hy]
      exact hO_open r y
    · have hzA : z ∉ A r := fun h => hH (mem_iUnion.1 h)
      by_cases hO : ∃ y, z ∈ O r y
      · obtain ⟨y, hy⟩ := hO
        rw [hT_eq_of_O_notA r hy hzA]
        exact (hO_open r y).sdiff (hA_closed r)
      · rw [hT_eq_of_notO r hO]
        exact (hA_closed r).isOpen_compl
  have hT_self (r : ℕ) (z : X) : z ∈ T r z := by
    by_cases hH : ∃ y, z ∈ H r y
    · obtain ⟨y, hy⟩ := hH
      rw [hT_eq_of_H r hy]
      exact hH_sub_O r y hy
    · have hzA : z ∉ A r := fun h => hH (mem_iUnion.1 h)
      by_cases hO : ∃ y, z ∈ O r y
      · obtain ⟨y, hy⟩ := hO
        rw [hT_eq_of_O_notA r hy hzA]
        exact ⟨hy, hzA⟩
      · rw [hT_eq_of_notO r hO]
        exact hzA
  have hT_trans (r : ℕ) (z w : X) (hw : w ∈ T r z) : T r w ⊆ T r z := by
    by_cases hH : ∃ y, z ∈ H r y
    · obtain ⟨y, hy⟩ := hH
      rw [hT_eq_of_H r hy] at hw ⊢
      by_cases hwA : w ∈ A r
      · obtain ⟨y', hy'⟩ := mem_iUnion.1 hwA
        have heq : y' = y := hO_unique r (hH_sub_O r y' hy') hw
        rw [hT_eq_of_H r (heq ▸ hy')]
      · rw [hT_eq_of_O_notA r hw hwA]
        exact diff_subset
    · have hzA : z ∉ A r := fun h => hH (mem_iUnion.1 h)
      by_cases hO : ∃ y, z ∈ O r y
      · obtain ⟨y, hy⟩ := hO
        rw [hT_eq_of_O_notA r hy hzA] at hw ⊢
        rw [hT_eq_of_O_notA r hw.1 hw.2]
      · rw [hT_eq_of_notO r hO] at hw ⊢
        by_cases hwO : ∃ y', w ∈ O r y'
        · obtain ⟨y', hy'⟩ := hwO
          rw [hT_eq_of_O_notA r hy' hw]
          exact fun _ ht => ht.2
        · rw [hT_eq_of_notO r hwO]
  have hT_bound (r : ℕ) {z : X} (hz : z ∈ A r) : T r z ⊆ iterNet U 3 {z} := by
    obtain ⟨y, hy⟩ := mem_iUnion.1 hz
    rw [hT_eq_of_H r hy]
    exact hO_bound r y hy
  -- Step 4: Glue T r along the countable closed cover A r
  let r0 (z : X) : ℕ := Nat.find (hA_cov z)
  let V (z : X) : Set X :=
    (⋂ k ∈ Finset.range (r0 z + 1), T k z) \ (⋃ k ∈ Finset.range (r0 z), A k)
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · intro z
    exact (isOpen_biInter_finset fun k _ => hT_open k z).sdiff
      (isClosed_biUnion_finset fun k _ => hA_closed k)
  · intro z
    refine ⟨?_, ?_⟩
    · simp only [mem_iInter]
      intro k _
      exact hT_self k z
    · simp only [mem_iUnion, Finset.mem_range, not_exists]
      intro k hk hzk
      exact Nat.find_min (hA_cov z) hk hzk
  · intro z w hw
    have hr_le : r0 z ≤ r0 w := by
      by_contra hlt
      have hlt' : r0 w < r0 z := Nat.lt_of_not_ge hlt
      exact hw.2 (mem_iUnion₂.2 ⟨r0 w, Finset.mem_range.2 hlt', Nat.find_spec (hA_cov w)⟩)
    intro t ht
    refine ⟨?_, ?_⟩
    · simp only [mem_iInter, Finset.mem_range]
      intro k hk
      have hkw : w ∈ T k z := (mem_iInter₂.1 hw.1) k (Finset.mem_range.2 hk)
      have htw : t ∈ T k w := (mem_iInter₂.1 ht.1) k (Finset.mem_range.2 (by omega))
      exact hT_trans k z w hkw htw
    · intro htA
      simp only [mem_iUnion, Finset.mem_range] at htA
      obtain ⟨k, hk, htk⟩ := htA
      exact ht.2 (mem_iUnion₂.2 ⟨k, Finset.mem_range.2 (by omega), htk⟩)
  · intro z t ht
    have htT : t ∈ T (r0 z) z :=
      (mem_iInter₂.1 ht.1) (r0 z) (Finset.mem_range.2 (Nat.lt_succ_self (r0 z)))
    exact hT_bound (r0 z) (Nat.find_spec (hA_cov z)) htT

/-- Any transitive open neighbornet `V` induces a closure-preserving closed family. -/
private lemma closurePreserving_of_transitive_neighbornet
    (V : X → Set X) (hV_open : ∀ x, IsOpen (V x)) (hV_self : ∀ x, x ∈ V x)
    (hV_trans : ∀ x y, y ∈ V x → V y ⊆ V x) :
    ClosurePreserving {B : Set X | ∃ S : Set X, B = (⋃ a ∈ S, V a)ᶜ} := by
  intro 𝓖 h𝓖
  apply Subset.antisymm
  · intro x hxcl
    by_contra hxnot
    have hdisj : Disjoint (V x) (⋃₀ 𝓖) := by
      rw [Set.disjoint_left]
      intro z hzx hzG
      obtain ⟨B, hBG, hzB⟩ := hzG
      obtain ⟨S, rfl⟩ := h𝓖 hBG
      have hxnotB : x ∉ (⋃ a ∈ S, V a)ᶜ := fun hxB =>
        hxnot ⟨closure (⋃ a ∈ S, V a)ᶜ, ⟨(⋃ a ∈ S, V a)ᶜ, hBG, rfl⟩, subset_closure hxB⟩
      rw [mem_compl_iff, not_not] at hxnotB
      simp only [mem_iUnion] at hxnotB
      obtain ⟨a, haS, hxa⟩ := hxnotB
      have hza : z ∈ V a := hV_trans a x hxa hzx
      exact hzB (mem_iUnion₂.2 ⟨a, haS, hza⟩)
    rw [mem_closure_iff] at hxcl
    obtain ⟨z, hzx, hzG⟩ := hxcl (V x) (hV_open x) (hV_self x)
    exact Set.disjoint_left.1 hdisj hzx hzG
  · intro x hx
    obtain ⟨C, ⟨B, hBG, rfl⟩, hxC⟩ := hx
    exact closure_mono (subset_sUnion_of_mem hBG) hxC

end Helpers

theorem main : Specs.L_0011.stmt := by
  unfold Specs.L_0011.stmt
  intro X _ hT3 ⟨G, hG⟩
  let S := mkDecStrat G hG
  obtain ⟨N, hN_closed, hN_lf, hN_disj, hN_net⟩ := exists_sigmaDiscrete_closed_network S
  have hV_ex : ∀ m : ℕ, ∃ V : X → Set X,
      (∀ x, IsOpen (V x)) ∧
      (∀ x, x ∈ V x) ∧
      (∀ x y, y ∈ V x → V y ⊆ V x) ∧
      (∀ x, V x ⊆ iterNet (fun y => S.G m {y}) 3 {x}) := fun m =>
    exists_transitive_neighbornet_cubed S N hN_closed hN_lf hN_disj hN_net
      (fun y => S.G m {y}) (fun y => S.isOpen m {y} isClosed_singleton)
      (fun y => S.subset m {y} isClosed_singleton (mem_singleton y))
  choose V hV_open hV_self hV_trans hV_bound using hV_ex
  let 𝓑' : ℕ → Set (Set X) := fun m => {B : Set X | ∃ H : Set X, B = (⋃ a ∈ H, V m a)ᶜ}
  refine ⟨⋃ m, 𝓑' m, ?_, ⟨𝓑', ?_, rfl⟩⟩
  · -- IsQuasiBase
    intro x O hO hxO
    let H : Set X := Oᶜ
    have hH_closed : IsClosed H := hO.isClosed_compl
    have hxH : x ∉ H := fun h => h hxO
    obtain ⟨m, hm⟩ := exists_notMem_closure_iterNet S 3 H hH_closed x hxH
    let B : Set X := (⋃ a ∈ H, V m a)ᶜ
    refine ⟨B, mem_iUnion.2 ⟨m, H, rfl⟩, ?_, ?_⟩
    · -- x ∈ interior B
      have hsub : (⋃ a ∈ H, V m a) ⊆ iterNet (fun y => S.G m {y}) 3 H := by
        intro z hz
        simp only [mem_iUnion] at hz
        obtain ⟨a, haH, hza⟩ := hz
        have hza' : z ∈ iterNet (fun y => S.G m {y}) 3 {a} := hV_bound m a hza
        exact iterNet_mono_set (singleton_subset_iff.2 haH) hza'
      have hxcl : x ∈ (closure (⋃ a ∈ H, V m a))ᶜ := fun h => hm (closure_mono hsub h)
      exact mem_interior.2 ⟨(closure (⋃ a ∈ H, V m a))ᶜ,
        compl_subset_compl.2 subset_closure, isClosed_closure.isOpen_compl, hxcl⟩
    · -- B ⊆ O
      intro z hz
      by_contra hzo
      exact hz (mem_iUnion₂.2 ⟨z, hzo, hV_self m z⟩)
  · -- ∀ m, ClosurePreserving (𝓑' m)
    intro m
    exact closurePreserving_of_transitive_neighbornet (V m) (hV_open m) (hV_self m) (hV_trans m)

end Proofs.L_0011
