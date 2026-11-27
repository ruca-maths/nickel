import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Rat.Denumerable
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Defs.D_0009
import Targets.Defs
import Proofs.L_0002
import Proofs.L_0003
import Proofs.L_0004
import Proofs.L_0006

/-!
# The Sorgenfrey Line `(ℝ, Defs.D_0009.rho ℝ)` is Neither Stratifiable nor `M₁`

This standalone module proves that the Sorgenfrey line `(ℝ, Defs.D_0009.rho ℝ)` — the
uncountable real counterpart of Chen–Wang's half-open interval topology `Defs.D_0009.rho` —
is **not stratifiable** and **not `M₁`**, despite being zero-dimensional, first-countable,
regular, and Lindelöf:

1. **`sorgenfrey_prod_not_normal`**: The Sorgenfrey plane `(ℝ, rho ℝ) × (ℝ, rho ℝ)` is
   not `NormalSpace`, proved via Jones's Lemma applied to the countable dense subset `ℚ × ℚ`
   and the continuum-sized closed discrete anti-diagonal `D = { (x, -x) | x : ℝ }`.
2. **`isStratifiable_prod`**: Borges (1966) finite-product permanence of `MSpace.IsStratifiable`
   (self-contained via `IsStratification` without needing extra imports).
3. **`normalSpace_of_isStratifiable`**: Every stratifiable space is `NormalSpace` (via the
   monotone normality operator `Hsep`).
4. **`sorgenfrey_not_isStratifiable`** & **`sorgenfrey_not_isM1`**:
   `¬ @MSpace.IsStratifiable ℝ (Defs.D_0009.rho ℝ)` and
   `¬ @MSpace.IsM1 ℝ (Defs.D_0009.rho ℝ)`.
-/

namespace Research.SorgenfreyNotStrat

open Set Topology TopologicalSpace

/-! ## Part 1: Basic properties of the Sorgenfrey topology `Defs.D_0009.rho ℝ` -/

/-- The Sorgenfrey topology on `ℝ`, using `Defs.D_0009.rho ℝ`. -/
noncomputable abbrev sorgTop : TopologicalSpace ℝ := Defs.D_0009.rho ℝ

/-- Product topology on the Sorgenfrey plane `ℝ × ℝ`. -/
noncomputable abbrev sorgProdTop : TopologicalSpace (ℝ × ℝ) := @instTopologicalSpaceProd ℝ ℝ sorgTop sorgTop

private lemma sorg_exists_Ico_subset {U : Set ℝ} (hUo : @IsOpen ℝ sorgTop U) {x : ℝ} (hx : x ∈ U) :
    ∃ u : ℝ, x < u ∧ Set.Ico x u ⊆ U := by
  let : TopologicalSpace ℝ := sorgTop
  have hgen : ∀ V : Set ℝ, IsOpen V → ∀ y ∈ V, ∃ a b : ℝ, y ∈ Set.Ico a b ∧ Set.Ico a b ⊆ V := by
    intro V hV
    induction hV with
    | basic s hs =>
      obtain ⟨a, b, rfl⟩ := hs
      exact fun y hy => ⟨a, b, hy, Subset.rfl⟩
    | univ =>
      exact fun y _ => ⟨y, y + 1, ⟨le_rfl, by linarith⟩, subset_univ _⟩
    | inter s t _ _ ihs iht =>
      intro y ⟨hys, hyt⟩
      obtain ⟨a₁, b₁, hy1, h1⟩ := ihs y hys
      obtain ⟨a₂, b₂, hy2, h2⟩ := iht y hyt
      refine ⟨max a₁ a₂, min b₁ b₂, ⟨max_le hy1.1 hy2.1, lt_min hy1.2 hy2.2⟩, fun z hz => ?_⟩
      exact ⟨h1 ⟨le_trans (le_max_left _ _) hz.1, lt_of_lt_of_le hz.2 (min_le_left _ _)⟩,
             h2 ⟨le_trans (le_max_right _ _) hz.1, lt_of_lt_of_le hz.2 (min_le_right _ _)⟩⟩
    | sUnion F _ ih =>
      rintro y ⟨s, hsF, hys⟩
      obtain ⟨a, b, hy, hsub⟩ := ih s hsF y hys
      exact ⟨a, b, hy, hsub.trans (subset_sUnion_of_mem hsF)⟩
  obtain ⟨a, b, hxb, hsub⟩ := hgen U hUo x hx
  exact ⟨b, hxb.2, fun z hz => hsub ⟨le_trans hxb.1 hz.1, hz.2⟩⟩

/-! ## Part 2: Dense `ℚ × ℚ` and closed discrete anti-diagonal in the Sorgenfrey plane -/

/-- The rational grid `ℚ × ℚ` inside `ℝ × ℝ`. -/
def ratGrid : Set (ℝ × ℝ) := Set.range (fun p : ℚ × ℚ => ((p.1 : ℝ), (p.2 : ℝ)))

/-- The anti-diagonal `{ (x, -x) | x : ℝ }` inside `ℝ × ℝ`. -/
def antiDiag : Set (ℝ × ℝ) := { p : ℝ × ℝ | p.2 = -p.1 }

/-- `ratGrid` is dense in the Sorgenfrey plane. -/
theorem ratGrid_dense : @Dense (ℝ × ℝ) sorgProdTop ratGrid := by
  let : TopologicalSpace ℝ := sorgTop
  rw [dense_iff_inter_open]
  intro U hUo ⟨⟨x, y⟩, hxyU⟩
  obtain ⟨V, W, hVo, hWo, hxV, hyW, hVWU⟩ := isOpen_prod_iff.mp hUo x y hxyU
  obtain ⟨u, hxu, hVsub⟩ := sorg_exists_Ico_subset hVo hxV
  obtain ⟨v, hyv, hWsub⟩ := sorg_exists_Ico_subset hWo hyW
  obtain ⟨a, hxa, hau⟩ := exists_rat_btwn hxu
  obtain ⟨b, hyb, hbv⟩ := exists_rat_btwn hyv
  refine ⟨((a : ℝ), (b : ℝ)), hVWU ⟨hVsub ⟨le_of_lt hxa, hau⟩, hWsub ⟨le_of_lt hyb, hbv⟩⟩,
    ⟨(a, b), rfl⟩⟩

/-- Every subset of `antiDiag` is closed in the Sorgenfrey plane. -/
theorem antiDiag_closed_discrete :
    ∀ S ⊆ antiDiag, @IsClosed (ℝ × ℝ) sorgProdTop S := by
  let : TopologicalSpace ℝ := sorgTop
  intro S hS
  rw [← isOpen_compl_iff]
  refine isOpen_iff_mem_nhds.mpr fun ⟨x, y⟩ hxy => ?_
  rcases lt_trichotomy (x + y) 0 with hlt | heq | hgt
  · let ε : ℝ := -(x + y) / 2
    have hε : 0 < ε := by dsimp only [ε]; linarith
    have hopen : IsOpen (Set.Ico x (x + ε) ×ˢ Set.Ico y (y + ε)) :=
      (Defs.D_0009.isOpen_Ico x (x + ε)).prod (Defs.D_0009.isOpen_Ico y (y + ε))
    refine Filter.mem_of_superset (hopen.mem_nhds ⟨⟨le_rfl, by linarith⟩, ⟨le_rfl, by linarith⟩⟩) ?_
    rintro ⟨a, b⟩ ⟨⟨_, ha⟩, ⟨_, hb⟩⟩ habS
    have ha' : a < x + ε := ha
    have hb' : b < y + ε := hb
    have hdiag : b = -a := hS habS
    dsimp only [ε] at ha' hb'
    linarith
  · have hyx : y = -x := by linarith
    have hopen : IsOpen (Set.Ico x (x + 1) ×ˢ Set.Ico y (y + 1)) :=
      (Defs.D_0009.isOpen_Ico x (x + 1)).prod (Defs.D_0009.isOpen_Ico y (y + 1))
    refine Filter.mem_of_superset (hopen.mem_nhds ⟨⟨le_rfl, by linarith⟩, ⟨le_rfl, by linarith⟩⟩) ?_
    rintro ⟨a, b⟩ ⟨⟨ha, _⟩, ⟨hb, _⟩⟩ habS
    have hdiag : b = -a := hS habS
    have hax : a = x := by linarith
    have hby : b = y := by linarith
    subst hax; subst hby
    exact hxy habS
  · have hopen : IsOpen (Set.Ico x (x + 1) ×ˢ Set.Ico y (y + 1)) :=
      (Defs.D_0009.isOpen_Ico x (x + 1)).prod (Defs.D_0009.isOpen_Ico y (y + 1))
    refine Filter.mem_of_superset (hopen.mem_nhds ⟨⟨le_rfl, by linarith⟩, ⟨le_rfl, by linarith⟩⟩) ?_
    rintro ⟨a, b⟩ ⟨⟨ha, _⟩, ⟨hb, _⟩⟩ habS
    have hdiag : b = -a := hS habS
    linarith

/-! ## Part 3: Jones's Lemma & non-normality of the Sorgenfrey plane -/

private lemma jones_lemma {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {Q D : Set X} (hQ : Dense Q) (hD : ∀ S ⊆ D, IsClosed S) :
    ∃ φ : Set D → Set Q, Function.Injective φ := by
  have hsep : ∀ A : Set D, ∃ U V : Set X,
      IsOpen U ∧ IsOpen V ∧
      ((Subtype.val : D → X) '' A) ⊆ U ∧
      ((Subtype.val : D → X) '' Aᶜ) ⊆ V ∧
      Disjoint U V := by
    intro A
    have hA_cl : IsClosed ((Subtype.val : D → X) '' A) := hD _ (Subtype.coe_image_subset D A)
    have hAc_cl : IsClosed ((Subtype.val : D → X) '' Aᶜ) := hD _ (Subtype.coe_image_subset D Aᶜ)
    have hdisj : Disjoint ((Subtype.val : D → X) '' A) ((Subtype.val : D → X) '' Aᶜ) := by
      rw [Set.disjoint_left]
      rintro _ ⟨a, haA, rfl⟩ ⟨b, hbAc, hab⟩
      exact hbAc ((Subtype.ext hab.symm) ▸ haA)
    exact normal_separation hA_cl hAc_cl hdisj
  choose U V hUo hVo hAU hAcV hUV using hsep
  let φ : Set D → Set Q := fun A => (Subtype.val : Q → X) ⁻¹' U A
  refine ⟨φ, fun A₁ A₂ hEq => ?_⟩
  ext d
  constructor
  · intro hd₁
    by_contra hd₂
    obtain ⟨q, hqUV, hqQ⟩ := dense_iff_inter_open.mp hQ (U A₁ ∩ V A₂)
      ((hUo A₁).inter (hVo A₂)) ⟨d.1, hAU A₁ ⟨d, hd₁, rfl⟩, hAcV A₂ ⟨d, hd₂, rfl⟩⟩
    have hq₁ : (⟨q, hqQ⟩ : Q) ∈ φ A₁ := hqUV.1
    rw [hEq] at hq₁
    exact Set.disjoint_left.mp (hUV A₂) hq₁ hqUV.2
  · intro hd₂
    by_contra hd₁
    obtain ⟨q, hqUV, hqQ⟩ := dense_iff_inter_open.mp hQ (U A₂ ∩ V A₁)
      ((hUo A₂).inter (hVo A₁)) ⟨d.1, hAU A₂ ⟨d, hd₂, rfl⟩, hAcV A₁ ⟨d, hd₁, rfl⟩⟩
    have hq₂ : (⟨q, hqQ⟩ : Q) ∈ φ A₂ := hqUV.1
    rw [← hEq] at hq₂
    exact Set.disjoint_left.mp (hUV A₁) hq₂ hqUV.2

private lemma geom_third_tail_bound (m d : ℕ) :
    (∑ i ∈ Finset.range d, ((1 : ℝ) / 3) ^ (m + 1 + i)) ≤ ((1 : ℝ) / 2) * ((1 : ℝ) / 3) ^ m := by
  have hgeom : ∀ k : ℕ,
      (∑ i ∈ Finset.range k, ((1 : ℝ) / 3) ^ (m + 1 + i)) +
        ((1 : ℝ) / 2) * ((1 : ℝ) / 3) ^ (m + k) =
      ((1 : ℝ) / 2) * ((1 : ℝ) / 3) ^ m := by
    intro k
    induction k with
    | zero => simp
    | succ k ihk =>
      rw [Finset.sum_range_succ, add_assoc]
      have hstep : ((1 : ℝ) / 3) ^ (m + 1 + k) + ((1 : ℝ) / 2) * ((1 : ℝ) / 3) ^ (m + (k + 1)) =
          ((1 : ℝ) / 2) * ((1 : ℝ) / 3) ^ (m + k) := by
        have h1 : m + 1 + k = m + k + 1 := by omega
        have h2 : m + (k + 1) = m + k + 1 := by omega
        rw [h1, h2, pow_succ]
        have h3 : (1 : ℝ) / 3 + (1 : ℝ) / 2 * ((1 : ℝ) / 3) = (1 : ℝ) / 2 := by norm_num
        calc ((1 : ℝ) / 3) ^ (m + k) * (1 / 3) + 1 / 2 * (((1 : ℝ) / 3) ^ (m + k) * (1 / 3))
            = ((1 : ℝ) / 3) ^ (m + k) * (1 / 3 + 1 / 2 * (1 / 3)) := by ring
          _ = ((1 : ℝ) / 3) ^ (m + k) * (1 / 2) := by rw [h3]
          _ = 1 / 2 * ((1 : ℝ) / 3) ^ (m + k) := mul_comm _ _
      rw [hstep, ihk]
  have hpos : (0 : ℝ) ≤ ((1 : ℝ) / 2) * ((1 : ℝ) / 3) ^ (m + d) :=
    mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _)
  have h := hgeom d
  linarith

private lemma exists_injective_setNat_real : ∃ ψ : Set ℕ → ℝ, Function.Injective ψ := by
  classical
  let term : Set ℕ → ℕ → ℝ := fun A i => if i ∈ A then ((1 : ℝ) / 3) ^ i else 0
  let psum : Set ℕ → ℕ → ℝ := fun A k => ∑ i ∈ Finset.range k, term A i
  have hterm_nonneg : ∀ A i, 0 ≤ term A i := fun A i => by
    dsimp only [term]; split_ifs
    · exact pow_nonneg (by norm_num) _
    · exact le_rfl
  have hterm_le : ∀ A i, term A i ≤ ((1 : ℝ) / 3) ^ i := fun A i => by
    dsimp only [term]; split_ifs
    · exact le_rfl
    · exact pow_nonneg (by norm_num) _
  have hpsum_mono : ∀ A {k₁ k₂ : ℕ}, k₁ ≤ k₂ → psum A k₁ ≤ psum A k₂ := by
    intro A k₁ k₂ hle
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hle)
      (fun i _ _ => hterm_nonneg A i)
  have hpsum_tail : ∀ A m k, psum A k ≤ psum A (m + 1) + ((1 : ℝ) / 2) * ((1 : ℝ) / 3) ^ m := by
    intro A m k
    by_cases hk : k ≤ m + 1
    · have h1 := hpsum_mono A hk
      have h2 : (0 : ℝ) ≤ ((1 : ℝ) / 2) * ((1 : ℝ) / 3) ^ m :=
        mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _)
      linarith
    · push Not at hk
      let d := k - (m + 1)
      have hk_eq : k = (m + 1) + d := by omega
      rw [hk_eq]
      have hsplit : psum A ((m + 1) + d) = psum A (m + 1) +
          ∑ i ∈ Finset.range d, term A (m + 1 + i) := by
        dsimp only [psum]
        rw [Finset.sum_range_add]
      rw [hsplit]
      have hsum_le : (∑ i ∈ Finset.range d, term A (m + 1 + i)) ≤
          ∑ i ∈ Finset.range d, ((1 : ℝ) / 3) ^ (m + 1 + i) :=
        Finset.sum_le_sum fun i _ => hterm_le A (m + 1 + i)
      exact add_le_add_right (hsum_le.trans (geom_third_tail_bound m d)) _
  have hbdd : ∀ A : Set ℕ, BddAbove (Set.range (psum A)) := by
    intro A
    refine ⟨psum A 1 + ((1 : ℝ) / 2) * ((1 : ℝ) / 3) ^ 0, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact hpsum_tail A 0 k
  let ψ : Set ℕ → ℝ := fun A => sSup (Set.range (psum A))
  refine ⟨ψ, fun A B hAB => ?_⟩
  by_contra hne
  have hex : ∃ n : ℕ, (n ∈ A) ≠ (n ∈ B) := by
    by_contra hall
    push Not at hall
    apply hne
    ext n
    exact eq_iff_iff.mp (hall n)
  let m : ℕ := Nat.find hex
  have hm_diff : (m ∈ A) ≠ (m ∈ B) := Nat.find_spec hex
  have hm_eq : psum A m = psum B m := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have him : i < m := Finset.mem_range.mp hi
    have heq : (i ∈ A) = (i ∈ B) := by
      by_contra h
      exact Nat.find_min hex him h
    simp only [term, heq]
  have hlt_of : ∀ {X Y : Set ℕ}, psum X m = psum Y m → m ∈ X → m ∉ Y → ψ Y < ψ X := by
    intro X Y hXY hmX hmY
    have hX_lb : psum X m + ((1 : ℝ) / 3) ^ m ≤ ψ X := by
      have h1 : psum X (m + 1) = psum X m + ((1 : ℝ) / 3) ^ m := by
        dsimp only [psum]; rw [Finset.sum_range_succ]; simp [term, hmX]
      rw [← h1]
      exact le_csSup (hbdd X) ⟨m + 1, rfl⟩
    have hY_ub : ψ Y ≤ psum Y m + ((1 : ℝ) / 2) * ((1 : ℝ) / 3) ^ m := by
      refine csSup_le (Set.range_nonempty _) ?_
      rintro _ ⟨k, rfl⟩
      have h1 : psum Y (m + 1) = psum Y m := by
        dsimp only [psum]; rw [Finset.sum_range_succ]; simp [term, hmY]
      rw [← h1]
      exact hpsum_tail Y m k
    have hpos : (0 : ℝ) < ((1 : ℝ) / 3) ^ m := pow_pos (by norm_num) _
    linarith
  by_cases hmA : m ∈ A
  · have hmB : m ∉ B := fun h => hm_diff (propext ⟨fun _ => h, fun _ => hmA⟩)
    exact ne_of_gt (hlt_of hm_eq hmA hmB) hAB
  · have hmB : m ∈ B := by
      by_contra h
      exact hm_diff (propext ⟨fun h' => (hmA h').elim, fun h' => (h h').elim⟩)
    exact ne_of_lt (hlt_of hm_eq.symm hmB hmA) hAB

/-- The Sorgenfrey plane `(ℝ, rho ℝ) × (ℝ, rho ℝ)` is not normal. -/
theorem sorgenfrey_prod_not_normal : ¬ @NormalSpace (ℝ × ℝ) sorgProdTop := by
  let : TopologicalSpace (ℝ × ℝ) := sorgProdTop
  intro hN
  obtain ⟨φ, hφ⟩ := jones_lemma ratGrid_dense antiDiag_closed_discrete
  have hle_inj : Cardinal.mk (Set antiDiag) ≤ Cardinal.mk (Set ratGrid) :=
    Cardinal.mk_le_of_injective hφ
  have hQ_cnt : Countable ratGrid := (Set.countable_range _).to_subtype
  obtain ⟨eQ, heQ⟩ := exists_injective_nat ratGrid
  have hSetQ_le_SetNat : Cardinal.mk (Set ratGrid) ≤ Cardinal.mk (Set ℕ) := by
    refine Cardinal.mk_le_of_injective (f := fun S : Set ratGrid => eQ '' S) ?_
    intro S₁ S₂ hEq
    exact Set.image_injective.mpr heQ hEq
  obtain ⟨ψ, hψ⟩ := exists_injective_setNat_real
  have hSetNat_le_R : Cardinal.mk (Set ℕ) ≤ Cardinal.mk ℝ :=
    Cardinal.mk_le_of_injective hψ
  have hR_le_D : Cardinal.mk ℝ ≤ Cardinal.mk antiDiag := by
    refine Cardinal.mk_le_of_injective (f := fun x : ℝ => (⟨(x, -x), rfl⟩ : antiDiag)) ?_
    intro x y h
    exact congrArg (fun p : antiDiag => p.1.1) h
  have hD_lt_SetD : Cardinal.mk antiDiag < Cardinal.mk (Set antiDiag) := by
    rw [Cardinal.mk_set]
    exact Cardinal.cantor _
  have hSetQ_le_D : Cardinal.mk (Set ratGrid) ≤ Cardinal.mk antiDiag :=
    le_trans hSetQ_le_SetNat (le_trans hSetNat_le_R hR_le_D)
  exact not_le_of_gt hD_lt_SetD (le_trans hle_inj hSetQ_le_D)

/-! ## Part 4: Stratifiable ⇒ Normal & finite products ⇒ Sorgenfrey is not stratifiable / not `M₁` -/

private lemma exists_antitone_stratification {X : Type*} [TopologicalSpace X]
    {G : ℕ → Set X → Set X} (hG : MSpace.IsStratification G) :
    ∃ G' : ℕ → Set X → Set X,
      MSpace.IsStratification G' ∧ (∀ n H, G' (n + 1) H ⊆ G' n H) := by
  rcases hG with ⟨hGo, hGs, hGi, hGm⟩
  let G' : ℕ → Set X → Set X := fun n H => ⋂ i ∈ Finset.range (n + 1), G i H
  refine ⟨G', ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro n H hH; exact isOpen_biInter_finset fun i _ => hGo i H hH
  · intro n H hH x hx; exact mem_iInter₂.mpr fun i _ => hGs i H hH hx
  · intro H hH
    apply Subset.antisymm
    · intro x hx
      rw [← hGi H hH]
      refine mem_iInter.mpr fun n => closure_mono (fun y hy =>
        mem_iInter₂.mp hy n (Finset.mem_range.mpr (Nat.lt_succ_self n))) (mem_iInter.mp hx n)
    · intro x hx
      exact mem_iInter.mpr fun n => subset_closure (mem_iInter₂.mpr fun i _ => hGs i H hH hx)
  · intro n H K hH hK hHK x hx
    exact mem_iInter₂.mpr fun i hi => hGm i H K hH hK hHK (mem_iInter₂.mp hx i hi)
  · intro n H x hx
    exact mem_iInter₂.mpr fun i hi =>
      mem_iInter₂.mp hx i (Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hi)))

private lemma antitone_le {X : Type*} {G : ℕ → Set X → Set X}
    (hanti : ∀ n H, G (n + 1) H ⊆ G n H) {m n : ℕ} (hmn : m ≤ n) (H : Set X) :
    G n H ⊆ G m H := by
  induction hmn with
  | refl => exact Subset.rfl
  | step _ ih => exact (hanti _ H).trans ih

private lemma normalSpace_of_isStratifiable {X : Type} [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X) : NormalSpace X :=
  (Proofs.L_0006.main X hStrat).1

private lemma isStratifiable_prod_self {X : Type*} [TopologicalSpace X]
    (hStrat : MSpace.IsStratifiable X) : MSpace.IsStratifiable (X × X) := by
  have : T1Space X := hStrat.1
  obtain ⟨_, G₀, hG₀⟩ := hStrat
  obtain ⟨G, hG, hanti⟩ := exists_antitone_stratification hG₀
  -- Define `g n x := G n {x}` and `gp n (x, y) := G n {x} ×ˢ G n {y}`,
  -- then `GP n H := ⋃ p ∈ H, gp n p`.
  let gp : ℕ → X × X → Set (X × X) := fun n p => G n {p.1} ×ˢ G n {p.2}
  let GP : ℕ → Set (X × X) → Set (X × X) := fun n H => ⋃ p ∈ H, gp n p
  refine ⟨inferInstance, GP, ?_, ?_, ?_, ?_⟩
  · intro n H _
    exact isOpen_biUnion fun p _ =>
      (hG.1 n {p.1} isClosed_singleton).prod (hG.1 n {p.2} isClosed_singleton)
  · intro n H _ p hpH
    exact mem_iUnion₂.mpr ⟨p, hpH, hG.2.1 n _ isClosed_singleton rfl, hG.2.1 n _ isClosed_singleton rfl⟩
  · intro H hH
    apply Subset.antisymm
    · intro ⟨x, y⟩ hxy
      by_contra hnot
      obtain ⟨U, V, hUo, hVo, hxU, hyV, hUV⟩ :=
        isOpen_prod_iff.mp hH.isOpen_compl x y hnot
      have hUc_cl : IsClosed Uᶜ := hUo.isClosed_compl
      have hVc_cl : IsClosed Vᶜ := hVo.isClosed_compl
      have hxUc : x ∉ Uᶜ := fun h => h hxU
      have hyVc : y ∉ Vᶜ := fun h => h hyV
      rw [← hG.2.2.1 Uᶜ hUc_cl, mem_iInter] at hxUc
      rw [← hG.2.2.1 Vᶜ hVc_cl, mem_iInter] at hyVc
      push Not at hxUc hyVc
      obtain ⟨n₁, hn₁⟩ := hxUc
      obtain ⟨n₂, hn₂⟩ := hyVc
      let n := max n₁ n₂
      let W₁ : Set X := (closure (G n Uᶜ))ᶜ
      let W₂ : Set X := (closure (G n Vᶜ))ᶜ
      have hxW₁ : x ∈ W₁ := fun h => hn₁ (closure_mono (antitone_le hanti (le_max_left _ _) Uᶜ) h)
      have hyW₂ : y ∈ W₂ := fun h => hn₂ (closure_mono (antitone_le hanti (le_max_right _ _) Vᶜ) h)
      have hWo : IsOpen (W₁ ×ˢ W₂) := isClosed_closure.isOpen_compl.prod isClosed_closure.isOpen_compl
      have hcl : (x, y) ∈ closure (GP n H) := mem_iInter.mp hxy n
      obtain ⟨⟨a, b⟩, ⟨haW₁, hbW₂⟩, habGP⟩ := mem_closure_iff.mp hcl (W₁ ×ˢ W₂) hWo ⟨hxW₁, hyW₂⟩
      obtain ⟨⟨p₁, p₂⟩, hpH, haGp, hbGp⟩ := mem_iUnion₂.mp habGP
      have hp_not_UV : (p₁, p₂) ∉ U ×ˢ V := fun h => hUV h hpH
      by_cases hp₁ : p₁ ∈ U
      · have hp₂ : p₂ ∈ Vᶜ := fun h => hp_not_UV ⟨hp₁, h⟩
        have hbG : b ∈ G n Vᶜ := hG.2.2.2 n {p₂} Vᶜ isClosed_singleton hVc_cl
          (Set.singleton_subset_iff.mpr hp₂) hbGp
        exact hbW₂ (subset_closure hbG)
      · have haG : a ∈ G n Uᶜ := hG.2.2.2 n {p₁} Uᶜ isClosed_singleton hUc_cl
          (Set.singleton_subset_iff.mpr hp₁) haGp
        exact haW₁ (subset_closure haG)
    · intro p hpH
      refine mem_iInter.mpr fun n => subset_closure ?_
      exact mem_iUnion₂.mpr ⟨p, hpH, hG.2.1 n _ isClosed_singleton rfl, hG.2.1 n _ isClosed_singleton rfl⟩
  · intro n H K _ _ hHK
    exact biUnion_subset_biUnion_left hHK

/-- The Sorgenfrey line `(ℝ, Defs.D_0009.rho ℝ)` is not stratifiable. -/
theorem sorgenfrey_not_isStratifiable : ¬ @MSpace.IsStratifiable ℝ sorgTop := by
  intro hStrat
  have hProd : @MSpace.IsStratifiable (ℝ × ℝ) sorgProdTop :=
    @isStratifiable_prod_self ℝ sorgTop hStrat
  have hNorm : @NormalSpace (ℝ × ℝ) sorgProdTop :=
    @normalSpace_of_isStratifiable (ℝ × ℝ) sorgProdTop hProd
  exact sorgenfrey_prod_not_normal hNorm

/-- The Sorgenfrey line `(ℝ, Defs.D_0009.rho ℝ)` is not `M₁`. -/
theorem sorgenfrey_not_isM1 : ¬ @MSpace.IsM1 ℝ sorgTop := by
  let : TopologicalSpace ℝ := sorgTop
  intro hM1
  have hM2 : MSpace.IsM2 ℝ := Proofs.L_0002.main ℝ hM1
  have hM3 : MSpace.IsM3 ℝ := Proofs.L_0003.main ℝ hM2
  have hStrat : MSpace.IsStratifiable ℝ := Proofs.L_0004.m3_to_strat ℝ hM3
  exact sorgenfrey_not_isStratifiable hStrat

end Research.SorgenfreyNotStrat
