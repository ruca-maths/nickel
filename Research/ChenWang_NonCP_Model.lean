import Targets
import Defs.D_0001
import Defs.D_0010
import Proofs.L_0029
import Proofs.L_0032

/-!
# Concrete Zero-Dimensional `T3Space` with Clopen `G_δ` Point and `¬ HasCPOuterBase`

This file constructs the first completely concrete, kernel-verified topological space
in the repository that satisfies EVERY non-stratifiability clause of `Specs.L_0031`:

1. `delta_system_of_card_eq` & `exists_infinite_delta_system`:
   Elementary ZFC proof of the Finite `Δ`-System Lemma for uncountable families of
   finite sets.
2. `cantorCube_not_hasCPOuterBase`:
   In `I → Bool` (for any uncountable `I`, e.g. `ℕ → Bool`), the zero point has
   `¬ Defs.D_0001.HasCPOuterBase (fun _ => false)`.
3. `BoxFan I := Option (ℕ × (I → Bool))`:
   A concrete zero-dimensional `T3Space` with apex `y₀ := none`, equipped with
   clopen neighborhoods `W n` satisfying `⋂ n, W n = {y₀}`, such that:
   * `boxFan_t3Space : T3Space (BoxFan I)`
   * `boxFan_W_clopen` & `boxFan_W_inter : (⋂ n, boxFanW I n) = {none}`
   * `boxFan_not_hasCPOuterBase : ¬ Defs.D_0001.HasCPOuterBase (none : BoxFan I)`
   * `boxFan_not_hasSigmaCPLocalBase : ¬ Defs.D_0010.HasSigmaCPLocalBase (none : BoxFan I)`
     (via `Proofs.L_0032`)
   * `boxFan_not_isM1 : ¬ MSpace.IsM1 (BoxFan I)` (via `Proofs.L_0029`)
-/

namespace Research.ChenWangNonCPModel

open MSpace Set Topology

section DeltaSystem

/-- Finite `Δ`-System Lemma for uniform-cardinality uncountable families of finite sets. -/
theorem delta_system_of_card_eq {α : Type*} [DecidableEq α] :
    ∀ (m : ℕ) (S : Set α) (_ : ¬ S.Countable) (F : α → Finset α)
      (_ : ∀ i ∈ S, (F i).card = m),
      ∃ (J : Set α) (R : Finset α),
        J ⊆ S ∧ J.Infinite ∧
        (∀ i ∈ J, R ⊆ F i) ∧
        (∀ i ∈ J, ∀ j ∈ J, i ≠ j → F i ∩ F j = R)
  | 0, S, hS_unc, F, hcard => by
      refine ⟨S, ∅, Subset.rfl, fun hfin => hS_unc hfin.countable,
        fun _ _ => Finset.empty_subset _, fun i hi j hj _ => ?_⟩
      have hi0 : F i = ∅ := Finset.card_eq_zero.mp (hcard i hi)
      have hj0 : F j = ∅ := Finset.card_eq_zero.mp (hcard j hj)
      rw [hi0, hj0, Finset.inter_empty]
  | m + 1, S, hS_unc, F, hcard => by
      by_cases hex : ∃ x : α, ¬ ({ i ∈ S | x ∈ F i }).Countable
      · obtain ⟨x, hx_unc⟩ := hex
        let Sx : Set α := { i ∈ S | x ∈ F i }
        let F' : α → Finset α := fun i => (F i).erase x
        have hcard' : ∀ i ∈ Sx, (F' i).card = m := by
          intro i hi
          have h1 : (F' i).card = (F i).card - 1 := Finset.card_erase_of_mem hi.2
          rw [hcard i hi.1] at h1
          exact h1
        obtain ⟨J, R', hJSx, hJinf, hR'sub, hR'inter⟩ :=
          delta_system_of_card_eq m Sx hx_unc F' hcard'
        refine ⟨J, insert x R', hJSx.trans (fun _ h => h.1), hJinf, ?_, ?_⟩
        · intro i hi y hy
          rcases Finset.mem_insert.mp hy with rfl | hyR'
          · exact (hJSx hi).2
          · exact Finset.mem_of_mem_erase (hR'sub i hi hyR')
        · intro i hi j hj hne
          ext y
          simp only [Finset.mem_inter, Finset.mem_insert]
          by_cases hyx : y = x
          · subst hyx
            simp [(hJSx hi).2, (hJSx hj).2]
          · have hmem : y ∈ F' i ∩ F' j ↔ y ∈ R' := by rw [hR'inter i hi j hj hne]
            simp only [F', Finset.mem_inter, Finset.mem_erase, hyx, ne_eq, not_false_eq_true,
              true_and] at hmem
            simp [hyx, hmem]
      · push Not at hex
        have hstep : ∀ (l : List α),
            ∃ a ∈ S, ∀ b ∈ l, Disjoint (F b) (F a) := by
          intro l
          let U : Set α := ⋃ b ∈ l, (F b : Set α)
          have hU_count : U.Countable :=
            ((l.toFinset.countable_toSet).biUnion fun b _ => (F b).countable_toSet).mono fun x hx => by
              simp only [U, mem_iUnion, Finset.mem_coe] at hx ⊢
              obtain ⟨b, hb, hxb⟩ := hx
              exact ⟨b, List.mem_toFinset.mpr hb, hxb⟩
          let Bad : Set α := ⋃ x ∈ U, { i ∈ S | x ∈ F i }
          have hBad_count : Bad.Countable := hU_count.biUnion (fun x _ => hex x)
          have hne : (S \ Bad).Nonempty := by
            by_contra hemp
            rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hemp
            exact hS_unc (hBad_count.mono hemp)
          obtain ⟨a, haS, haBad⟩ := hne
          refine ⟨a, haS, fun b hb => Finset.disjoint_left.mpr fun x hxb hxa => haBad ?_⟩
          refine mem_biUnion ?_ ⟨haS, hxa⟩
          exact mem_iUnion₂.mpr ⟨b, hb, hxb⟩
        -- Build an infinite pairwise-disjoint sequence recursively via `Nat.rec`
        let seq : ℕ → List α := Nat.rec [] (fun _ l => Classical.choose (hstep l) :: l)
        have hseq_spec : ∀ n,
            (∀ a ∈ seq n, a ∈ S) ∧
            (∀ i : Fin (seq n).length, ∀ j : Fin (seq n).length,
              i ≠ j → Disjoint (F ((seq n).get i)) (F ((seq n).get j))) ∧
            (seq n).length = n := by
          intro n
          induction n with
          | zero =>
            refine ⟨fun _ h => by simp [seq] at h, fun i => by exact Fin.elim0 i, rfl⟩
          | succ n ih =>
            obtain ⟨ih_mem, ih_disj, ih_len⟩ := ih
            let a := Classical.choose (hstep (seq n))
            have ha : a ∈ S ∧ ∀ b ∈ seq n, Disjoint (F b) (F a) :=
              Classical.choose_spec (hstep (seq n))
            have hseq_eq : seq (n + 1) = a :: seq n := rfl
            refine ⟨?_, ?_, by simp [hseq_eq, ih_len]⟩
            · intro x hx
              rw [hseq_eq, List.mem_cons] at hx
              rcases hx with rfl | hx
              · exact ha.1
              · exact ih_mem x hx
            · intro i j hij
              rcases i with ⟨i, hi⟩
              rcases j with ⟨j, hj⟩
              cases i with
              | zero =>
                cases j with
                | zero => exact (hij rfl).elim
                | succ j =>
                  have hmemj : (seq n).get ⟨j, Nat.lt_of_succ_lt_succ hj⟩ ∈ seq n :=
                    List.get_mem _ _
                  exact (ha.2 _ hmemj).symm
              | succ i =>
                cases j with
                | zero =>
                  have hmemi : (seq n).get ⟨i, Nat.lt_of_succ_lt_succ hi⟩ ∈ seq n :=
                    List.get_mem _ _
                  exact ha.2 _ hmemi
                | succ j =>
                  have hne' : (⟨i, Nat.lt_of_succ_lt_succ hi⟩ : Fin (seq n).length) ≠
                      ⟨j, Nat.lt_of_succ_lt_succ hj⟩ := by
                    intro heq
                    apply hij
                    exact Fin.ext (congrArg (· + 1) (congrArg Fin.val heq))
                  exact ih_disj _ _ hne'
        let f : ℕ → α := fun n => Classical.choose (hstep (seq n))
        have hf_mem : ∀ n, f n ∈ S := fun n => (Classical.choose_spec (hstep (seq n))).1
        have hf_disj_lt : ∀ {k n : ℕ}, k < n → Disjoint (F (f k)) (F (f n)) := by
          intro k n hkn
          have hmem_k : f k ∈ seq n := by
            have hstep_mem : ∀ d, f k ∈ seq (k + 1 + d) := by
              intro d
              induction d with
              | zero => exact List.mem_cons_self
              | succ d ihd => exact List.mem_cons_of_mem _ ihd
            have heq : k + 1 + (n - (k + 1)) = n := by omega
            exact heq ▸ hstep_mem (n - (k + 1))
          exact (Classical.choose_spec (hstep (seq n))).2 (f k) hmem_k
        have hf_inj : Function.Injective f := by
          intro k n hkn
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have hd := hf_disj_lt hlt
            rw [hkn] at hd
            have hne0 : (F (f n)).Nonempty :=
              Finset.card_pos.mp (by rw [hcard (f n) (hf_mem n)]; omega)
            obtain ⟨x, hx⟩ := hne0
            exact Finset.disjoint_left.mp hd hx hx
          · have hd := hf_disj_lt hgt
            rw [hkn] at hd
            have hne0 : (F (f n)).Nonempty :=
              Finset.card_pos.mp (by rw [hcard (f n) (hf_mem n)]; omega)
            obtain ⟨x, hx⟩ := hne0
            exact Finset.disjoint_left.mp hd hx hx
        refine ⟨range f, ∅, ?_, infinite_range_of_injective hf_inj,
          fun _ _ => Finset.empty_subset _, ?_⟩
        · rintro _ ⟨n, rfl⟩; exact hf_mem n
        · rintro _ ⟨k, rfl⟩ _ ⟨n, rfl⟩ hne
          have hkn : k ≠ n := fun h => hne (congrArg f h)
          rcases lt_or_gt_of_ne hkn with hlt | hgt
          · exact Finset.disjoint_iff_inter_eq_empty.mp (hf_disj_lt hlt)
          · exact Finset.disjoint_iff_inter_eq_empty.mp (hf_disj_lt hgt).symm

/-- Uncountable family of finite sets over `α` contains an infinite `Δ`-system. -/
theorem exists_infinite_delta_system {α : Type*} [DecidableEq α] (S : Set α)
    (hS_unc : ¬ S.Countable) (F : α → Finset α) :
    ∃ (J : Set α) (R : Finset α),
      J ⊆ S ∧ J.Infinite ∧
      (∀ i ∈ J, R ⊆ F i) ∧
      (∀ i ∈ J, ∀ j ∈ J, i ≠ j → F i ∩ F j = R) := by
  have hex : ∃ m : ℕ, ¬ ({ i ∈ S | (F i).card = m }).Countable := by
    by_contra hall
    push Not at hall
    apply hS_unc
    have hsub : S ⊆ ⋃ m : ℕ, { i ∈ S | (F i).card = m } :=
      fun i hi => mem_iUnion.mpr ⟨(F i).card, hi, rfl⟩
    exact (countable_iUnion hall).mono hsub
  obtain ⟨m, hm⟩ := hex
  obtain ⟨J, R, hJsub, hJinf, hRsub, hRinter⟩ :=
    delta_system_of_card_eq m { i ∈ S | (F i).card = m } hm F (fun _ h => h.2)
  exact ⟨J, R, hJsub.trans (fun _ h => h.1), hJinf, hRsub, hRinter⟩

end DeltaSystem

section CantorCube

/-- In the Cantor cube `I → Bool` for any uncountable index type `I`,
the zero point `fun _ => false` does NOT admit a closure-preserving open outer base. -/
theorem cantorCube_not_hasCPOuterBase {I : Type*} (hI : ¬ Countable I) :
    ¬ Defs.D_0001.HasCPOuterBase (fun _ : I => false) := by
  classical
  rintro ⟨𝓥, h𝓥_open, h𝓥_base, h𝓥_cp⟩
  have hU_open : ∀ i : I, IsOpen ({ f : I → Bool | f i = false }) := fun i =>
    show IsOpen ((fun f : I → Bool => f i) ⁻¹' {false}) from
      (isOpen_discrete ({false} : Set Bool)).preimage (continuous_apply i)
  have hV_ex : ∀ i : I, ∃ V ∈ 𝓥, V ⊆ { f : I → Bool | f i = false } :=
    fun i => h𝓥_base _ (hU_open i) rfl
  choose V hV_mem hV_sub using hV_ex
  have hF_ex : ∀ i : I, ∃ F : Finset I,
      { f : I → Bool | ∀ j ∈ F, f j = false } ⊆ V i := by
    intro i
    have hopen := (h𝓥_open (V i) (hV_mem i)).1
    have h0 := (h𝓥_open (V i) (hV_mem i)).2
    rw [isOpen_pi_iff] at hopen
    obtain ⟨F, t, ht, hsub⟩ := hopen (fun _ => false) h0
    refine ⟨F, fun f hf => hsub ?_⟩
    intro j hj
    have hfj : f j = false := hf j hj
    rw [hfj]
    exact (ht j hj).2
  choose F hF_sub using hF_ex
  have huniv_unc : ¬ (univ : Set I).Countable := by
    intro hc
    exact hI (countable_univ_iff.mp hc)
  obtain ⟨J, R, -, hJinf, hRsub, hRinter⟩ :=
    exists_infinite_delta_system (univ : Set I) huniv_unc F
  let J' : Set I := J \ (R : Set I)
  have hJ'inf : J'.Infinite := hJinf.sdiff R.finite_toSet
  let zStar : I → Bool := fun j => if j ∈ R then false else true
  let 𝓖 : Set (Set (I → Bool)) := V '' J'
  have h𝓖_sub : 𝓖 ⊆ 𝓥 := by
    rintro _ ⟨i, _, rfl⟩
    exact hV_mem i
  have hz_cl : zStar ∈ closure (⋃₀ 𝓖) := by
    rw [mem_closure_iff]
    intro O hO hzO
    rw [isOpen_pi_iff] at hO
    obtain ⟨K, t, ht, hKsub⟩ := hO zStar hzO
    -- Only finitely many `i ∈ J'` can have `F i` intersecting `K \ R`
    let Bad : Set I := { i ∈ J' | ∃ k ∈ K \ R, k ∈ F i }
    have hBad_fin : Bad.Finite := by
      have hsub : Bad ⊆ ⋃ k ∈ (K \ R : Finset I), { i ∈ J' | k ∈ F i } := by
        intro i ⟨hiJ', k, hkKR, hkFi⟩
        exact mem_biUnion hkKR ⟨hiJ', hkFi⟩
      refine ((K \ R).finite_toSet.biUnion fun k hk => ?_).subset hsub
      have hkR : k ∉ R := (Finset.mem_sdiff.mp hk).2
      refine Set.Subsingleton.finite fun i₁ hi₁ i₂ hi₂ => ?_
      by_contra hne
      have hinter := hRinter i₁ hi₁.1.1 i₂ hi₂.1.1 hne
      have hk_in : k ∈ F i₁ ∩ F i₂ := Finset.mem_inter.mpr ⟨hi₁.2, hi₂.2⟩
      rw [hinter] at hk_in
      exact hkR hk_in
    obtain ⟨i, hiJ', hiNotBad⟩ := (hJ'inf.sdiff hBad_fin).nonempty
    let f : I → Bool := fun j => if j ∈ F i then false else true
    have hfVi : f ∈ V i := hF_sub i (fun j hj => by simp [f, hj])
    have hfO : f ∈ O := by
      apply hKsub
      intro k hkK
      have hfk : f k = zStar k := by
        by_cases hkR : k ∈ R
        · have hkFi : k ∈ F i := hRsub i hiJ'.1 hkR
          simp [f, zStar, hkR, hkFi]
        · have hkNotFi : k ∉ F i := by
            intro hkFi
            exact hiNotBad ⟨hiJ', k, Finset.mem_sdiff.mpr ⟨hkK, hkR⟩, hkFi⟩
          simp [f, zStar, hkR, hkNotFi]
      rw [hfk]
      exact (ht k hkK).2
    exact ⟨f, hfO, V i, ⟨i, hiJ', rfl⟩, hfVi⟩
  rw [h𝓥_cp 𝓖 h𝓖_sub] at hz_cl
  obtain ⟨_, ⟨_, ⟨i, hiJ', rfl⟩, rfl⟩, hzi⟩ := hz_cl
  have hclosed : IsClosed ({ f : I → Bool | f i = false }) :=
    show IsClosed ((fun f : I → Bool => f i) ⁻¹' {false}) from
      (isClosed_discrete ({false} : Set Bool)).preimage (continuous_apply i)
  have hz_false : zStar i = false := hclosed.closure_subset (closure_mono (hV_sub i) hzi)
  have hiR : i ∉ R := hiJ'.2
  simp [zStar, hiR] at hz_false

end CantorCube

section BoxFanConstruction

/-- `BoxFan I := Option (ℕ × (I → Bool))` attaches a countable sequence of clopen
copies of the Cantor cube `I → Bool` converging to the apex `none`. -/
abbrev BoxFan (I : Type) : Type := Option (ℕ × (I → Bool))

/-- The `n`-th clopen shrinking neighborhood of the apex `none` in `BoxFan I`. -/
def boxFanW (I : Type) (n : ℕ) : Set (BoxFan I) :=
  { x | match x with | none => True | some (k, _) => n ≤ k }

/-- The box-fan topology on `BoxFan I`:
* Each slice `{ some (k, f) | f ∈ U }` (with `U` open in `I → Bool`) is open.
* A set containing `none` is open iff there exists `N` such that for every `k ≥ N`,
  the slice `{ f | some (k, f) ∈ U }` is open and contains `fun _ => false`, and every
  `some (k, f) ∈ U` has an open slice neighborhood inside `U`. -/
@[instance_reducible]
def boxFanTopology (I : Type) : TopologicalSpace (BoxFan I) where
  IsOpen U :=
    (∀ k f, some (k, f) ∈ U →
      ∃ V : Set (I → Bool), IsOpen V ∧ f ∈ V ∧ ∀ g ∈ V, some (k, g) ∈ U) ∧
    (none ∈ U →
      ∃ N : ℕ, ∀ k, N ≤ k →
        ∃ V : Set (I → Bool), IsOpen V ∧ (fun _ => false) ∈ V ∧
          ∀ g ∈ V, some (k, g) ∈ U)
  isOpen_univ :=
    ⟨fun _ _ _ => ⟨univ, isOpen_univ, trivial, fun _ _ => trivial⟩,
     fun _ => ⟨0, fun _ _ => ⟨univ, isOpen_univ, trivial, fun _ _ => trivial⟩⟩⟩
  isOpen_inter U₁ U₂ h₁ h₂ := by
    refine ⟨?_, ?_⟩
    · intro k f ⟨hf1, hf2⟩
      obtain ⟨V₁, hV₁, hfV₁, hsub₁⟩ := h₁.1 k f hf1
      obtain ⟨V₂, hV₂, hfV₂, hsub₂⟩ := h₂.1 k f hf2
      exact ⟨V₁ ∩ V₂, hV₁.inter hV₂, ⟨hfV₁, hfV₂⟩, fun g ⟨h1, h2⟩ => ⟨hsub₁ g h1, hsub₂ g h2⟩⟩
    · intro ⟨hnone1, hnone2⟩
      obtain ⟨N₁, hN₁⟩ := h₁.2 hnone1
      obtain ⟨N₂, hN₂⟩ := h₂.2 hnone2
      refine ⟨max N₁ N₂, fun k hk => ?_⟩
      obtain ⟨V₁, hV₁, h0V₁, hsub₁⟩ := hN₁ k (le_trans (le_max_left N₁ N₂) hk)
      obtain ⟨V₂, hV₂, h0V₂, hsub₂⟩ := hN₂ k (le_trans (le_max_right N₁ N₂) hk)
      exact ⟨V₁ ∩ V₂, hV₁.inter hV₂, ⟨h0V₁, h0V₂⟩, fun g ⟨h1, h2⟩ => ⟨hsub₁ g h1, hsub₂ g h2⟩⟩
  isOpen_sUnion S hS := by
    refine ⟨?_, ?_⟩
    · intro k f ⟨U, hUS, hfU⟩
      obtain ⟨V, hV, hfV, hsub⟩ := (hS U hUS).1 k f hfU
      exact ⟨V, hV, hfV, fun g hg => ⟨U, hUS, hsub g hg⟩⟩
    · intro ⟨U, hUS, hnoneU⟩
      obtain ⟨N, hN⟩ := (hS U hUS).2 hnoneU
      refine ⟨N, fun k hk => ?_⟩
      obtain ⟨V, hV, h0V, hsub⟩ := hN k hk
      exact ⟨V, hV, h0V, fun g hg => ⟨U, hUS, hsub g hg⟩⟩

/-- Slice sets `{ some (k, f) | f ∈ V }` are open whenever `V` is open in `I → Bool`. -/
theorem boxFan_slice_isOpen (I : Type) (k : ℕ) {V : Set (I → Bool)} (hV : IsOpen V) :
    @IsOpen (BoxFan I) (boxFanTopology I) { x | ∃ f ∈ V, x = some (k, f) } := by
  refine ⟨?_, fun ⟨_, _, h⟩ => by cases h⟩
  rintro k' f ⟨f', hf'V, heq⟩
  cases heq
  exact ⟨V, hV, hf'V, fun g hg => ⟨g, hg, rfl⟩⟩

/-- Basic clopen neighborhoods of `none` in `BoxFan I`:
`{none} ∪ { some (k, f) | N ≤ k ∧ f ∈ φ k }`. -/
def boxFanBasic (I : Type) (N : ℕ) (φ : ℕ → Set (I → Bool)) : Set (BoxFan I) :=
  { x | match x with | none => True | some (k, f) => N ≤ k ∧ f ∈ φ k }

theorem boxFanBasic_clopen (I : Type) (N : ℕ) (φ : ℕ → Set (I → Bool))
    (hφ_open : ∀ k, IsOpen (φ k)) (hφ_closed : ∀ k, IsClosed (φ k))
    (hφ_zero : ∀ k, (fun _ => false) ∈ φ k) :
    let : TopologicalSpace (BoxFan I) := boxFanTopology I
    IsOpen (boxFanBasic I N φ) ∧ IsClosed (boxFanBasic I N φ) := by
  let : TopologicalSpace (BoxFan I) := boxFanTopology I
  refine ⟨?_, ?_⟩
  · refine ⟨?_, fun _ => ⟨N, fun k hk => ⟨φ k, hφ_open k, hφ_zero k, fun g hg => ⟨hk, hg⟩⟩⟩⟩
    intro k f ⟨hk, hf⟩
    exact ⟨φ k, hφ_open k, hf, fun g hg => ⟨hk, hg⟩⟩
  · rw [← isOpen_compl_iff]
    refine ⟨?_, fun h => absurd trivial h⟩
    intro k f hnot
    by_cases hk : N ≤ k
    · have hfnot : f ∈ (φ k)ᶜ := fun hf => hnot ⟨hk, hf⟩
      exact ⟨(φ k)ᶜ, (hφ_closed k).isOpen_compl, hfnot, fun g hg ⟨_, hgφ⟩ => hg hgφ⟩
    · exact ⟨univ, isOpen_univ, trivial, fun _ _ ⟨hk', _⟩ => hk hk'⟩

/-- Every `boxFanW I n` is clopen and contains `none`. -/
theorem boxFan_W_clopen (I : Type) (n : ℕ) :
    let : TopologicalSpace (BoxFan I) := boxFanTopology I
    IsOpen (boxFanW I n) ∧ IsClosed (boxFanW I n) ∧ (none : BoxFan I) ∈ boxFanW I n := by
  let : TopologicalSpace (BoxFan I) := boxFanTopology I
  have hEq : boxFanW I n = boxFanBasic I n (fun _ => univ) := by
    ext x; cases x <;> simp [boxFanW, boxFanBasic]
  rw [hEq]
  have hcl := boxFanBasic_clopen I n (fun _ => univ)
    (fun _ => isOpen_univ) (fun _ => isClosed_univ) (fun _ => trivial)
  exact ⟨hcl.1, hcl.2, trivial⟩

/-- The intersection of `boxFanW I n` over all `n : ℕ` is `{none}`. -/
theorem boxFan_W_inter (I : Type) :
    (⋂ n : ℕ, boxFanW I n) = {(none : BoxFan I)} := by
  ext x
  cases x with
  | none => simp [boxFanW]
  | some p =>
    rcases p with ⟨k, f⟩
    simp only [mem_iInter, mem_singleton_iff, reduceCtorEq, iff_false, not_forall]
    exact ⟨k + 1, by simp [boxFanW]⟩

/-- `BoxFan I` is a `T3Space` (zero-dimensional regular `T1Space`). -/
theorem boxFan_t3Space (I : Type) :
    @T3Space (BoxFan I) (boxFanTopology I) := by
  classical
  let : TopologicalSpace (BoxFan I) := boxFanTopology I
  have hT1 : T1Space (BoxFan I) := by
    refine ⟨fun x => ?_⟩
    rw [← isOpen_compl_iff]
    cases x with
    | none =>
      refine ⟨fun k f _ => ⟨univ, isOpen_univ, trivial, fun _ _ h => by cases h⟩,
        fun h => absurd rfl h⟩
    | some p =>
      rcases p with ⟨k₀, f₀⟩
      refine ⟨?_, ?_⟩
      · intro k f hne
        by_cases hk : k = k₀
        · subst hk
          have hfne : f ≠ f₀ := fun h => hne (by simp [h])
          refine ⟨{f₀}ᶜ, isClosed_singleton.isOpen_compl, hfne, fun g hg heq => ?_⟩
          cases heq
          exact hg rfl
        · refine ⟨univ, isOpen_univ, trivial, fun g _ heq => ?_⟩
          cases heq
          exact hk rfl
      · intro _
        refine ⟨k₀ + 1, fun k hk => ⟨univ, isOpen_univ, trivial, fun g _ heq => ?_⟩⟩
        cases heq
        omega
  have hReg : RegularSpace (BoxFan I) := by
    refine RegularSpace.of_exists_mem_nhds_isClosed_subset fun x s hs => ?_
    obtain ⟨U, hUs, hUopen, hxU⟩ := mem_nhds_iff.mp hs
    cases x with
    | none =>
      obtain ⟨N, hN⟩ := hUopen.2 hxU
      have hcl_ex : ∀ k : ℕ, ∃ C : Set (I → Bool),
          IsOpen C ∧ IsClosed C ∧ (fun _ => false) ∈ C ∧
          (N ≤ k → ∀ g ∈ C, some (k, g) ∈ U) := by
        intro k
        by_cases hk : N ≤ k
        · obtain ⟨V, hV, h0V, hVsub⟩ := hN k hk
          rw [isOpen_pi_iff] at hV
          obtain ⟨F, t, ht, hFsub⟩ := hV (fun _ => false) h0V
          let C : Set (I → Bool) := { g | ∀ j ∈ F, g j = false }
          have hC_eq : C = ⋂ j ∈ F, (fun g : I → Bool => g j) ⁻¹' {false} := by
            ext g; simp [C]
          have hC_open : IsOpen C := by
            rw [hC_eq]
            exact isOpen_biInter_finset fun j _ =>
              (isOpen_discrete ({false} : Set Bool)).preimage (continuous_apply j)
          have hC_closed : IsClosed C := by
            rw [hC_eq]
            exact isClosed_biInter fun j _ =>
              (isClosed_discrete ({false} : Set Bool)).preimage (continuous_apply j)
          refine ⟨C, hC_open, hC_closed, fun _ _ => rfl, fun _ g hg => hVsub g (hFsub ?_)⟩
          intro j hj
          rw [hg j hj]
          exact (ht j hj).2
        · exact ⟨univ, isOpen_univ, isClosed_univ, trivial, fun h => (hk h).elim⟩
      choose φ hφ_open hφ_closed hφ_zero hφ_sub using hcl_ex
      have hcl := boxFanBasic_clopen I N φ hφ_open hφ_closed hφ_zero
      refine ⟨boxFanBasic I N φ, hcl.1.mem_nhds trivial, hcl.2, ?_⟩
      intro y hy
      apply hUs
      cases y with
      | none => exact hxU
      | some p => exact hφ_sub p.1 hy.1 p.2 hy.2
    | some p =>
      rcases p with ⟨k, f⟩
      obtain ⟨V, hV, hfV, hVsub⟩ := hUopen.1 k f hxU
      rw [isOpen_pi_iff] at hV
      obtain ⟨F, t, ht, hFsub⟩ := hV f hfV
      let C : Set (I → Bool) := { g | ∀ j ∈ F, g j = f j }
      have hC_eq : C = ⋂ j ∈ F, (fun g : I → Bool => g j) ⁻¹' {f j} := by
        ext g; simp [C]
      have hC_open : IsOpen C := by
        rw [hC_eq]
        exact isOpen_biInter_finset fun j _ =>
          (isOpen_discrete ({f j} : Set Bool)).preimage (continuous_apply j)
      have hC_closed : IsClosed C := by
        rw [hC_eq]
        exact isClosed_biInter fun j _ =>
          (isClosed_discrete ({f j} : Set Bool)).preimage (continuous_apply j)
      let T : Set (BoxFan I) := { y | ∃ g ∈ C, y = some (k, g) }
      have hT_open : IsOpen T := boxFan_slice_isOpen I k hC_open
      have hT_closed : IsClosed T := by
        rw [← isOpen_compl_iff]
        refine ⟨?_, ?_⟩
        · intro k' g hgnot
          by_cases hk : k' = k
          · subst hk
            have hgC : g ∈ Cᶜ := fun h => hgnot ⟨g, h, rfl⟩
            refine ⟨Cᶜ, hC_closed.isOpen_compl, hgC, fun g' hg' ⟨g'', hg'', heq⟩ => ?_⟩
            cases heq
            exact hg' hg''
          · refine ⟨univ, isOpen_univ, trivial, fun g' _ ⟨g'', _, heq⟩ => ?_⟩
            cases heq
            exact hk rfl
        · intro _
          refine ⟨k + 1, fun k' hk' => ⟨univ, isOpen_univ, trivial, fun g' _ ⟨g'', _, heq⟩ => ?_⟩⟩
          cases heq
          omega
      refine ⟨T, hT_open.mem_nhds ⟨f, fun _ _ => rfl, rfl⟩, hT_closed, ?_⟩
      rintro _ ⟨g, hgC, rfl⟩
      apply hUs
      apply hVsub g
      apply hFsub
      intro j hj
      rw [hgC j hj]
      exact (ht j hj).2
  exact ⟨⟩

/-- Main Theorem: For any uncountable `I` (e.g. `I = ℕ → Bool`), the apex `none` of
`BoxFan I` does NOT admit a closure-preserving open outer base (`¬ HasCPOuterBase none`). -/
theorem boxFan_not_hasCPOuterBase {I : Type} (hI : ¬ Countable I) :
    ¬ @Defs.D_0001.HasCPOuterBase (BoxFan I) (boxFanTopology I) none := by
  classical
  let : TopologicalSpace (BoxFan I) := boxFanTopology I
  rintro ⟨𝓥, h𝓥_open, h𝓥_base, h𝓥_cp⟩
  let U : I → Set (BoxFan I) := fun i =>
    boxFanBasic I 0 (fun _ => { f : I → Bool | f i = false })
  have hU_clopen : ∀ i : I, IsOpen (U i) ∧ IsClosed (U i) := fun i =>
    boxFanBasic_clopen I 0 _
      (fun _ => show IsOpen ((fun f : I → Bool => f i) ⁻¹' {false}) from
        (isOpen_discrete ({false} : Set Bool)).preimage (continuous_apply i))
      (fun _ => show IsClosed ((fun f : I → Bool => f i) ⁻¹' {false}) from
        (isClosed_discrete ({false} : Set Bool)).preimage (continuous_apply i))
      (fun _ => rfl)
  have hV_ex : ∀ i : I, ∃ V ∈ 𝓥, V ⊆ U i :=
    fun i => h𝓥_base (U i) (hU_clopen i).1 trivial
  choose V hV_mem hV_sub using hV_ex
  have hN_ex : ∀ i : I, ∃ N : ℕ, ∃ F : Finset I,
      ∀ g : I → Bool, (∀ j ∈ F, g j = false) → some (N, g) ∈ V i := by
    intro i
    obtain ⟨N, hN⟩ := (h𝓥_open (V i) (hV_mem i)).1.2 (h𝓥_open (V i) (hV_mem i)).2
    obtain ⟨W, hW_open, h0W, hW_sub⟩ := hN N le_rfl
    rw [isOpen_pi_iff] at hW_open
    obtain ⟨F, t, ht, hFsub⟩ := hW_open (fun _ => false) h0W
    refine ⟨N, F, fun g hg => hW_sub g (hFsub ?_)⟩
    intro j hj
    rw [hg j hj]
    exact (ht j hj).2
  choose N F hNF using hN_ex
  have hexN : ∃ N₀ : ℕ, ¬ ({ i : I | N i = N₀ }).Countable := by
    by_contra hall
    push Not at hall
    have huniv : (univ : Set I).Countable :=
      (countable_iUnion hall).mono (fun i _ => mem_iUnion.mpr ⟨N i, rfl⟩)
    exact hI (countable_univ_iff.mp huniv)
  obtain ⟨N₀, hN₀_unc⟩ := hexN
  obtain ⟨J, R, hJsub, hJinf, hRsub, hRinter⟩ :=
    exists_infinite_delta_system { i : I | N i = N₀ } hN₀_unc F
  let J' : Set I := J \ (R : Set I)
  have hJ'inf : J'.Infinite := hJinf.sdiff R.finite_toSet
  let fStar : I → Bool := fun j => if j ∈ R then false else true
  let zStar : BoxFan I := some (N₀, fStar)
  let 𝓖 : Set (Set (BoxFan I)) := V '' J'
  have h𝓖_sub : 𝓖 ⊆ 𝓥 := by
    rintro _ ⟨i, _, rfl⟩
    exact hV_mem i
  have hz_cl : zStar ∈ closure (⋃₀ 𝓖) := by
    rw [mem_closure_iff]
    intro O hO hzO
    obtain ⟨W, hW_open, hfStarW, hW_sub⟩ := hO.1 N₀ fStar hzO
    rw [isOpen_pi_iff] at hW_open
    obtain ⟨K, t, ht, hKsub⟩ := hW_open fStar hfStarW
    let Bad : Set I := { i ∈ J' | ∃ k ∈ K \ R, k ∈ F i }
    have hBad_fin : Bad.Finite := by
      have hsub : Bad ⊆ ⋃ k ∈ (K \ R : Finset I), { i ∈ J' | k ∈ F i } := by
        intro i ⟨hiJ', k, hkKR, hkFi⟩
        exact mem_biUnion hkKR ⟨hiJ', hkFi⟩
      refine ((K \ R).finite_toSet.biUnion fun k hk => ?_).subset hsub
      have hkR : k ∉ R := (Finset.mem_sdiff.mp hk).2
      refine Set.Subsingleton.finite fun i₁ hi₁ i₂ hi₂ => ?_
      by_contra hne
      have hinter := hRinter i₁ hi₁.1.1 i₂ hi₂.1.1 hne
      have hk_in : k ∈ F i₁ ∩ F i₂ := Finset.mem_inter.mpr ⟨hi₁.2, hi₂.2⟩
      rw [hinter] at hk_in
      exact hkR hk_in
    obtain ⟨i, hiJ', hiNotBad⟩ := (hJ'inf.sdiff hBad_fin).nonempty
    let g : I → Bool := fun j => if j ∈ F i then false else true
    have hNi : N i = N₀ := hJsub hiJ'.1
    have hgVi : some (N₀, g) ∈ V i := hNi ▸ hNF i g (fun j hj => by simp [g, hj])
    have hgO : some (N₀, g) ∈ O := by
      apply hW_sub g
      apply hKsub
      intro k hkK
      have hgk : g k = fStar k := by
        by_cases hkR : k ∈ R
        · have hkFi : k ∈ F i := hRsub i hiJ'.1 hkR
          simp [g, fStar, hkR, hkFi]
        · have hkNotFi : k ∉ F i := by
            intro hkFi
            exact hiNotBad ⟨hiJ', k, Finset.mem_sdiff.mpr ⟨hkK, hkR⟩, hkFi⟩
          simp [g, fStar, hkR, hkNotFi]
      rw [hgk]
      exact (ht k hkK).2
    exact ⟨some (N₀, g), hgO, V i, ⟨i, hiJ', rfl⟩, hgVi⟩
  rw [h𝓥_cp 𝓖 h𝓖_sub] at hz_cl
  obtain ⟨_, ⟨_, ⟨i, hiJ', rfl⟩, rfl⟩, hzi⟩ := hz_cl
  have hzU : zStar ∈ U i := (hU_clopen i).2.closure_subset (closure_mono (hV_sub i) hzi)
  have hf_false : fStar i = false := hzU.2
  have hiR : i ∉ R := hiJ'.2
  simp [fStar, hiR] at hf_false

/-- Corollary 1: `BoxFan I` (for uncountable `I`) has `¬ HasSigmaCPLocalBase none`
(via `Proofs.L_0032`). -/
theorem boxFan_not_hasSigmaCPLocalBase {I : Type} (hI : ¬ Countable I) :
    ¬ @Defs.D_0010.HasSigmaCPLocalBase (BoxFan I) (boxFanTopology I) none := by
  let : TopologicalSpace (BoxFan I) := boxFanTopology I
  intro hsig
  exact boxFan_not_hasCPOuterBase hI
    (Proofs.L_0032.main (BoxFan I) none (boxFanW I) (boxFan_W_clopen I) (boxFan_W_inter I) hsig)

/-- Corollary 2: `BoxFan I` (for uncountable `I`) is a concrete zero-dimensional `T3Space`
that is NOT `M₁` (via `Proofs.L_0029` + `Proofs.L_0032`). -/
theorem boxFan_not_isM1 {I : Type} (hI : ¬ Countable I) :
    ¬ @MSpace.IsM1 (BoxFan I) (boxFanTopology I) := by
  let : TopologicalSpace (BoxFan I) := boxFanTopology I
  intro hm1
  exact boxFan_not_hasSigmaCPLocalBase hI (Proofs.L_0029.main (BoxFan I) hm1 none)

end BoxFanConstruction

end Research.ChenWangNonCPModel
