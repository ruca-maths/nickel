import Targets
import Defs.D_0001

namespace ChildResearch.CandidateReduction

open MSpace Set Topology

theorem closure_inter_clopen {X : Type} [TopologicalSpace X]
    (B C : Set X) (hCo : IsOpen C) (hCc : IsClosed C) :
    closure (B ∩ C) = closure B ∩ C := by
  apply Subset.antisymm
  · simpa only [hCc.closure_eq] using (closure_inter_subset (s := B) (t := C))
  · exact hCo.closure_inter

theorem cp_restrict {X : Type} [TopologicalSpace X]
    {F : Set (Set X)} (hF : ClosurePreserving F) (C : Set X)
    (hCo : IsOpen C) (hCc : IsClosed C) :
    ClosurePreserving ((fun B => B ∩ C) '' F) := by
  classical
  intro G hG
  let A : Set (Set X) := {B ∈ F | B ∩ C ∈ G}
  have hAsub : A ⊆ F := fun _ h => h.1
  have hUnion : ⋃₀ G = (⋃₀ A) ∩ C := by
    ext z
    constructor
    · rintro ⟨S, hS, hzS⟩
      obtain ⟨B, hB, rfl⟩ := hG hS
      exact ⟨mem_sUnion.mpr ⟨B, ⟨hB, hS⟩, hzS.1⟩, hzS.2⟩
    · rintro ⟨⟨B, hB, hzB⟩, hzC⟩
      exact mem_sUnion.mpr ⟨B ∩ C, hB.2, hzB, hzC⟩
  rw [hUnion, closure_inter_clopen _ _ hCo hCc, hF A hAsub]
  ext z
  constructor
  · rintro ⟨⟨_, ⟨B, hB, rfl⟩, hzB⟩, hzC⟩
    exact mem_sUnion.mpr ⟨closure (B ∩ C), ⟨B ∩ C, hB.2, rfl⟩,
      by rw [closure_inter_clopen _ _ hCo hCc]; exact ⟨hzB, hzC⟩⟩
  · rintro ⟨_, ⟨S, hS, rfl⟩, hzS⟩
    obtain ⟨B, hB, rfl⟩ := hG hS
    rw [closure_inter_clopen _ _ hCo hCc] at hzS
    exact ⟨mem_sUnion.mpr ⟨closure B, ⟨B, ⟨hB, hS⟩, rfl⟩, hzS.1⟩, hzS.2⟩

theorem cp_union_shrinking {X : Type} [TopologicalSpace X]
    (x : X) (F : ℕ → Set (Set X)) (g : ℕ → Set X)
    (hCP : ∀ n, ClosurePreserving (F n))
    (hx : ∀ n S, S ∈ F n → x ∈ S)
    (hclosed : ∀ n, IsClosed (g n)) (hanti : Antitone g)
    (hsep : ∀ y, y ≠ x → ∃ n, y ∉ g n)
    (hsub : ∀ n S, S ∈ F n → S ⊆ g n) :
    ClosurePreserving (⋃ n, F n) := by
  classical
  intro G hG
  apply Subset.antisymm
  · intro y hy
    by_cases hyx : y = x
    · subst y
      obtain ⟨z, S, hS, _⟩ := Set.Nonempty.of_closure ⟨x, hy⟩
      obtain ⟨n, hSn⟩ := mem_iUnion.mp (hG hS)
      exact mem_sUnion.mpr ⟨closure S, ⟨S, hS, rfl⟩, subset_closure (hx n S hSn)⟩
    · obtain ⟨m, hym⟩ := hsep y hyx
      let A : ℕ → Set (Set X) := fun n => G ∩ F n
      let E : Set X := ⋃ n ∈ Finset.range m, closure (⋃₀ A n)
      have hEc : IsClosed E := isClosed_biUnion_finset (fun _ _ => isClosed_closure)
      have hcover : ⋃₀ G ⊆ E ∪ g m := by
        rintro z ⟨S, hS, hzS⟩
        obtain ⟨n, hSn⟩ := mem_iUnion.mp (hG hS)
        by_cases hnm : n < m
        · exact Or.inl (mem_iUnion₂.mpr ⟨n, Finset.mem_range.mpr hnm,
            subset_closure (mem_sUnion.mpr ⟨S, ⟨hS, hSn⟩, hzS⟩)⟩)
        · exact Or.inr (hanti (Nat.le_of_not_gt hnm) (hsub n S hSn hzS))
      have hyE : y ∈ E := (closure_minimal hcover (hEc.union (hclosed m)) hy).resolve_right hym
      obtain ⟨n, _, hyn⟩ := mem_iUnion₂.mp hyE
      rw [hCP n (A n) (fun _ h => h.2)] at hyn
      obtain ⟨_, ⟨S, hS, rfl⟩, hyS⟩ := hyn
      exact mem_sUnion.mpr ⟨closure S, ⟨S, hS.1, rfl⟩, hyS⟩
  · rintro y ⟨_, ⟨S, hS, rfl⟩, hyS⟩
    exact closure_mono (subset_sUnion_of_mem hS) hyS

theorem m1_cp_open_of_clopen_sequence {X : Type} [TopologicalSpace X]
    (hM : IsM1 X) (x : X) (g : ℕ → Set X)
    (hgo : ∀ n, IsOpen (g n)) (hgc : ∀ n, IsClosed (g n))
    (hxg : ∀ n, x ∈ g n) (hanti : Antitone g)
    (hsep : ∀ y, y ≠ x → ∃ n, y ∉ g n) :
    ∃ K : Set (Set X),
      (∀ U ∈ K, IsOpen U ∧ x ∈ U) ∧
      (∀ U : Set X, IsOpen U → x ∈ U → ∃ V ∈ K, V ⊆ U) ∧
      ClosurePreserving K := by
  classical
  obtain ⟨_, B, hB, b, hCP, hb⟩ := hM
  have hbsub : ∀ n, b n ⊆ B := by
    intro n S hS
    rw [hb]
    exact mem_iUnion.mpr ⟨n, hS⟩
  let A : ℕ → Set (Set X) := fun n => {S ∈ b n | x ∈ S}
  let F : ℕ → Set (Set X) := fun n => (fun S => S ∩ g n) '' A n
  have hFcp : ∀ n, ClosurePreserving (F n) := by
    intro n
    apply cp_restrict (F := A n) _ (g n) (hgo n) (hgc n)
    intro G hG
    exact hCP n G (fun _ h => (hG h).1)
  refine ⟨⋃ n, F n, ?_, ?_, ?_⟩
  · intro U hU
    obtain ⟨n, S, hS, rfl⟩ := mem_iUnion.mp hU
    exact ⟨(hB.isOpen (hbsub n hS.1)).inter (hgo n), hS.2, hxg n⟩
  · intro U hU hxU
    obtain ⟨S, hS, hxS, hSU⟩ := hB.mem_nhds_iff.mp (hU.mem_nhds hxU)
    rw [hb] at hS
    obtain ⟨n, hSn⟩ := mem_iUnion.mp hS
    refine ⟨S ∩ g n, mem_iUnion.mpr ⟨n, S, ⟨hSn, hxS⟩, rfl⟩,
      inter_subset_left.trans hSU⟩
  · refine cp_union_shrinking x F g hFcp ?_ hgc hanti hsep ?_
    · rintro n U ⟨S, hS, rfl⟩
      exact ⟨hS.2, hxg n⟩
    · rintro n U ⟨S, _, rfl⟩
      exact inter_subset_right

/- A decreasing sequence is not necessary as input: finite intersections turn
any countable clopen family separating x from every other point into one.
-/
theorem m1_cp_open_of_clopen_separators {X : Type} [TopologicalSpace X]
    (hM : IsM1 X) (x : X) (g : ℕ → Set X)
    (hgo : ∀ n, IsOpen (g n)) (hgc : ∀ n, IsClosed (g n))
    (hxg : ∀ n, x ∈ g n)
    (hsep : ∀ y, y ≠ x → ∃ n, y ∉ g n) :
    ∃ K : Set (Set X),
      (∀ U ∈ K, IsOpen U ∧ x ∈ U) ∧
      (∀ U : Set X, IsOpen U → x ∈ U → ∃ V ∈ K, V ⊆ U) ∧
      ClosurePreserving K := by
  let c : ℕ → Set X := fun n => ⋂ k ≤ n, g k
  apply m1_cp_open_of_clopen_sequence hM x c
  · intro n
    exact (finite_le_nat n).isOpen_biInter (fun k _ => hgo k)
  · intro n
    exact isClosed_iInter (fun k => isClosed_iInter (fun _ => hgc k))
  · intro n
    exact mem_iInter₂.mpr (fun k _ => hxg k)
  · intro m n hmn z hz
    exact mem_iInter₂.mpr (fun k hk => mem_iInter₂.mp hz k (hk.trans hmn))
  · intro y hy
    obtain ⟨n, hn⟩ := hsep y hy
    exact ⟨n, fun hyc => hn (mem_iInter₂.mp hyc n le_rfl)⟩


/-- Conditional counterexample reduction, with only one point required. -/
theorem refute_of_candidate (Y : Type) [TopologicalSpace Y]
    (hM3 : IsM3 Y) (x : Y) (g : ℕ → Set Y)
    (hgo : ∀ n, IsOpen (g n)) (hgc : ∀ n, IsClosed (g n))
    (hxg : ∀ n, x ∈ g n)
    (hsep : ∀ y, y ≠ x → ∃ n, y ∉ g n)
    (hno : ¬ ∃ K : Set (Set Y),
      (∀ U ∈ K, IsOpen U ∧ x ∈ U) ∧
      (∀ U : Set Y, IsOpen U → x ∈ U → ∃ V ∈ K, V ⊆ U) ∧
      ClosurePreserving K) :
    ¬ MSpace.Goals.Tinf_M3_imp_M1 := by
  intro h
  exact hno (m1_cp_open_of_clopen_separators (h Y hM3) x g hgo hgc hxg hsep)

/-- Proposed replacement for the negative reduction R_0005. -/
def HasWitness : Prop :=
  ∃ (Y : Type) (τ : TopologicalSpace Y),
    @IsM3 Y τ ∧
    ∃ (x : Y) (g : ℕ → Set Y),
      (∀ n, @IsOpen Y τ (g n)) ∧ (∀ n, @IsClosed Y τ (g n)) ∧
      (∀ n, x ∈ g n) ∧ (∀ y, y ≠ x → ∃ n, y ∉ g n) ∧
      ¬ @Defs.D_0001.HasCPOuterBase Y τ x

theorem refute_of_witness (h : HasWitness) : ¬ MSpace.Goals.Tinf_M3_imp_M1 := by
  obtain ⟨Y, τ, hM3, x, g, hgo, hgc, hxg, hsep, hno⟩ := h
  letI : TopologicalSpace Y := τ
  exact refute_of_candidate Y hM3 x g hgo hgc hxg hsep hno


example : (∃ (Y : Type) (τ : TopologicalSpace Y),
    @IsM3 Y τ ∧
    ∃ (x : Y) (g : ℕ → Set Y),
      (∀ n, @IsOpen Y τ (g n)) ∧ (∀ n, @IsClosed Y τ (g n)) ∧
      (∀ n, x ∈ g n) ∧ (∀ y, y ≠ x → ∃ n, y ∉ g n) ∧
      ¬ (∃ K : Set (Set Y),
        (∀ U ∈ K, @IsOpen Y τ U ∧ x ∈ U) ∧
        (∀ U : Set Y, @IsOpen Y τ U → x ∈ U → ∃ V ∈ K, V ⊆ U) ∧
        @ClosurePreserving Y τ K)) → ¬ MSpace.Goals.Tinf_M3_imp_M1 :=
  refute_of_witness

end ChildResearch.CandidateReduction
