import Mathlib.Topology.Basic
import Mathlib.Topology.Maps.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Finset.Nat
import Targets
import Defs.D_0001

namespace Work.L0031Shell

open Set TopologicalSpace MSpace Defs.D_0001

section ClopenShell

variable {Y : Type*} [TopologicalSpace Y]

/-- 単調減少化した clopen 列 W' -/
def decClopen (W : ℕ → Set Y) : ℕ → Set Y
  | 0 => Set.univ
  | n + 1 => ⋂ i ≤ n, W i

/-- 第 n 殻 S_n = W'_n \ W'_{n+1} -/
def shell (W : ℕ → Set Y) (n : ℕ) : Set Y :=
  decClopen W n \ decClopen W (n + 1)

omit [TopologicalSpace Y] in
lemma decClopen_antitone (W : ℕ → Set Y) : Antitone (decClopen W) := by
  intro m n hmn
  induction hmn with
  | refl => exact Subset.rfl
  | @step k _ ih =>
    refine Subset.trans ?_ ih
    cases k with
    | zero => exact subset_univ _
    | succ j =>
      intro x hx
      simp only [decClopen, mem_iInter] at hx ⊢
      intro i hi
      exact hx i (Nat.le_succ_of_le hi)

lemma decClopen_isClopen {W : ℕ → Set Y}
    (hW : ∀ n, IsOpen (W n) ∧ IsClosed (W n)) (n : ℕ) :
    IsOpen (decClopen W n) ∧ IsClosed (decClopen W n) := by
  cases n with
  | zero => exact ⟨isOpen_univ, isClosed_univ⟩
  | succ m =>
    have hopen : IsOpen (⋂ i ∈ Set.Iic m, W i) :=
      (Set.finite_Iic m).isOpen_biInter (fun i _ => (hW i).1)
    have hclosed : IsClosed (⋂ i ∈ Set.Iic m, W i) :=
      isClosed_biInter (fun i _ => (hW i).2)
    simpa [decClopen, Set.mem_Iic] using And.intro hopen hclosed

lemma shell_isClopen {W : ℕ → Set Y}
    (hW : ∀ n, IsOpen (W n) ∧ IsClosed (W n)) (n : ℕ) :
    IsOpen (shell W n) ∧ IsClosed (shell W n) := by
  have h1 := decClopen_isClopen hW n
  have h2 := decClopen_isClopen hW (n + 1)
  exact ⟨h1.1.sdiff h2.2, h1.2.sdiff h2.1⟩

/-- clopen 殻における閉包交換律: S ∩ cl(B) = cl(S ∩ B) -/
lemma clopen_inter_closure {S B : Set Y} (hSo : IsOpen S) (hSc : IsClosed S) :
    S ∩ closure B = closure (S ∩ B) := by
  apply Subset.antisymm
  · exact hSo.inter_closure
  · exact closure_minimal (inter_subset_inter_right S subset_closure) (hSc.inter isClosed_closure)

omit [TopologicalSpace Y] in
/-- 任意の x ≠ y はある殻 S_n に属する -/
lemma exists_shell_of_ne {W : ℕ → Set Y} {y x : Y}
    (hinter : (⋂ n, W n) = {y}) (hxy : x ≠ y) :
    ∃ n, x ∈ shell W n := by
  classical
  have hnot : ∃ k, x ∉ decClopen W k := by
    by_contra hall
    push Not at hall
    have hmem : x ∈ ⋂ n, W n := by
      rw [mem_iInter]
      intro n
      have := hall (n + 1)
      simp only [decClopen, mem_iInter] at this
      exact this n le_rfl
    rw [hinter, mem_singleton_iff] at hmem
    exact hxy hmem
  let k0 := Nat.find hnot
  have hk0_not : x ∉ decClopen W k0 := Nat.find_spec hnot
  have hk0_pos : 0 < k0 := by
    by_contra h0
    have : k0 = 0 := Nat.eq_zero_of_not_pos h0
    rw [this] at hk0_not
    exact hk0_not (mem_univ x)
  refine ⟨k0 - 1, ?_, ?_⟩
  · have hlt : k0 - 1 < k0 := Nat.sub_lt hk0_pos Nat.one_pos
    exact Classical.not_not.mp (Nat.find_min hnot hlt)
  · rwa [Nat.sub_add_cancel hk0_pos]

/-- 殻上での部分空間 CP 性（Y の部分集合の言葉で表現） -/
def ClosurePreservingOn (S : Set Y) (𝓥 : Set (Set Y)) : Prop :=
  ∀ 𝓖 ⊆ 𝓥, closure (⋃₀ ((fun V => S ∩ V) '' 𝓖)) =
    ⋃₀ (closure '' ((fun V => S ∩ V) '' 𝓖))

omit [TopologicalSpace Y] in
private lemma sUnion_inter_image (S : Set Y) (𝓖 : Set (Set Y)) :
    ⋃₀ ((fun V => S ∩ V) '' 𝓖) = S ∩ ⋃₀ 𝓖 := by
  ext z
  simp only [mem_sUnion, mem_image, mem_inter_iff]
  constructor
  · rintro ⟨_, ⟨V, hV, rfl⟩, hzS, hzV⟩
    exact ⟨hzS, V, hV, hzV⟩
  · rintro ⟨hzS, V, hV, hzV⟩
    exact ⟨S ∩ V, ⟨V, hV, rfl⟩, hzS, hzV⟩

/-- 定理 1A (金魚): 頂点近傍族の CP 性は各 clopen 殻上での CP 性と完全同値 -/
theorem closurePreserving_iff_forall_shell
    {W : ℕ → Set Y} {y : Y}
    (hW : ∀ n, IsOpen (W n) ∧ IsClosed (W n) ∧ y ∈ W n)
    (hinter : (⋂ n, W n) = {y})
    {𝓥 : Set (Set Y)} (hmem : ∀ V ∈ 𝓥, y ∈ V) :
    ClosurePreserving 𝓥 ↔ ∀ n, ClosurePreservingOn (shell W n) 𝓥 := by
  have hW' : ∀ n, IsOpen (W n) ∧ IsClosed (W n) := fun n => ⟨(hW n).1, (hW n).2.1⟩
  constructor
  · intro hCP n 𝓖 h𝓖
    have hS := shell_isClopen hW' n
    rw [sUnion_inter_image, ← clopen_inter_closure hS.1 hS.2, hCP 𝓖 h𝓖]
    ext z
    constructor
    · rintro ⟨hzS, ⟨_, ⟨V, hV, rfl⟩, hzV⟩⟩
      refine ⟨closure (shell W n ∩ V), ⟨shell W n ∩ V, ⟨V, hV, rfl⟩, rfl⟩, ?_⟩
      rw [← clopen_inter_closure hS.1 hS.2]
      exact ⟨hzS, hzV⟩
    · rintro ⟨_, ⟨_, ⟨V, hV, rfl⟩, rfl⟩, hz⟩
      rw [← clopen_inter_closure hS.1 hS.2] at hz
      exact ⟨hz.1, ⟨closure V, ⟨V, hV, rfl⟩, hz.2⟩⟩
  · intro hshell 𝓖 h𝓖
    apply Subset.antisymm
    · intro x hx
      by_cases hG : 𝓖 = ∅
      · subst hG; simp at hx
      · by_cases hxy : x = y
        · obtain ⟨V, hV⟩ := nonempty_iff_ne_empty.mpr hG
          exact ⟨closure V, ⟨V, hV, rfl⟩, subset_closure (hxy ▸ hmem V (h𝓖 hV))⟩
        · obtain ⟨n, hxn⟩ := exists_shell_of_ne hinter hxy
          have hS := shell_isClopen hW' n
          have hx' : x ∈ closure (shell W n ∩ ⋃₀ 𝓖) := by
            rw [← clopen_inter_closure hS.1 hS.2]
            exact ⟨hxn, hx⟩
          rw [← sUnion_inter_image, hshell n 𝓖 h𝓖] at hx'
          rcases hx' with ⟨_, ⟨_, ⟨V, hV, rfl⟩, rfl⟩, hz⟩
          rw [← clopen_inter_closure hS.1 hS.2] at hz
          exact ⟨closure V, ⟨V, hV, rfl⟩, hz.2⟩
    · rintro x ⟨_, ⟨V, hV, rfl⟩, hxV⟩
      exact closure_mono (subset_sUnion_of_mem hV) hxV

/-- 有限極大元和性質（Reverse-WQO） -/
def HasFiniteMaximalSubunion (𝓐 : Set (Set Y)) : Prop :=
  ∀ 𝓗 ⊆ 𝓐, ∃ 𝓕 ⊆ 𝓗, 𝓕.Finite ∧ ⋃₀ 𝓗 = ⋃₀ 𝓕

/-- 有限極大元和性質を持つ族は CP -/
lemma closurePreserving_of_finiteMaximalSubunion {𝓐 : Set (Set Y)}
    (hA : HasFiniteMaximalSubunion 𝓐) : ClosurePreserving 𝓐 := by
  intro 𝓖 h𝓖
  obtain ⟨𝓕, h𝓕𝓖, hfin, heq⟩ := hA 𝓖 h𝓖
  apply Subset.antisymm
  · rw [heq, sUnion_eq_biUnion, hfin.closure_biUnion]
    rintro x hx
    obtain ⟨A, hA', hxA⟩ := mem_iUnion₂.mp hx
    exact ⟨closure A, ⟨A, h𝓕𝓖 hA', rfl⟩, hxA⟩
  · rintro x ⟨_, ⟨A, hA', rfl⟩, hxA⟩
    exact closure_mono (subset_sUnion_of_mem hA') hxA

/-- 定理 2A(1) (金魚): 各殻が離散（全部分集合が閉）なら HasCPOuterBase y が成立 -/
theorem hasCPOuterBase_of_discrete_shells
    {W : ℕ → Set Y} {y : Y}
    (hW : ∀ n, IsOpen (W n) ∧ IsClosed (W n) ∧ y ∈ W n)
    (hinter : (⋂ n, W n) = {y})
    (hdisc : ∀ n (A : Set Y), A ⊆ shell W n → IsClosed A) :
    HasCPOuterBase y := by
  refine ⟨{V | IsOpen V ∧ y ∈ V}, fun _ hV => hV, fun U hUo hyU => ⟨U, ⟨hUo, hyU⟩, Subset.rfl⟩, ?_⟩
  rw [closurePreserving_iff_forall_shell (𝓥 := {V | IsOpen V ∧ y ∈ V}) hW hinter (fun _ hV => hV.2)]
  intro n 𝓖 _
  have hunion_sub : ⋃₀ ((fun V => shell W n ∩ V) '' 𝓖) ⊆ shell W n := by
    rintro z ⟨_, ⟨V, _, rfl⟩, hz⟩; exact hz.1
  rw [(hdisc n _ hunion_sub).closure_eq]
  ext z
  constructor
  · rintro ⟨A, ⟨V, hV, rfl⟩, hz⟩
    exact ⟨closure (shell W n ∩ V), ⟨shell W n ∩ V, ⟨V, hV, rfl⟩, rfl⟩, subset_closure hz⟩
  · rintro ⟨_, ⟨_, ⟨V, hV, rfl⟩, rfl⟩, hz⟩
    rw [(hdisc n _ inter_subset_left).closure_eq] at hz
    exact ⟨shell W n ∩ V, ⟨V, hV, rfl⟩, hz⟩

end ClopenShell

/-- 定理 2B(1) (金魚): 終域に clopen CP 局所基があるとき、任意の位相的埋め込みの始域も HasCPOuterBase を持つ -/
theorem hasCPOuterBase_of_inducing_clopen_CP
    {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    {f : X → Z} (hf : Topology.IsInducing f)
    {x : X} {𝓥 : Set (Set Z)}
    (hclopen : ∀ V ∈ 𝓥, IsOpen V ∧ IsClosed V ∧ f x ∈ V)
    (hbase : ∀ U : Set Z, IsOpen U → f x ∈ U → ∃ V ∈ 𝓥, V ⊆ U)
    (hCP : ClosurePreserving 𝓥) :
    HasCPOuterBase x := by
  let 𝓥' : Set (Set X) := (fun V => f ⁻¹' V) '' 𝓥
  refine ⟨𝓥', ?_, ?_, ?_⟩
  · rintro _ ⟨V, hV, rfl⟩
    exact ⟨(hclopen V hV).1.preimage hf.continuous, (hclopen V hV).2.2⟩
  · intro U hUo hxU
    rw [hf.isOpen_iff] at hUo
    rcases hUo with ⟨W, hWo, rfl⟩
    obtain ⟨V, hV, hVW⟩ := hbase W hWo hxU
    exact ⟨f ⁻¹' V, ⟨V, hV, rfl⟩, preimage_mono hVW⟩
  · intro 𝓖 h𝓖
    apply Subset.antisymm
    · intro a ha
      let 𝓗 : Set (Set Z) := {V ∈ 𝓥 | f ⁻¹' V ∈ 𝓖}
      have hsub : ⋃₀ 𝓖 ⊆ f ⁻¹' (⋃₀ 𝓗) := by
        rintro b ⟨A, hA, hbA⟩
        rcases h𝓖 hA with ⟨V, hV, rfl⟩
        exact ⟨V, ⟨hV, hA⟩, hbA⟩
      have hfa : f a ∈ closure (⋃₀ 𝓗) := by
        have h1 : a ∈ closure (f ⁻¹' (⋃₀ 𝓗)) := closure_mono hsub ha
        exact hf.continuous.closure_preimage_subset (⋃₀ 𝓗) h1
      rw [hCP 𝓗 (fun V hV => hV.1)] at hfa
      rcases hfa with ⟨_, ⟨V, ⟨hV, hVinG⟩, rfl⟩, hfaV⟩
      rw [(hclopen V hV).2.1.closure_eq] at hfaV
      exact ⟨closure (f ⁻¹' V), ⟨f ⁻¹' V, hVinG, rfl⟩, subset_closure hfaV⟩
    · rintro a ⟨_, ⟨A, hA, rfl⟩, haA⟩
      exact closure_mono (subset_sUnion_of_mem hA) haA

end Work.L0031Shell
