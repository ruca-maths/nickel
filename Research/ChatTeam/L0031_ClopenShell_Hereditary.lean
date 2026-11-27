import Mathlib.Topology.Basic
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Finset.Nat
import Targets
import Defs.D_0001
import Defs.D_0010
import Proofs.L_0014
import Proofs.L_0017
import Proofs.L_0032

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

section ShellStratifiable

variable {Y : Type*} [TopologicalSpace Y]

omit [TopologicalSpace Y] in
private lemma antitone_of_succ {α : Type*} {f : ℕ → Set α}
    (hf : ∀ k, f (k + 1) ⊆ f k) {a b : ℕ} (hab : a ≤ b) : f b ⊆ f a := by
  induction hab with
  | refl => exact Subset.rfl
  | @step m _ ih => exact (hf m).trans ih

omit [TopologicalSpace Y] in
lemma decClopen_mem {W : ℕ → Set Y} {y : Y} (hy : ∀ n, y ∈ W n) (n : ℕ) :
    y ∈ decClopen W n := by
  cases n with
  | zero => exact mem_univ y
  | succ m =>
    simp only [decClopen, mem_iInter]
    intro i _
    exact hy i

omit [TopologicalSpace Y] in
lemma shell_disjoint (W : ℕ → Set Y) {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (shell W m) (shell W n) := by
  rw [Set.disjoint_left]
  intro x hxm hxn
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact hxm.2 (decClopen_antitone W (Nat.succ_le_of_lt hlt) hxn.1)
  · exact hxn.2 (decClopen_antitone W (Nat.succ_le_of_lt hgt) hxm.1)

structure IsShellHeathSystem (W : ℕ → Set Y) (y : Y)
    (g_shell : ℕ → ℕ → Y → Set Y) : Prop where
  open_mem_sub : ∀ n k x, x ∈ shell W n →
    IsOpen (g_shell n k x) ∧ x ∈ g_shell n k x ∧ g_shell n k x ⊆ shell W n
  mono : ∀ n k x, x ∈ shell W n → g_shell n (k + 1) x ⊆ g_shell n k x
  shell_sep : ∀ n (H : Set Y), IsClosed H → H ⊆ shell W n →
    ∀ x ∈ shell W n, x ∉ H → ∃ k, x ∉ closure (⋃ z ∈ H, g_shell n k z)
  vertex_sep : ∀ H : Set Y, IsClosed H → y ∉ H →
    ∃ k, y ∉ closure (⋃ n, ⋃ z ∈ H ∩ shell W n, g_shell n k z)

theorem isStratifiable_iff_shells {Y : Type} [TopologicalSpace Y]
    {W : ℕ → Set Y} {y : Y}
    (hW : ∀ n, IsOpen (W n) ∧ IsClosed (W n) ∧ y ∈ W n)
    (hinter : (⋂ n, W n) = {y}) :
    IsStratifiable Y ↔
      (∀ n (x : Y), x ∈ shell W n → IsClosed ({x} : Set Y)) ∧
      ∃ g_shell : ℕ → ℕ → Y → Set Y, IsShellHeathSystem W y g_shell := by
  have hW' : ∀ n, IsOpen (W n) ∧ IsClosed (W n) := fun n => ⟨(hW n).1, (hW n).2.1⟩
  constructor
  · rintro ⟨hT1, hStrat⟩
    refine ⟨?_, ?_⟩
    · intro n x _
      exact @isClosed_singleton Y _ hT1 x
    · obtain ⟨g, hg_open, hg_mono, hg_sep⟩ := Proofs.L_0014.main Y hT1 hStrat
      refine ⟨fun n k x => g k x ∩ shell W n, ?_⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro n k x hxn
        exact ⟨(hg_open k x).1.inter (shell_isClopen hW' n).1,
          ⟨(hg_open k x).2, hxn⟩, inter_subset_right⟩
      · intro n k x _
        exact inter_subset_inter_left _ (hg_mono k x)
      · intro n H hH _ x _ hxH
        obtain ⟨k, hk⟩ := hg_sep H hH x hxH
        refine ⟨k, fun hxcl => hk (closure_mono ?_ hxcl)⟩
        intro w hw
        simp only [mem_iUnion] at hw ⊢
        rcases hw with ⟨z, hzH, hwz⟩
        exact ⟨z, hzH, hwz.1⟩
      · intro H hH hyH
        obtain ⟨k, hk⟩ := hg_sep H hH y hyH
        refine ⟨k, fun hycl => hk (closure_mono ?_ hycl)⟩
        intro w hw
        simp only [mem_iUnion] at hw ⊢
        rcases hw with ⟨n, z, hz, hwz⟩
        exact ⟨z, hz.1, hwz.1⟩
  · rintro ⟨hT1_shell, g_shell, hsys⟩
    classical
    have hT1 : T1Space Y := by
      constructor
      intro x
      by_cases hxy : x = y
      · subst hxy
        rw [← hinter]
        exact isClosed_iInter (fun n => (hW n).2.1)
      · obtain ⟨n, hxn⟩ := exists_shell_of_ne hinter hxy
        exact hT1_shell n x hxn
    let shellIdx (x : Y) (hxy : x ≠ y) : ℕ :=
      Classical.choose (exists_shell_of_ne hinter hxy)
    have hshellIdx : ∀ (x : Y) (hxy : x ≠ y), x ∈ shell W (shellIdx x hxy) :=
      fun x hxy => Classical.choose_spec (exists_shell_of_ne hinter hxy)
    let g : ℕ → Y → Set Y := fun k x =>
      if hxy : x = y then decClopen W k else g_shell (shellIdx x hxy) k x
    have hg_open : ∀ k x, IsOpen (g k x) ∧ x ∈ g k x := by
      intro k x
      by_cases hxy : x = y
      · simp only [g, hxy, ↓reduceDIte]
        subst hxy
        exact ⟨(decClopen_isClopen hW' k).1, decClopen_mem (fun i => (hW i).2.2) k⟩
      · simp only [g, hxy, ↓reduceDIte]
        have h := hsys.open_mem_sub (shellIdx x hxy) k x (hshellIdx x hxy)
        exact ⟨h.1, h.2.1⟩
    have hg_mono : ∀ k x, g (k + 1) x ⊆ g k x := by
      intro k x
      by_cases hxy : x = y
      · simp only [g, hxy, ↓reduceDIte]
        exact decClopen_antitone W (Nat.le_succ k)
      · simp only [g, hxy, ↓reduceDIte]
        exact hsys.mono (shellIdx x hxy) k x (hshellIdx x hxy)
    have hg_sep : ∀ H : Set Y, IsClosed H → ∀ x, x ∉ H →
        ∃ k, x ∉ closure (⋃ z ∈ H, g k z) := by
      intro H hH x hxH
      by_cases hxy : x = y
      · subst hxy
        obtain ⟨k, hk⟩ := hsys.vertex_sep H hH hxH
        refine ⟨k, fun hycl => hk (closure_mono ?_ hycl)⟩
        intro w hw
        simp only [mem_iUnion] at hw ⊢
        rcases hw with ⟨z, hzH, hwz⟩
        have hzy : z ≠ x := fun h => hxH (h ▸ hzH)
        simp only [g, hzy, ↓reduceDIte] at hwz
        exact ⟨shellIdx z hzy, z, ⟨hzH, hshellIdx z hzy⟩, hwz⟩
      · let n := shellIdx x hxy
        have hxn : x ∈ shell W n := hshellIdx x hxy
        have hSn := shell_isClopen hW' n
        obtain ⟨k₁, hk₁⟩ :=
          hsys.shell_sep n (H ∩ shell W n) (hH.inter hSn.2) inter_subset_right x hxn (fun h => hxH h.1)
        let k := max (n + 1) k₁
        refine ⟨k, fun hxcl => ?_⟩
        have hxcl' : x ∈ closure (shell W n ∩ ⋃ z ∈ H, g k z) := by
          rw [← clopen_inter_closure hSn.1 hSn.2]
          exact ⟨hxn, hxcl⟩
        have hsub : shell W n ∩ (⋃ z ∈ H, g k z) ⊆ ⋃ z ∈ H ∩ shell W n, g_shell n k₁ z := by
          rintro w ⟨hwn, hw⟩
          simp only [mem_iUnion] at hw ⊢
          rcases hw with ⟨z, hzH, hwz⟩
          by_cases hzy : z = y
          · simp only [g, hzy, ↓reduceDIte] at hwz
            exact False.elim (hwn.2 (decClopen_antitone W (le_max_left (n + 1) k₁) hwz))
          · simp only [g, hzy, ↓reduceDIte] at hwz
            have hzm : z ∈ shell W (shellIdx z hzy) := hshellIdx z hzy
            have hwm : w ∈ shell W (shellIdx z hzy) :=
              (hsys.open_mem_sub (shellIdx z hzy) k z hzm).2.2 hwz
            have hmn : shellIdx z hzy = n := by
              by_contra hne
              exact Set.disjoint_left.mp (shell_disjoint W hne) hwm hwn
            rw [hmn] at hzm hwz
            have hstep := antitone_of_succ (f := fun j => g_shell n j z)
              (fun j => hsys.mono n j z hzm) (le_max_right (n + 1) k₁)
            exact ⟨z, ⟨hzH, hzm⟩, hstep hwz⟩
        exact hk₁ (closure_mono hsub hxcl')
    exact ⟨hT1, Proofs.L_0017.main Y ⟨g, hg_open, hg_mono, hg_sep⟩⟩

end ShellStratifiable

theorem hasCPOuterBase_of_reverseWQO_shells
    {Y : Type*} [TopologicalSpace Y] {W : ℕ → Set Y} {y : Y}
    (hW : ∀ n, IsOpen (W n) ∧ IsClosed (W n) ∧ y ∈ W n)
    (hinter : (⋂ n, W n) = {y})
    (𝓐 : ℕ → Set (Set Y))
    (hWQO : ∀ n, HasFiniteMaximalSubunion (𝓐 n))
    (hcofinal : ∀ U : Set Y, IsOpen U → y ∈ U →
      ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ V ⊆ U ∧ ∀ n, shell W n ∩ V ∈ 𝓐 n) :
    HasCPOuterBase y := by
  let 𝓥 : Set (Set Y) := {V | IsOpen V ∧ y ∈ V ∧ ∀ n, shell W n ∩ V ∈ 𝓐 n}
  refine ⟨𝓥, fun _ hV => ⟨hV.1, hV.2.1⟩, ?_, ?_⟩
  · intro U hUo hyU
    obtain ⟨V, hVo, hyV, hVU, hVA⟩ := hcofinal U hUo hyU
    exact ⟨V, ⟨hVo, hyV, hVA⟩, hVU⟩
  · rw [closurePreserving_iff_forall_shell (𝓥 := 𝓥) hW hinter (fun _ hV => hV.2.1)]
    intro n 𝓖 h𝓖
    have hsub : (fun V => shell W n ∩ V) '' 𝓖 ⊆ 𝓐 n := by
      rintro _ ⟨V, hV, rfl⟩
      exact (h𝓖 hV).2.2 n
    exact closurePreserving_of_finiteMaximalSubunion (hWQO n) _ hsub

section ClopenPartitionNoGo

open Defs.D_0010

theorem hasCPOuterBase_of_locallyFinite_clopen_shells
    {Y : Type} [TopologicalSpace Y]
    {W : ℕ → Set Y} {y : Y}
    (hW : ∀ n, IsOpen (W n) ∧ IsClosed (W n) ∧ y ∈ W n)
    (hinter : (⋂ n, W n) = {y})
    {g_shell : ℕ → ℕ → Y → Set Y}
    (hsys : IsShellHeathSystem W y g_shell)
    (hclosed : ∀ n k x, x ∈ shell W n → IsClosed (g_shell n k x))
    (hlf : ∀ n k, ∀ x ∈ shell W n, ∃ O : Set Y, IsOpen O ∧ x ∈ O ∧
      {P : Set Y | (∃ z ∈ shell W n, P = g_shell n k z) ∧ (O ∩ P).Nonempty}.Finite) :
    HasCPOuterBase y := by
  have hW' : ∀ n, IsOpen (W n) ∧ IsClosed (W n) := fun n => ⟨(hW n).1, (hW n).2.1⟩
  let 𝓟 (n k : ℕ) : Set (Set Y) := {P | ∃ z ∈ shell W n, P = g_shell n k z}
  let 𝓑 : ℕ → Set (Set Y) := fun k =>
    {V | IsOpen V ∧ y ∈ V ∧ ∀ n, ∃ 𝓕 ⊆ 𝓟 n k, shell W n ∩ V = shell W n \ ⋃₀ 𝓕}
  apply Proofs.L_0032.main Y y W hW hinter
  refine ⟨𝓑, ?_, ?_, ?_⟩
  · intro k V hV
    exact ⟨hV.1, hV.2.1⟩
  · intro k
    rw [closurePreserving_iff_forall_shell (𝓥 := 𝓑 k) hW hinter (fun _ hV => hV.2.1)]
    intro n 𝓖 h𝓖
    apply Subset.antisymm
    · intro x hx
      have hSn := shell_isClopen hW' n
      have hunion_sub : ⋃₀ ((fun V => shell W n ∩ V) '' 𝓖) ⊆ shell W n := by
        rintro w ⟨_, ⟨V, _, rfl⟩, hw⟩
        exact hw.1
      have hxn : x ∈ shell W n := closure_minimal hunion_sub hSn.2 hx
      have hxmem : x ∈ ⋃₀ ((fun V => shell W n ∩ V) '' 𝓖) := by
        by_contra hxnot
        obtain ⟨O, _, hxO, hOfin⟩ := hlf n k x hxn
        let 𝒬 : Set (Set Y) := {P ∈ 𝓟 n k | x ∈ P}
        have h𝒬_fin : 𝒬.Finite :=
          hOfin.subset fun P hP => ⟨hP.1, ⟨x, hxO, hP.2⟩⟩
        let Ux : Set Y := ⋂ P ∈ 𝒬, P
        have hUxo : IsOpen Ux := h𝒬_fin.isOpen_biInter fun P hP => by
          rcases hP.1 with ⟨z, hz, rfl⟩
          exact (hsys.open_mem_sub n k z hz).1
        have hxUx : x ∈ Ux := by
          simp only [Ux, mem_iInter]
          intro P hP
          exact hP.2
        obtain ⟨w, hwUx, hwU⟩ := mem_closure_iff.mp hx Ux hUxo hxUx
        rcases hwU with ⟨_, ⟨V, hV, rfl⟩, hwV⟩
        obtain ⟨𝓕, h𝓕sub, hVeq⟩ := (h𝓖 hV).2.2 n
        have hxV : x ∉ shell W n ∩ V := fun h => hxnot ⟨shell W n ∩ V, ⟨V, hV, rfl⟩, h⟩
        dsimp only at hwV
        rw [hVeq] at hxV hwV
        have hxF : x ∈ ⋃₀ 𝓕 := by
          by_contra h
          exact hxV ⟨hxn, h⟩
        rcases hxF with ⟨P, hPF, hxP⟩
        have hPQ : P ∈ 𝒬 := ⟨h𝓕sub hPF, hxP⟩
        have hwP : w ∈ P := by
          simp only [Ux, mem_iInter] at hwUx
          exact hwUx P hPQ
        exact hwV.2 ⟨P, hPF, hwP⟩
      rcases hxmem with ⟨A, hA, hxA⟩
      exact ⟨closure A, ⟨A, hA, rfl⟩, subset_closure hxA⟩
    · rintro x ⟨_, ⟨A, hA, rfl⟩, hxA⟩
      exact closure_mono (subset_sUnion_of_mem hA) hxA
  · intro U hUo hyU
    let H : Set Y := Uᶜ
    have hHc : IsClosed H := hUo.isClosed_compl
    have hyH : y ∉ H := fun h => h hyU
    obtain ⟨k, hk⟩ := hsys.vertex_sep H hHc hyH
    let E : Set Y := ⋃ n, ⋃ z ∈ H ∩ shell W n, g_shell n k z
    have hE_shell : ∀ n,
        shell W n ∩ E = ⋃₀ {P ∈ 𝓟 n k | ∃ z ∈ H ∩ shell W n, P = g_shell n k z} := by
      intro n
      ext w
      constructor
      · rintro ⟨hwn, hwE⟩
        simp only [E, mem_iUnion] at hwE
        rcases hwE with ⟨m, z, ⟨hzH, hzm⟩, hwz⟩
        have hwm : w ∈ shell W m := (hsys.open_mem_sub m k z hzm).2.2 hwz
        have hmn : m = n := by
          by_contra hne
          exact Set.disjoint_left.mp (shell_disjoint W hne) hwm hwn
        subst hmn
        exact ⟨g_shell m k z, ⟨⟨z, hzm, rfl⟩, ⟨z, ⟨hzH, hzm⟩, rfl⟩⟩, hwz⟩
      · rintro ⟨P, ⟨_, ⟨z, ⟨hzH, hzn⟩, rfl⟩⟩, hwz⟩
        refine ⟨(hsys.open_mem_sub n k z hzn).2.2 hwz, ?_⟩
        simp only [E, mem_iUnion]
        exact ⟨n, z, ⟨hzH, hzn⟩, hwz⟩
    have hEc : IsClosed E := by
      rw [← closure_subset_iff_isClosed]
      intro x hxE
      by_cases hxy : x = y
      · subst hxy
        exact False.elim (hk hxE)
      · obtain ⟨n, hxn⟩ := exists_shell_of_ne hinter hxy
        have hSn := shell_isClopen hW' n
        have hxcl : x ∈ closure (shell W n ∩ E) := by
          rw [← clopen_inter_closure hSn.1 hSn.2]
          exact ⟨hxn, hxE⟩
        let 𝓕 : Set (Set Y) := {P ∈ 𝓟 n k | ∃ z ∈ H ∩ shell W n, P = g_shell n k z}
        rw [hE_shell n] at hxcl
        have hxF : x ∈ ⋃₀ 𝓕 := by
          by_contra hxnot
          obtain ⟨O, hOo, hxO, hOfin⟩ := hlf n k x hxn
          let 𝓕₀ : Set (Set Y) := {P ∈ 𝓕 | (O ∩ P).Nonempty}
          have h𝓕₀_fin : 𝓕₀.Finite := hOfin.subset fun P hP => ⟨hP.1.1, hP.2⟩
          let O' : Set Y := O ∩ ⋂ P ∈ 𝓕₀, Pᶜ
          have hO'o : IsOpen O' := hOo.inter (h𝓕₀_fin.isOpen_biInter fun P hP => by
            rcases hP.1.1 with ⟨z, hz, rfl⟩
            exact (hclosed n k z hz).isOpen_compl)
          have hxO' : x ∈ O' := by
            refine ⟨hxO, ?_⟩
            simp only [mem_iInter]
            intro P hP hxP
            exact hxnot ⟨P, hP.1, hxP⟩
          obtain ⟨w, hwO', hwF⟩ := mem_closure_iff.mp hxcl O' hO'o hxO'
          rcases hwF with ⟨P, hPF, hwP⟩
          have hP0 : P ∈ 𝓕₀ := ⟨hPF, ⟨w, hwO'.1, hwP⟩⟩
          have hwPc : w ∈ Pᶜ := by
            have hmem := hwO'.2
            simp only [mem_iInter] at hmem
            exact hmem P hP0
          exact hwPc hwP
        have hxIE : x ∈ shell W n ∩ E := by rwa [hE_shell n]
        exact hxIE.2
    refine ⟨k, Eᶜ, ⟨hEc.isOpen_compl, fun hyE => hk (subset_closure hyE), ?_⟩, ?_⟩
    · intro n
      refine ⟨{P ∈ 𝓟 n k | ∃ z ∈ H ∩ shell W n, P = g_shell n k z}, fun _ hP => hP.1, ?_⟩
      ext w
      constructor
      · rintro ⟨hwn, hwEc⟩
        refine ⟨hwn, fun hwF => hwEc ?_⟩
        have hwIE : w ∈ shell W n ∩ E := by rwa [hE_shell n]
        exact hwIE.2
      · rintro ⟨hwn, hwF⟩
        refine ⟨hwn, fun hwE => hwF ?_⟩
        have hwIE : w ∈ shell W n ∩ E := ⟨hwn, hwE⟩
        rwa [hE_shell n] at hwIE
    · intro w hwEc
      by_contra hwU
      have hwy : w ≠ y := fun h => hwU (h ▸ hyU)
      obtain ⟨n, hwn⟩ := exists_shell_of_ne hinter hwy
      apply hwEc
      simp only [E, mem_iUnion]
      exact ⟨n, w, ⟨hwU, hwn⟩, (hsys.open_mem_sub n k w hwn).2.1⟩

theorem hasCPOuterBase_of_clopenPartition_shells
    {Y : Type} [TopologicalSpace Y]
    {W : ℕ → Set Y} {y : Y}
    (hW : ∀ n, IsOpen (W n) ∧ IsClosed (W n) ∧ y ∈ W n)
    (hinter : (⋂ n, W n) = {y})
    {g_shell : ℕ → ℕ → Y → Set Y}
    (hsys : IsShellHeathSystem W y g_shell)
    (hclosed : ∀ n k x, x ∈ shell W n → IsClosed (g_shell n k x))
    (hpart : ∀ n k, ∀ x ∈ shell W n, ∀ z ∈ shell W n,
      (g_shell n k x ∩ g_shell n k z).Nonempty → g_shell n k z = g_shell n k x) :
    HasCPOuterBase y := by
  refine hasCPOuterBase_of_locallyFinite_clopen_shells hW hinter hsys hclosed ?_
  intro n k x hxn
  refine ⟨g_shell n k x, (hsys.open_mem_sub n k x hxn).1, (hsys.open_mem_sub n k x hxn).2.1, ?_⟩
  refine (Set.finite_singleton (g_shell n k x)).subset ?_
  rintro P ⟨⟨z, hzn, rfl⟩, hne⟩
  exact mem_singleton_iff.mpr (hpart n k x hxn z hzn hne)

end ClopenPartitionNoGo

end Work.L0031Shell
