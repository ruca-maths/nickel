import Specs.L_0015
import Proofs.L_0005

namespace Proofs.L_0015

open MSpace Set Topology

theorem main : Specs.L_0015.stmt := by
  unfold Specs.L_0015.stmt
  intro X _ hT3 ⟨g, hg, hanti, hstrat⟩
  have : T3Space X := hT3
  -- 単調減少性（任意の m ≤ n に対する拡張）
  have hg_le : ∀ {m n : ℕ}, m ≤ n → ∀ x : X, g n x ⊆ g m x := by
    intro m n hmn
    induction hmn with
    | refl => intro x; exact Subset.rfl
    | @step k _ ih => intro x; exact (hanti k x).trans (ih x)
  -- g から stratification を構成し、L_0005 よりパラコンパクト性を得る
  have hStrat : IsStratifiable X := by
    refine ⟨inferInstance, fun n H => ⋃ y ∈ H, g n y, ?_, ?_, ?_, ?_⟩
    · intro n H _
      exact isOpen_biUnion fun y _ => (hg n y).1
    · intro n H _ y hy
      exact mem_biUnion hy (hg n y).2
    · intro H hH
      apply Subset.antisymm
      · intro x hx
        by_contra hxH
        obtain ⟨n, hn⟩ := hstrat H hH x hxH
        exact hn (mem_iInter.mp hx n)
      · exact subset_iInter fun n y hy => subset_closure (mem_biUnion hy (hg n y).2)
    · intro n H K _ _ hHK
      exact biUnion_subset_biUnion_left hHK
  obtain ⟨hpara⟩ := Proofs.L_0005.main X hStrat
  -- 各 m について開被覆 {g m p | p : X} の局所有限な開細分 U m を取る
  have hcov_ref : ∀ m : ℕ, ∃ (β : Type) (t : β → Set X),
      (∀ i, IsOpen (t i)) ∧ (⋃ i, t i) = univ ∧ LocallyFinite t ∧ ∀ i, ∃ p : X, t i ⊆ g m p := by
    intro m
    exact hpara X (g m) (fun p => (hg m p).1)
      (eq_univ_of_forall fun p => mem_iUnion.mpr ⟨p, (hg m p).2⟩)
  choose β U hUopen hUcov hUlf hUref using hcov_ref
  -- 各 m に対する推移的開 neighbornet T m
  let T (m : ℕ) (x : X) : Set X := ⋂ (i : β m) (_ : x ∈ U m i), U m i
  have hT_mem : ∀ m x, x ∈ T m x := by
    intro m x
    simp only [T, mem_iInter]
    intro i hi
    exact hi
  have hT_open : ∀ m x, IsOpen (T m x) := by
    intro m x
    obtain ⟨N, hN, hfin⟩ := hUlf m x
    have hI_fin : {i : β m | x ∈ U m i}.Finite :=
      hfin.subset fun i hi => ⟨x, hi, mem_of_mem_nhds hN⟩
    have hEq : T m x = ⋂ i ∈ hI_fin.toFinset, U m i := by
      ext z
      simp [T]
    rw [hEq]
    exact isOpen_biInter_finset fun i _ => hUopen m i
  have hT_trans : ∀ m x y, y ∈ T m x → T m y ⊆ T m x := by
    intro m x y hyx z hzy
    simp only [T, mem_iInter] at hyx hzy ⊢
    intro i hxi
    exact hzy i (hyx i hxi)
  -- 単調減少な推移的開 neighbornet 列 W m
  let W (m : ℕ) (x : X) : Set X := ⋂ r ∈ Finset.range (m + 1), T r x
  have hW_mem : ∀ m x, x ∈ W m x := by
    intro m x
    simp only [W, mem_iInter]
    intro r _
    exact hT_mem r x
  have hW_open : ∀ m x, IsOpen (W m x) := fun m x =>
    isOpen_biInter_finset fun r _ => hT_open r x
  have hW_sub_T : ∀ m x, W m x ⊆ T m x := fun m x =>
    biInter_subset_of_mem (Finset.mem_range.mpr (Nat.lt_succ_self m))
  have hW_anti : ∀ {m₁ m₂ : ℕ}, m₁ ≤ m₂ → ∀ x, W m₂ x ⊆ W m₁ x := by
    intro m₁ m₂ hle x z hz
    simp only [W, mem_iInter, Finset.mem_range] at hz ⊢
    intro r hr
    exact hz r (by omega)
  have hW_trans : ∀ m x y, y ∈ W m x → W m y ⊆ W m x := by
    intro m x y hyx z hzy
    simp only [W, mem_iInter] at hyx hzy ⊢
    intro r hr
    exact hT_trans r x y (hyx r hr) (hzy r hr)
  -- g_n の 2 乗・3 乗
  let g2 (n : ℕ) (y : X) : Set X := ⋃ p ∈ g n y, g n p
  let g3 (n : ℕ) (x : X) : Set X := ⋃ w ∈ g n x, g2 n w
  -- A n m = {y | St(y, U m) ⊆ g2 n y}
  let A (n m : ℕ) : Set X := {y : X | ∀ i : β m, y ∈ U m i → U m i ⊆ g2 n y}
  have hA_cov : ∀ n x, ∃ m, x ∈ closure (A n m) := by
    intro n x
    obtain ⟨m₀, hm₀⟩ := hstrat (g n x)ᶜ (hg n x).1.isClosed_compl x (fun h => h (hg n x).2)
    refine ⟨max n m₀, subset_closure ?_⟩
    intro i hxi z hzi
    obtain ⟨p, hp⟩ := hUref (max n m₀) i
    have hpx : p ∈ g n x := by
      by_contra hpnx
      apply hm₀
      exact subset_closure (mem_biUnion hpnx (hg_le (le_max_right n m₀) p (hp hxi)))
    exact mem_biUnion hpx (hg_le (le_max_left n m₀) p (hp hzi))
  -- 各 n, x に対し x ∈ closure (A n m) となる最小の m を k n x とおく
  classical
  let k (n : ℕ) (x : X) : ℕ := Nat.find (hA_cov n x)
  have hk_mem : ∀ n x, x ∈ closure (A n (k n x)) := fun n x => Nat.find_spec (hA_cov n x)
  have hk_min : ∀ n x j, j < k n x → x ∉ closure (A n j) := fun n x _ hj =>
    Nat.find_min (hA_cov n x) hj
  -- 推移的開 neighbornet V n
  let V (n : ℕ) (x : X) : Set X :=
    W (k n x) x \ ⋃ j ∈ Finset.range (k n x), closure (A n j)
  have hV_open : ∀ n x, IsOpen (V n x) := fun n x =>
    (hW_open (k n x) x).sdiff (isClosed_biUnion_finset fun _ _ => isClosed_closure)
  have hV_mem : ∀ n x, x ∈ V n x := by
    intro n x
    refine ⟨hW_mem (k n x) x, ?_⟩
    simp only [mem_iUnion, Finset.mem_range, not_exists]
    intro j hj
    exact hk_min n x j hj
  have hV_trans : ∀ n x y, y ∈ V n x → V n y ⊆ V n x := by
    intro n x y hyx z hzy
    have hkle : k n x ≤ k n y := by
      by_contra hlt
      have hlt' : k n y < k n x := Nat.lt_of_not_ge hlt
      exact hyx.2 (mem_biUnion (Finset.mem_range.mpr hlt') (hk_mem n y))
    refine ⟨hW_trans (k n x) x y hyx.1 (hW_anti hkle y hzy.1), ?_⟩
    intro hz
    simp only [mem_iUnion, Finset.mem_range] at hz
    obtain ⟨j, hj, hzj⟩ := hz
    exact hzy.2 (mem_biUnion (Finset.mem_range.mpr (lt_of_lt_of_le hj hkle)) hzj)
  have hV_sub_g3 : ∀ n x, V n x ⊆ g3 n x := by
    intro n x z hz
    let m := k n x
    have hxcl : x ∈ closure (A n m) := hk_mem n x
    have hO_open : IsOpen (T m x ∩ g n x) := (hT_open m x).inter (hg n x).1
    have hxO : x ∈ T m x ∩ g n x := ⟨hT_mem m x, (hg n x).2⟩
    obtain ⟨w, ⟨hwT, hwg⟩, hwA⟩ := (mem_closure_iff.mp hxcl) (T m x ∩ g n x) hO_open hxO
    have hxU : x ∈ ⋃ i, U m i := by rw [hUcov m]; trivial
    obtain ⟨i₀, hi₀⟩ := mem_iUnion.mp hxU
    have hwU : w ∈ U m i₀ := (mem_iInter₂.mp hwT) i₀ hi₀
    have hzT : z ∈ T m x := hW_sub_T m x hz.1
    have hzU : z ∈ U m i₀ := (mem_iInter₂.mp hzT) i₀ hi₀
    have hzg2 : z ∈ g2 n w := hwA i₀ hwU hzU
    exact mem_biUnion hwg hzg2
  refine ⟨V, fun n x => (hV_open n x).mem_nhds (hV_mem n x), hV_trans, ?_⟩
  intro H hH x hxH
  obtain ⟨n₁, hn₁⟩ := hstrat H hH x hxH
  let K₁ : Set X := closure (⋃ y ∈ H, g n₁ y)
  obtain ⟨n₂, hn₂⟩ := hstrat K₁ isClosed_closure x hn₁
  let K₂ : Set X := closure (⋃ y ∈ K₁, g n₂ y)
  obtain ⟨n₃, hn₃⟩ := hstrat K₂ isClosed_closure x hn₂
  let n : ℕ := max n₁ (max n₂ n₃)
  refine ⟨n, fun hxcl => hn₃ (closure_mono ?_ hxcl)⟩
  intro z hz
  obtain ⟨y, hyH, hzy⟩ := mem_iUnion₂.mp hz
  obtain ⟨w, hwy, hzw⟩ := mem_iUnion₂.mp (hV_sub_g3 n y hzy)
  obtain ⟨p, hpw, hzp⟩ := mem_iUnion₂.mp hzw
  have hwK₁ : w ∈ K₁ :=
    subset_closure (mem_biUnion hyH (hg_le (le_max_left n₁ (max n₂ n₃)) y hwy))
  have hpK₂ : p ∈ K₂ :=
    subset_closure (mem_biUnion hwK₁ (hg_le ((le_max_left n₂ n₃).trans (le_max_right n₁ _)) w hpw))
  exact mem_biUnion hpK₂ (hg_le ((le_max_right n₂ n₃).trans (le_max_right n₁ _)) p hzp)

end Proofs.L_0015
