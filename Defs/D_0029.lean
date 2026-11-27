import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0009
import Defs.D_0012
import Defs.D_0024
import Defs.D_0028

namespace Defs.D_0029

/-!
Chen–Wang (arXiv 1809.03763v2) の X 上の位相 ρ の**修正版**と Proposition 3.4, 3.5.1。

本文 245–250 行: 「Q_n を位相 ρ′ を持つ Q のコピーとし、X = Π_n Q_n に積位相を入れる」。
B'_n の成分 B_ni は（本文で同じ字形の）区間族 𝒬 = {[p_n, p_m)} の元であり、Q の点ではない。
実際 Prop 3.4 の証明は B = [q_n1, q_m1) × … × [q_nn, q_mn) × X_n と書いている。
よって ρ は **ρ′ の積**であり、Defs.D_0011 の `xtop`（離散位相の積）は論文と一致しない。
`xtop` では H(n, x) が開閉（`Defs.D_0012.Hcell_isClopen`）なので、Prop 3.5.1
「Int_ρ H(n, x) = ∅」が偽になる。ここでは `ptop`（ρ′ の積）で次を示す。

* `ptop α` : 各成分に `Defs.D_0009.rho α` を入れた積位相（論文の ρ）。
* `rho_nhd` : ρ′ の開集合 U と x ∈ U に対し、ある b > x で [x, b) ⊆ U（NoMaxOrder）。
* `gfun_isOpen_p`, `gfun_isClosed_p` : g(n, x) は ρ で開かつ閉。
* `prop_3_4` : {g(n, x)}_n は x の ρ での近傍基（Prop 3.4。Compat2.shrink を使う）。
* `prop_3_5_1` : n ≥ 1 なら Int_ρ H(n, x) = ∅（DenselyOrdered）。
* `Node` は DenselyOrdered かつ NoMaxOrder（D_0028 のモデルで上の仮定が成り立つ）。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0009 Defs.D_0012 Defs.D_0024

variable {α : Type} [LinearOrder α]

/-- 論文の ρ: 各成分に ρ′ を入れた積位相。 -/
def ptop (α : Type) [LinearOrder α] : TopologicalSpace (ℕ → α) :=
  @Pi.topologicalSpace ℕ (fun _ => α) (fun _ => rho α)

/-- ρ′ の開集合は各点で右半開区間を含む。 -/
theorem rho_nhd [NoMaxOrder α] {U : Set α} (hU : @IsOpen α (rho α) U) {x : α} (hx : x ∈ U) :
    ∃ b, x < b ∧ Set.Ico x b ⊆ U := by
  induction hU generalizing x with
  | basic s hs =>
    obtain ⟨p, r, rfl⟩ := hs
    exact ⟨r, hx.2, fun y hy => ⟨le_trans hx.1 hy.1, hy.2⟩⟩
  | univ =>
    obtain ⟨b, hb⟩ := exists_gt x
    exact ⟨b, hb, fun _ _ => trivial⟩
  | inter s t _ _ ihs iht =>
    obtain ⟨b1, h1, hs1⟩ := ihs hx.1
    obtain ⟨b2, h2, ht2⟩ := iht hx.2
    refine ⟨min b1 b2, lt_min h1 h2, fun y hy => ⟨hs1 ⟨hy.1, ?_⟩, ht2 ⟨hy.1, ?_⟩⟩⟩
    · exact lt_of_lt_of_le hy.2 (min_le_left _ _)
    · exact lt_of_lt_of_le hy.2 (min_le_right _ _)
  | sUnion S _ ih =>
    obtain ⟨s, hsS, hxs⟩ := hx
    obtain ⟨b, hb, hsub⟩ := ih s hsS hxs
    exact ⟨b, hb, fun y hy => ⟨s, hsS, hsub hy⟩⟩

/-- 有限個の座標が ρ′ 開集合に入るという条件の集合は ρ で開。 -/
theorem isOpen_fin_p (N : ℕ) (s : ℕ → Set α) (hs : ∀ k < N, @IsOpen α (rho α) (s k)) :
    @IsOpen (ℕ → α) (ptop α) {z | ∀ k < N, z k ∈ s k} := by
  let _ : TopologicalSpace α := rho α
  let _ : TopologicalSpace (ℕ → α) := ptop α
  have h : {z : ℕ → α | ∀ k < N, z k ∈ s k} = ⋂ k ∈ Finset.range N, (fun z => z k) ⁻¹' s k := by
    ext z; simp
  rw [h]
  exact isOpen_biInter_finset (fun k hk =>
    (hs k (Finset.mem_range.mp hk)).preimage (continuous_apply k))

/-- 有限個の座標が ρ′ 閉集合に入るという条件の集合は ρ で閉。 -/
theorem isClosed_fin_p (N : ℕ) (s : ℕ → Set α) (hs : ∀ k < N, @IsClosed α (rho α) (s k)) :
    @IsClosed (ℕ → α) (ptop α) {z | ∀ k < N, z k ∈ s k} := by
  let _ : TopologicalSpace α := rho α
  let _ : TopologicalSpace (ℕ → α) := ptop α
  have h : {z : ℕ → α | ∀ k < N, z k ∈ s k} = ⋂ k ∈ Finset.range N, (fun z => z k) ⁻¹' s k := by
    ext z; simp
  rw [h]
  exact isClosed_biInter (fun k hk =>
    (hs k (Finset.mem_range.mp hk)).preimage (continuous_apply k))

variable (q : ℕ ≃ α) (T : Tree2 α)

/-- g(n, x) は ρ で開。 -/
theorem gfun_isOpen_p (n : ℕ) (x : ℕ → α) :
    @IsOpen (ℕ → α) (ptop α) (gfun q T n x) := by
  rw [gfun_eq]
  refine isOpen_fin_p _ _ (fun k _ => ?_)
  split_ifs
  · exact isOpen_Ico _ _
  · exact isOpen_Ico _ _

/-- g(n, x) は ρ で閉。 -/
theorem gfun_isClosed_p [NoMaxOrder α] (n : ℕ) (x : ℕ → α) :
    @IsClosed (ℕ → α) (ptop α) (gfun q T n x) := by
  rw [gfun_eq]
  refine isClosed_fin_p _ _ (fun k _ => ?_)
  split_ifs
  · exact isClosed_Ico _ _
  · exact isClosed_Ico _ _

/-- Proposition 3.4: {g(n, x)}_n は x の ρ での近傍基。 -/
theorem prop_3_4 [NoMaxOrder α] (hc : Compat2 q T) (x : ℕ → α) (U : Set (ℕ → α))
    (hU : @IsOpen (ℕ → α) (ptop α) U) (hx : x ∈ U) : ∃ n, gfun q T n x ⊆ U := by
  let _ : TopologicalSpace α := rho α
  let _ : TopologicalSpace (ℕ → α) := ptop α
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hU x hx
  have hb : ∀ a : ℕ, ∃ b, a ∈ I → x a < b ∧ Set.Ico (x a) b ⊆ u a := by
    intro a
    by_cases ha : a ∈ I
    · obtain ⟨b, h1, h2⟩ := rho_nhd (hu a ha).1 (hu a ha).2
      exact ⟨b, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨x a, fun h => absurd h ha⟩
  choose b hb using hb
  have hA : ∀ a : ℕ, ∃ A, a ∈ I → 0 < A ∧ T.child (x a) A < b a := by
    intro a
    by_cases ha : a ∈ I
    · obtain ⟨A, h1, h2⟩ := hc.shrink (x a) (b a) (hb a ha).1
      exact ⟨A, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose A hA using hA
  refine ⟨I.sup (fun a => a + 1 + A a), ?_⟩
  intro z hz
  apply hsub
  intro a ha
  have hle : a + 1 + A a ≤ I.sup (fun a => a + 1 + A a) :=
    Finset.le_sup (f := fun a => a + 1 + A a) ha
  set n := I.sup (fun a => a + 1 + A a)
  have hza := hz.1 a (by omega)
  apply (hb a ha).2
  refine ⟨hza.1, lt_of_lt_of_le hza.2 ?_⟩
  refine le_trans (T.child_le_child (x a) (hA a ha).1 ?_) (hA a ha).2.le
  unfold lvl; omega

/-- Proposition 3.5.1: n ≥ 1 なら H(n, x) は ρ で内部が空。 -/
theorem prop_3_5_1 [NoMaxOrder α] [DenselyOrdered α] (n : ℕ) (hn : 0 < n) (x : ℕ → α) :
    @interior (ℕ → α) (ptop α) (Hcell q T n x) = ∅ := by
  let _ : TopologicalSpace α := rho α
  let _ : TopologicalSpace (ℕ → α) := ptop α
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  obtain ⟨V, hVsub, hVo, hzV⟩ := mem_interior.mp hz
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hVo z hzV
  have hb : ∃ b, z 0 < b ∧ (0 ∈ I → Set.Ico (z 0) b ⊆ u 0) := by
    by_cases h0 : 0 ∈ I
    · obtain ⟨b, hb, hs⟩ := rho_nhd (hu 0 h0).1 (hu 0 h0).2
      exact ⟨b, hb, fun _ => hs⟩
    · obtain ⟨b, hb⟩ := exists_gt (z 0)
      exact ⟨b, hb, fun h => absurd h h0⟩
  obtain ⟨b, hzb, hbs⟩ := hb
  obtain ⟨v, hv1, hv2⟩ := exists_between hzb
  have hz' : Function.update z 0 v ∈ V := by
    apply hsub
    intro a ha
    by_cases h : a = 0
    · subst h
      rw [Function.update_self]
      exact hbs ha ⟨hv1.le, hv2⟩
    · rw [Function.update_of_ne h]
      exact (hu a ha).2
  have h1 := (hVsub hz').1 0 hn
  have h2 := (hVsub hzV).1 0 hn
  rw [Function.update_self] at h1
  rw [h1] at hv1
  rw [h2] at hv1
  exact lt_irrefl _ hv1

/-! D_0028 のモデル `Node` は上の仮定を満たす。 -/

open Defs.D_0028 in
instance : NoMaxOrder Node where
  exists_gt s := ⟨⟨s.val ++ [0]⟩, by
    show R s.val (s.val ++ [0])
    exact prefix_lt s.val 0 []⟩

open Defs.D_0028 in
instance : DenselyOrdered Node where
  dense s t h := by
    have h' : R s.val t.val := h
    rcases lt_cases s.val t.val h' with ⟨a, m, ht⟩ | h2
    · refine ⟨⟨s.val ++ [a + 1]⟩, ?_, ?_⟩
      · show R s.val (s.val ++ [a + 1])
        exact prefix_lt s.val (a + 1) []
      · show R (s.val ++ [a + 1]) t.val
        rw [ht]
        exact app_lt s.val (by omega) [] m
    · refine ⟨⟨s.val ++ [0]⟩, ?_, h2 [0]⟩
      show R s.val (s.val ++ [0])
      exact prefix_lt s.val 0 []

end Defs.D_0029
