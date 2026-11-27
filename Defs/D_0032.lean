import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0031

namespace Defs.D_0032

/-!
Chen–Wang (arXiv 1809.03763v2) Proposition 4.8 と Corollary 4.9（本文 777–833 行）の一般形。

論文は Ln covers sequence G(n, m, L) の中で述べるが、証明の中身は次の一般的な事実である:
**n ≥ 1 と x を固定すると、ある a ≥ n があって、ℓ ≥ a のとき g(ℓ, z) が H(n, x) と交われば
z ∈ H(n, x)**（`key_4_8`）。このとき H(ℓ, z) ⊆ H(n, z) = H(n, x)。
証明は論文と同じ: H(n, x) と交わるが H(n, z) ≠ H(n, x) となる g(n, z) は番号 hidx n z < hidx n x
ごとに高々 1 つ（`gfun_nested`）で有限個。各々について先頭 n 座標のどこか j で z j < x j となり、
Compat2.shrink で十分大きい番号の g(ℓ, ·) の第 j 座標の区間は x j を含まなくなる。

* `Hcell_eq_of_mem` : u ∈ H(n, x) なら H(n, u) = H(n, x)（H(n, ·) は分割）。
* `Hcell_eq_of_gfun_eq` : g(n, z) = g(n, z') なら H(n, z) = H(n, z')。
* `Hcell_anti` : n ≤ a なら H(a, z) ⊆ H(n, z)。
* `hidx_lt_of_bad` : Prop 3.3.6′ の形（g(n, z) ∩ H(n, x) ≠ ∅, H(n, z) ≠ H(n, x) ⇒ hidx z < hidx x）。
* `key_4_8` : 上の一般形。
* `prop_4_8` : G_m = g(m, y₀), n ≥ m ≥ 1, H(n, x) ⊆ G_m なら、ある a ≥ n について
  lnc(a, G_m) の元で H(n, x) と交わるものの族 𝒢 は H(n, x) を覆い、その各元 g(a, z) の
  H(a, z) は H(n, x) に含まれる（論文の ∪H(a, i*, l*) ⊂ H(n, i*, l*) ⊂ ∪G(a, i*, l*)）。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0031

variable {α : Type} [LinearOrder α] {q : ℕ ≃ α} {T : Tree2 α}

theorem Hcell_eq_of_mem {n : ℕ} (hn : 0 < n) {x u : ℕ → α} (hu : u ∈ Hcell q T n x) :
    Hcell q T n u = Hcell q T n x := by
  rw [← gfun_inter_H q T n hn u, ← gfun_inter_H q T n hn x,
    gfun_eq_of_mem_Hcell q T hn hu, hidx_eq_of_mem_Hcell q T hn hu]

theorem Hcell_eq_of_gfun_eq (hc : Compat2 q T) {n : ℕ} (hn : 0 < n) {z z' : ℕ → α}
    (h : gfun q T n z = gfun q T n z') : Hcell q T n z = Hcell q T n z' := by
  have h1 : hidx q n z ≤ hidx q n z' :=
    hidx_le_of_mem_gfun hc hn (h ▸ mem_gfun q T n z' : z' ∈ gfun q T n z)
  have h2 : hidx q n z' ≤ hidx q n z :=
    hidx_le_of_mem_gfun hc hn (h.symm ▸ mem_gfun q T n z : z ∈ gfun q T n z')
  rw [← gfun_inter_H q T n hn z, ← gfun_inter_H q T n hn z', h, le_antisymm h1 h2]

theorem Hcell_anti {n a : ℕ} (hn : 0 < n) (hna : n ≤ a) (z : ℕ → α) :
    Hcell q T a z ⊆ Hcell q T n z := by
  have hh : hidx q n z ≤ hidx q a z := code_mono n hn _ a hna
  have hl : lvl q n z ≤ lvl q a z := by unfold lvl; omega
  rintro w ⟨hw1, hw2⟩
  refine ⟨fun k hk => hw1 k (by omega), fun k hk1 hk2 => ?_⟩
  by_cases hka : k < a
  · rw [hw1 k hka]; exact mem_ival T (lvl_pos q n z) (z k)
  · exact ival_mono T (lvl_pos q n z) hl (z k) (hw2 k (by omega) (by omega))

theorem Hcell_sub_H {n : ℕ} (hn : 0 < n) (x : ℕ → α) :
    Hcell q T n x ⊆ H q n (hidx q n x) := by
  rw [← gfun_inter_H q T n hn x]; exact Set.inter_subset_right

/-- Prop 3.3.6′ の形。 -/
theorem hidx_lt_of_bad (hc : Compat2 q T) {n : ℕ} (hn : 0 < n) {x z : ℕ → α}
    (hne : (gfun q T n z ∩ Hcell q T n x).Nonempty) (hd : Hcell q T n z ≠ Hcell q T n x) :
    hidx q n z < hidx q n x := by
  obtain ⟨w, hw1, hw2⟩ := hne
  have hle : hidx q n z ≤ hidx q n x := by
    rw [← hidx_eq_of_mem_Hcell q T hn hw2]; exact hidx_le_of_mem_gfun hc hn hw1
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    apply hd
    -- 同じ番号: w ∈ g(n,z) ∩ H(n, hidx x) = g(n,z) ∩ H(n, hidx z) = H(n, z)
    have hwz : w ∈ Hcell q T n z := by
      rw [← gfun_inter_H q T n hn z, h]
      exact ⟨hw1, Hcell_sub_H hn x hw2⟩
    rw [← Hcell_eq_of_mem hn hwz, Hcell_eq_of_mem hn hw2]

/-- 「悪い」g(n, z) は H(n, x) の点 x を含む g(n, x) を含む。 -/
theorem gfun_sup_of_meet (hc : Compat2 q T) {n : ℕ} (hn : 0 < n) {x z : ℕ → α}
    (hne : (gfun q T n z ∩ Hcell q T n x).Nonempty) : gfun q T n x ⊆ gfun q T n z := by
  obtain ⟨w, hw1, hw2⟩ := hne
  rw [← gfun_eq_of_mem_Hcell q T hn hw2]
  exact gfun_trans hc hn hw1

/-- 番号 c ごとの一様な上界。 -/
theorem bad_bound (hc : Compat2 q T) {n : ℕ} (hn : 0 < n) (x : ℕ → α) (c : ℕ) :
    ∃ A, ∀ z, hidx q n z = c → Hcell q T n z ≠ Hcell q T n x →
      (gfun q T n z ∩ Hcell q T n x).Nonempty →
      ∀ ℓ, A ≤ ℓ → ¬ (gfun q T ℓ z ∩ Hcell q T n x).Nonempty := by
  by_cases hex : ∃ z0, hidx q n z0 = c ∧ Hcell q T n z0 ≠ Hcell q T n x ∧
      (gfun q T n z0 ∩ Hcell q T n x).Nonempty
  · obtain ⟨z0, hc0, hd0, hm0⟩ := hex
    -- 先頭 n 座標のどこかで z0 と x は異なる
    have hj : ∃ j < n, z0 j ≠ x j := by
      by_contra hall
      push_neg at hall
      apply hd0
      have hzx : z0 ∈ Hcell q T n x := by
        obtain ⟨w, hw1, hw2⟩ := hm0
        have hcode : hidx q n z0 = hidx q n x :=
          (code_eq_iff n hn _ _).2 (fun k hk => by
            show q.symm (z0 k) = q.symm (x k); rw [hall k hk])
        have hwz : w ∈ Hcell q T n z0 := by
          rw [← gfun_inter_H q T n hn z0, hcode]
          exact ⟨hw1, Hcell_sub_H hn x hw2⟩
        rw [← Hcell_eq_of_mem hn hw2, Hcell_eq_of_mem hn hwz]
        exact mem_Hcell q T n z0
      exact Hcell_eq_of_mem hn hzx
    obtain ⟨j, hjn, hjne⟩ := hj
    have hxz0 : x ∈ gfun q T n z0 := gfun_sup_of_meet hc hn hm0 (mem_gfun q T n x)
    have hlt : z0 j < x j := lt_of_le_of_ne (hxz0.1 j hjn).1 hjne
    obtain ⟨A, hA0, hA⟩ := hc.shrink (z0 j) (x j) hlt
    refine ⟨A + n, fun z hzc hd hm ℓ hAℓ hm' => ?_⟩
    -- g(n, z) = g(n, z0)（どちらも x を含み、番号が同じ）
    have hxz : x ∈ gfun q T n z := gfun_sup_of_meet hc hn hm (mem_gfun q T n x)
    have heq : gfun q T n z = gfun q T n z0 := by
      have hi : (gfun q T n z ∩ gfun q T n z0).Nonempty := ⟨x, hxz, hxz0⟩
      exact le_antisymm (gfun_nested hc (by rw [hc0, hzc]) (Set.inter_comm _ _ ▸ hi))
        (gfun_nested hc (by rw [hc0, hzc]) hi)
    have hzj : z j = z0 j := by
      have hz : z ∈ Hcell q T n z0 := by
        rw [← Hcell_eq_of_gfun_eq hc hn heq]; exact mem_Hcell q T n z
      exact hz.1 j hjn
    obtain ⟨w, hw1, hw2⟩ := hm'
    have hwj : w j = x j := hw2.1 j hjn
    have h1 := (hw1.1 j (by omega)).2
    rw [hwj, hzj] at h1
    have hle : A ≤ lvl q ℓ z := by unfold lvl; omega
    exact absurd (lt_trans h1 (lt_of_le_of_lt (T.child_le_child (z0 j) hA0 hle) hA))
      (lt_irrefl _)
  · exact ⟨0, fun z hzc hd hm _ _ _ => hex ⟨z, hzc, hd, hm⟩⟩

/-- Prop 4.8 の核心（一般形）。 -/
theorem key_4_8 (hc : Compat2 q T) {n : ℕ} (hn : 0 < n) (x : ℕ → α) :
    ∃ a, n ≤ a ∧ ∀ ℓ, a ≤ ℓ → ∀ z,
      (gfun q T ℓ z ∩ Hcell q T n x).Nonempty → z ∈ Hcell q T n x := by
  choose A hA using bad_bound hc hn x
  refine ⟨n + (Finset.range (hidx q n x)).sup A, by omega, fun ℓ hℓ z hm => ?_⟩
  by_contra hz
  have hd : Hcell q T n z ≠ Hcell q T n x := fun h => hz (h ▸ mem_Hcell q T n z)
  have hmn : (gfun q T n z ∩ Hcell q T n x).Nonempty := by
    obtain ⟨w, hw1, hw2⟩ := hm
    exact ⟨w, gfun_anti hc hn (by omega) z hw1, hw2⟩
  have hlt := hidx_lt_of_bad hc hn hmn hd
  have hAle : A (hidx q n z) ≤ (Finset.range (hidx q n x)).sup A :=
    Finset.le_sup (f := A) (Finset.mem_range.mpr hlt)
  exact hA (hidx q n z) z rfl hd hmn ℓ (by omega) hm

/-- Proposition 4.8。 -/
theorem prop_4_8 (hc : Compat2 q T) {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) {x y0 : ℕ → α}
    (hx : Hcell q T n x ⊆ gfun q T m y0) :
    ∃ a, n ≤ a ∧ ∀ ℓ, a ≤ ℓ →
      Hcell q T n x ⊆ ⋃₀ {S | S ∈ lnc q T ℓ (gfun q T m y0) ∧ (S ∩ Hcell q T n x).Nonempty} ∧
      ∀ z, gfun q T ℓ z ∈ lnc q T ℓ (gfun q T m y0) →
        (gfun q T ℓ z ∩ Hcell q T n x).Nonempty → Hcell q T ℓ z ⊆ Hcell q T n x := by
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  obtain ⟨a, hna, ha⟩ := key_4_8 hc hn x
  refine ⟨a, hna, fun ℓ hℓ => ⟨fun w hw => ?_, fun z _ hz => ?_⟩⟩
  · have hwG : w ∈ gfun q T m y0 := hx hw
    rw [← lnc_sUnion hc hm (hmn.trans (hna.trans hℓ)) y0] at hwG
    obtain ⟨S, hS, hwS⟩ := hwG
    exact ⟨S, ⟨hS, w, hwS, hw⟩, hwS⟩
  · have hzx := ha ℓ hℓ z hz
    rw [← Hcell_eq_of_mem hn hzx]
    exact Hcell_anti hn (hna.trans hℓ) z

end Defs.D_0032
