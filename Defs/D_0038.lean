import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Defs.D_0037

namespace Defs.D_0038

/-!
Chen–Wang (arXiv 1809.03763v2) Construction 6.1 B2–B3, Q, Q1, Q2（TeX 2995–3110, 3695–3806 行）:
集合 D(1σ^α_1, G₁)、穴 H(kσ^α_1, q_kσ)、E(αk, p_k) の定義。

* `pieces A1 k` : A1 = slab ∩（第 m+1 層の元）の branch k（第 m+2 層被覆の番号 k の元 S2）の
  piece（P = A1 ∩ S2 ∩ S3, S3 は A1 ∩ S2 の第 m+3 層被覆の元）と番号 v の組。
* `holeBoxesU a k q A1` : branch k, 番号 v ≥ q の piece の G_d の箱の和（論文の ∪G_d(kσ^α_1, jz, qσ)）。
* `holeCells a k q A1` : 同じく箱 ∩ piece の和（∪H_d(kσ^α_1, jz, qσ)）。
* `slabRec base step` : slab の符号 c についての強い帰納法。c 番目の slab では、それより前の
  slab で作った集合の和 `prior` を除いた残り H*(m, ·) と交わる第 m+1 層の元 S だけを使う（B3.2, Q2）。
* `D1slab a c` : B3 の D の slab c の部分（branch 1, 全 piece の G_d の箱）。`D1 a = D(1σ^α_1, G₁)`。
* `Eseq a p k` : E(α(k+1), p) と slab ごとの D(p_{k+1}, m^α, (k+1)_j)。k = 0 で
  E(α1) := g[p 1, D1]（論文の D(p, m^α) = g[p, D(1σ^α_1, G₁)], Prop 6.13.1）。
  k+1 では E(α(k+2)) = g[p (k+2), E(α(k+1))] ∪ ⋃_c H_{k+2}(c)。
  ここで H_{k+2}(c) は slab c の branch k+2 の穴（番号 v ≥ p (k+2)）で、前の slab の
  D(p_{k+2}, m^α, (k+2)_i) を除いた残りと交わる元だけを使う（Q2）。
  論文の q_k = max{p_k, q_n} は p が単調なら p_k。

論文の E(α2, p₂) = g[p₂, D] ∪ H(2σ^α_1, q₂σ) は `Eseq a p 1` にあたる
（`Eseq a p 0` は論文の D(p₁, m^α)）。H(kσ) から g[p_k, E(αn)] を除く操作は和集合を変えない。
-/

open Defs.D_0003 Defs.D_0003.Tree2 Defs.D_0007 Defs.D_0012 Defs.D_0024 Defs.D_0025 Defs.D_0031
  Defs.D_0035 Defs.D_0036 Defs.D_0037

variable {α : Type} [LinearOrder α] (q : ℕ ≃ α) (T : Tree2 α) (m : ℕ) (y0 : ℕ → α)

/-- A1 の branch k の piece と番号。 -/
noncomputable def pieces (A1 : Set (ℕ → α)) (k : ℕ) : Set (Set (ℕ → α) × ℕ) :=
  {Pv | ∃ S2 ∈ lncA q T (m + 2) A1, lab (lncA q T (m + 2) A1) S2 = k ∧
    ∃ S3 ∈ lncA q T (m + 3) (A1 ∩ S2),
      Pv.2 = lab (lncA q T (m + 3) (A1 ∩ S2)) S3 ∧ Pv.1 = A1 ∩ S2 ∩ S3}

/-- branch k, 番号 ≥ r の piece の G_d の箱の和。 -/
noncomputable def holeBoxesU (a : ℕ → ℕ) (k r : ℕ) (A1 : Set (ℕ → α)) : Set (ℕ → α) :=
  ⋃ Pv ∈ {Pv | Pv ∈ pieces q T m A1 k ∧ r ≤ Pv.2}, ⋃₀ Gd q T m a Pv.1 Pv.2

/-- branch k, 番号 ≥ r の piece の穴（箱 ∩ piece）の和。 -/
noncomputable def holeCells (a : ℕ → ℕ) (k r : ℕ) (A1 : Set (ℕ → α)) : Set (ℕ → α) :=
  ⋃ Pv ∈ {Pv | Pv ∈ pieces q T m A1 k ∧ r ≤ Pv.2},
    ⋃ B ∈ Gd q T m a Pv.1 Pv.2, B ∩ Pv.1

/-- slab c で、前の slab の集合の和 `prior` を除いた残りと交わる第 m+1 層の元。 -/
noncomputable def allowed (c : ℕ) (prior : Set (ℕ → α)) : Set (Set (ℕ → α)) :=
  {S | S ∈ lncA q T (m + 1) (slab q T m y0 c) ∧ (S ∩ (slab q T m y0 c \ prior)).Nonempty}

/-- 前の slab までの集合の和（帰納法の補助）。 -/
def slabCum (f : ℕ → Set (ℕ → α) → Set (ℕ → α)) : ℕ → Set (ℕ → α)
  | 0 => ∅
  | c + 1 => slabCum f c ∪ f c (slabCum f c)

/-- slab の符号についての帰納法: slab c の集合は f c (前の slab の集合の和)。 -/
def slabRec (f : ℕ → Set (ℕ → α) → Set (ℕ → α)) (c : ℕ) : Set (ℕ → α) :=
  f c (slabCum f c)

theorem slabCum_eq (f : ℕ → Set (ℕ → α) → Set (ℕ → α)) (c : ℕ) :
    slabCum f c = ⋃ i ∈ Finset.range c, slabRec f i := by
  induction c with
  | zero => simp [slabCum]
  | succ c ih =>
    show slabCum f c ∪ slabRec f c = _
    rw [ih, Finset.range_add_one, Finset.set_biUnion_insert, Set.union_comm]

/-- 論文の D(1σ^α_1, G₁) の slab c の部分（B3）。 -/
noncomputable def D1slab (a : ℕ → ℕ) : ℕ → Set (ℕ → α) :=
  slabRec (fun c prior => ⋃ S ∈ allowed q T m y0 c prior,
    holeBoxesU q T m a 1 0 (slab q T m y0 c ∩ S))

/-- 論文の D(1σ^α_1, G₁)。 -/
noncomputable def D1 (a : ℕ → ℕ) : Set (ℕ → α) := ⋃ c, D1slab q T m y0 a c

/-- E(α(k+1), p) と slab ごとの D(p_{k+1}, m^α, (k+1)_c) の組。 -/
noncomputable def Eseq (a : ℕ → ℕ) (p : ℕ → ℕ) : ℕ → Set (ℕ → α) × (ℕ → Set (ℕ → α))
  | 0 => (gset q T (p 1) (D1 q T m y0 a), fun c => gset q T (p 1) (D1slab q T m y0 a c))
  | k + 1 =>
    let prev := Eseq a p k
    let Hk : ℕ → Set (ℕ → α) := slabRec (fun c prior =>
      ⋃ S ∈ allowed q T m y0 c (prior ∪ prev.2 c),
        holeCells q T m a (k + 2) (p (k + 2)) (slab q T m y0 c ∩ S))
    (gset q T (p (k + 2)) prev.1 ∪ ⋃ c, Hk c,
      fun c => prev.2 c ∪ gset q T (p (k + 2)) (Hk c))

/-- 論文の E(α(k+1), p_{k+1})（k ≥ 1 が論文の E(α2) 以降）。 -/
noncomputable def Eset (a : ℕ → ℕ) (p : ℕ → ℕ) (k : ℕ) : Set (ℕ → α) := (Eseq q T m y0 a p k).1

theorem Eset_succ (a : ℕ → ℕ) (p : ℕ → ℕ) (k : ℕ) :
    ∃ Hk : ℕ → Set (ℕ → α), Eset q T m y0 a p (k + 1) =
      gset q T (p (k + 2)) (Eset q T m y0 a p k) ∪ ⋃ c, Hk c := ⟨_, rfl⟩

end Defs.D_0038
