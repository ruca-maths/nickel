# `L_0028`（Mizokami 2004 の中核）の分解案と検証済み子補題

本ノートおよび同梱の [L0028_sublemmas.lean](L0028_sublemmas.lean) は、`Specs.L_0028`（M₁ 空間で σ-閉離散稠密集合と CP 閉近傍基から正則閉 CP 閉近傍基を構成する補題）に向けた Lean 4 カーネル検証済みの部品群と、残る核心ギャップの整理である。

## 1. カーネル検証済みの子補題（[L0028_sublemmas.lean](L0028_sublemmas.lean)）

すべて `sorry` なし・標準公理（`propext`, `Classical.choice`, `Quot.sound`）のみで `lake env lean Research/L0028_sublemmas.lean` を通過済み：

1. **`M1_paracompact`**: 任意の M₁ 空間はパラコンパクト（`L_0002` + `L_0003` + `L_0010` + `L_0005` の合成）。
2. **`discrete_open_expansion_of_closed_discrete`**: パラコンパクト $T_3$ 空間（特に M₁ 空間）において、$x \notin E$ を満たす任意の閉離散集合 $E$ は、閉包が互いに素かつ離散族をなし、さらに $x \notin \overline{\bigcup_{p \in E} O_p}$ となる開拡大 $\{O_p\}_{p \in E}$ を持つ（collectionwise normality の閉離散版）。
3. **`sigma_cp_basis_monotone_union_closed`**: 任意の M₁ 空間は、単調増大（$\mathcal{B}'_n \subseteq \mathcal{B}'_{n+1}$）かつ各段が任意和で閉じた $\sigma$-CP 開基を持つ。
4. **`stratification_localized_cp`**: 上記の $\mathcal{B}'$、単調減少 stratification $G$、点 $x$ の CP 閉近傍基 $\mathcal{K}$ に対し、
   $$V(K, U) := \bigcup_{n=0}^\infty \bigcup \{ B \in \mathcal{B}'_n \mid B \subseteq U \land B \subseteq G_n(K) \}$$
   と定義すると：
   - $V(K, U)$ は開集合で $\operatorname{int} K \subseteq V(K, U) \subseteq U$（特に $x \in V(K, U)$）。
   - 任意の部分族 $\mathcal{H}$ と任意の $y \in \overline{\bigcup_{(K, U) \in \mathcal{H}} V(K, U)}$ に対し、
     $$(\exists (K, U) \in \mathcal{H},\ y \in \overline{V(K, U)}) \;\lor\; (\exists (K, U) \in \mathcal{H},\ y \in K \setminus \overline{\operatorname{int} K})$$
     が成り立つ。
5. **`regular_closed_base_of_cp_open_base`**: `L_0027` の逆（点 $x$ に CP 開近傍基 $\mathcal{V}$ があれば $\operatorname{closure}'' \mathcal{V}$ は正則閉 CP 閉近傍基になる）。
6. **`regular_closed_base_of_isolated` / `regular_closed_base_of_countable_nhds`**: 孤立点および可算近傍基を持つ点（特に第一可算空間）では `L_0028` の結論が直接成り立つ。

## 2. 棄却された単純構成と反例

- **$K \mapsto \operatorname{int} K$**: `L_0021` の $K = \overline{B} \cap \overline{W_n}$ に対し $K_k = [-2, -1/k] \cup \{0\}$ のように孤立境界点が残ると $\operatorname{int} K_k = (-2, -1/k)$ の CP 性が壊れる。
- **$B \mapsto B \cap W_n(x)$**: $\mathbb{R}$ 上で $\mathcal{B}_n = \{(-2, -1/k) \cup (0, 1) \mid k \ge 1\} \cup \{(0, 2)\}$、$x = -1$、$W_n = (-\infty, 0)$ とすると、$\partial W_n = \{0\}$ で CP 性が壊れる。
- **$\{B \in \mathcal{B}_n \mid x \in B \land B \subseteq W_n(x)\}$ への制限**: 列扇空間 $S_\omega$ で $B_f$ を $\mathcal{B}_{f(0)+1}$ に配置すると近傍基にならない。

## 3. Architect 向けの推奨分解（残る核心 1 ステップ）

`stratification_localized_cp` により、`L_0028` の残る障害は **「$y \in K \setminus \overline{\operatorname{int} K}$（非正則な境界点）を回避する、あるいは $K$ 自身を正則閉な CP 族または $V(K, U)$ が $K$ 全体を覆う構成に置き換えること」** に完全に局所化された。

- 既に検証済みの部品（`discrete_open_expansion_of_closed_discrete`、`sigma_cp_basis_monotone_union_closed`、`stratification_localized_cp`）はそのまま `Proofs/L_xxxx.lean` として再利用可能。
- 残る中核補題は、Mizokami (2004, *Topology Appl.* 141, 197–206) の構成に従って、$\sigma$-閉離散稠密集合 $D = \bigcup_n D_n$ の離散開拡大 $\{O_{n,p}\}$ と $\sigma$-CP 開基 $\mathcal{B}'$ を組み合わせ、$n$ に関して一様な CP 性を保つ正則閉（または開）近傍基を構成する部分である。
