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

### 追加の構造定理（[M3_M1_structure.lean](M3_M1_structure.lean)）

同じく `sorry` なし・標準公理のみで検証済み：

7. **`M3_is_sigma_space`（Heath 1969）**: 任意の M₃ 空間は $\sigma$-離散な閉網を持つ。
8. **`M3_closed_subset_has_cp_closed_nhds`**: 任意の M₃ 空間の任意の閉集合 $F$ は CP 閉近傍基を持つ（`L_0021` の閉集合・M₃ 版への一般化）。
9. **`zero_dim_M1_has_cp_clopen_base`**: ゼロ次元 M₁ 空間（clopen $\sigma$-CP 基を持つ空間）の各点は CP な clopen（よって開かつ正則閉）近傍基を持つ（ゼロ次元版 `L_0028`）。
10. **`collectionwise_normal_of_paracompact_t3`**: パラコンパクト $T_3$ 空間における任意の離散閉集合族は、閉包が互いに素かつ離散な開拡大を持つ。
11. **`M3_is_M1_of_closed_cp_outer_base`（Gruenhage–Ito 型の M₁ 特徴付け）**: 任意の閉集合が CP 開外基を持つ M₃ 空間は M₁ 空間である。
12. **`closed_cp_outer_base_of_pointwise_cp_and_dense_trace`（Ito の拡張補題）**: 任意の M₃ 空間において、部分集合 $F$ が CP 閉近傍基 $\mathcal{K}$ を持ち、さらに各点が CP 開近傍基を持つ $\sigma$-閉離散集合 $E = \bigcup_k E_k$ がすべての $K \in \mathcal{K}$ に対し $K \subseteq \overline{\operatorname{int} K \cup (K \cap E)}$ を満たすならば、$F$ は CP 開外基を持つ。
13. **`M3_is_M1_of_pointwise_cp_and_dense_trace`**: 上記の条件がすべての閉集合 $F$ で成り立つ M₃ 空間は M₁ である。
14. **`L0028_of_boundary_cp_trace` / `L0028_of_sigma_closed_discrete_firstCountable_compl`**: `Specs.L_0028` への条件付き帰着（境界トレースが $\sigma$-閉離散 CP 点集合で覆われる場合、特に $X \setminus \{x\}$ が第一可算点の $\sigma$-閉離散和である任意の M₃ 空間で `L_0028` の結論が成り立つ）。
15. **`M1_has_sigma_cp_regular_open_basis`**: 任意の M₁ 空間は正則開集合（$\operatorname{int}(\overline{R}) = R$）からなる $\sigma$-CP 開基を持つ。
16. **`M1_open_subspace`**: M₁ 空間の任意の開部分空間は M₁ 空間である。
17. **`M3_is_M1_of_countable_closed_cover_with_cp_outer_bases`**: 可算個の閉集合 $F_k$ で覆われ、各 $F_k$ に含まれる任意の閉集合が $X$ 内で CP 開外基を持つ M₃ 空間は M₁ 空間である（Mizokami 2004 の可算閉和定理の帰着骨格）。
18. **`M1_prod` / `hasCPOpenLocalBase_prod`（Ceder 1961）**: M₁ 空間の有限積は M₁ 空間であり、点の CP 開近傍基も有限積で保存される。
19. **`sigma_closed_discrete_normal_is_strongly_zero_dim`**: 任意の $\sigma$-閉離散正規空間は強ゼロ次元（$\operatorname{Ind}(X) = 0$、任意の閉集合と開近傍が clopen 集合で分離可能）である。
20. **`hasCPOpenLocalBase_iff_open_subspace`**: $T_3$ 空間において、点の CP 開近傍基の存在は開部分空間への制限・拡張で完全に不変な局所的性質である。
21. **`hasCPOpenLocalBase_of_isClosedMap_isOpenMap` / `M1_of_isClosedMap_isOpenMap_surjective`**: 連続かつ開閉写像のもとで、点の CP 開近傍基および M₁ 空間性（$T_3$ 全射像）が保存される。
22. **`M1_of_locally_M1`**: パラコンパクト $T_3$（特に M₃）空間が局所 M₁ ならば M₁ 空間である。
23. **`M3_is_M1_of_closed_discrete_sigmaCP_and_M1_compl`**: M₃ 空間 $X$ において閉離散集合 $D$ の各点が $\sigma$-CP 開局所基を持ち、補空間 $X \setminus D$ が M₁ ならば $X$ は M₁ 空間である。
24. **`M1_countable_pi`（Ceder 1961）**: M₁ 空間の可算直積 $\prod_{i \in \mathbb{N}} X_i$ は M₁ 空間である。
25. **`M1_sigma`**: M₁ 空間の任意の直和（位相和）$\bigoplus_{i \in \iota} X_i$ は M₁ 空間である。

## 2. 棄却された単純構成と反例

- **$K \mapsto \operatorname{int} K$**: `L_0021` の $K = \overline{B} \cap \overline{W_n}$ に対し $K_k = [-2, -1/k] \cup \{0\}$ のように孤立境界点が残ると $\operatorname{int} K_k = (-2, -1/k)$ の CP 性が壊れる。
- **$B \mapsto B \cap W_n(x)$**: $\mathbb{R}$ 上で $\mathcal{B}_n = \{(-2, -1/k) \cup (0, 1) \mid k \ge 1\} \cup \{(0, 2)\}$、$x = -1$、$W_n = (-\infty, 0)$ とすると、$\partial W_n = \{0\}$ で CP 性が壊れる。
- **$\{B \in \mathcal{B}_n \mid x \in B \land B \subseteq W_n(x)\}$ への制限**: 列扇空間 $S_\omega$ で $B_f$ を $\mathcal{B}_{f(0)+1}$ に配置すると近傍基にならない。

## 3. Architect 向けの推奨分解（残る核心 1 ステップ）

`stratification_localized_cp` により、`L_0028` の残る障害は **「$y \in K \setminus \overline{\operatorname{int} K}$（非正則な境界点）を回避する、あるいは $K$ 自身を正則閉な CP 族または $V(K, U)$ が $K$ 全体を覆う構成に置き換えること」** に完全に局所化された。

- 既に検証済みの部品（`discrete_open_expansion_of_closed_discrete`、`sigma_cp_basis_monotone_union_closed`、`stratification_localized_cp`）はそのまま `Proofs/L_xxxx.lean` として再利用可能。
- 残る中核補題は、Mizokami (2004, *Topology Appl.* 141, 197–206) の構成に従って、$\sigma$-閉離散稠密集合 $D = \bigcup_n D_n$ の離散開拡大 $\{O_{n,p}\}$ と $\sigma$-CP 開基 $\mathcal{B}'$ を組み合わせ、$n$ に関して一様な CP 性を保つ正則閉（または開）近傍基を構成する部分である。
