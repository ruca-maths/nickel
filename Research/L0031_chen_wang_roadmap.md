# `L_0031`（Chen–Wang 反例トラック `R_0009` + `R_0010`）検証済み子補題群

本ディレクトリには、親機の新トラック（`R_0009` + `R_0010`: `L_0029` ✅・`L_0032` ✅・未解決リーフ `L_0031`、および `Defs/D_0001`〜`D_0011`）に向けた **Lean 4 カーネル検証済みモジュール 4 本** を収録している。すべて `sorry` なし・警告なし・標準公理（`propext`, `Classical.choice`, `Quot.sound`）のみで検証済みである。

## 1. [ChenWang_Tree2_Instance.lean](ChenWang_Tree2_Instance.lean)（第2〜3節の具体実現と多座標橋渡し）
- **`QTree := List (OrderDual ℕ+)`** 上で `NoMaxOrder QTree`、`qtree_two_points`、`qtree_equiv_nat : Nonempty (ℕ ≃ QTree)` を構成。
- **`qtreeTree2 : Defs.D_0003.Tree2 QTree`**: `Defs.D_0002.Tree`・`Defs.D_0003.Tree2` の全公理の純組合せ的具体実現と `qtree_I_coD`（`Defs.D_0009.I_coD` の具体インスタンス化）。
- **`H_isDiscreteFam` / `H_isTopologicalBasis` / `H_inter_eq_singleton`**: `Defs.D_0011.xtop`（Baire 型積位相 $\rho$）上で $\{H(n, c)\}_c$ が離散開閉分割・開閉開基をなし、$\bigcap_n H(n+1, \operatorname{code}(n+1, q^{-1} \circ x)) = \{x\}$ となること。
- **`rho_t1Space` / `rho_t3Space` / `xtop_le_rhoProd`**: 半開区間位相 $\rho'$ の $T_3$ 性と $\rho \le \rho'^{\mathbb{N}}$。
- **`ICyl_clopen` / `ICyl_coD` / `ICyl_laminar` / `H_subset_unique_ICyl`**: 多座標柱状ブロック `ICyl T n a p` が c.o.D 層状細分をなし、各 `H q n c` が一意な `ICyl T n a p` に含まれること（第2〜3節と第4節 $L_n$ 被覆の橋渡し）。

## 2. [ChenWang_UnboundedMAD.lean](ChenWang_UnboundedMAD.lean)（第9節 Proposition 9.1 の ZFC 修正と非有界分割脱出）
- **`exists_unbounded_AD` / `exists_unbounded_MAD`**: ZFC で $(\mathbb{N}^\mathbb{N}, \le^*)$ における非有界 MAD 族が存在すること（`List ℕ ↪ ℕ` の枝族 + Zorn の補題）。
- **`prop_9_1_repaired`**: 非有界族の可算分割 $\mathcal{M} \subseteq \bigcup_i \mathcal{M}_i$ は必ず非有界な層 $\mathcal{M}_i$ を持つこと（`ChenWang_Audit2_BoundedMAD.lean` の指摘に対する完全な ZFC 修正）。
- **`unbounded_exists_frequently_gt` / `not_hasCPOuterBase_of_unbounded_partition_escape`**: 非有界族の無限回超過補題と、可算分割の非有界層での脱出証人から `¬ Defs.D_0001.HasCPOuterBase y₀` を導く第9節の抽象定理。

## 3. [ChenWang_L0031_Criteria.lean](ChenWang_L0031_Criteria.lean)（`Specs.L_0031` および `¬ Tinf` への直結帰着）
- **`isStratifiable_of_clopen_g_function`**: 単調開閉 $g$-関数から `T1Space Y` と `MSpace.IsStratifiable Y` を自動導出（`Proofs.L_0017` 利用）。
- **`not_hasCPOuterBase_of_escape`**（公理依存なし）: 脱出部分族からの `¬ HasCPOuterBase y₀`。
- **`L0031_of_clopen_g_function_and_escape` / `not_Tinf_of_clopen_g_function_and_escape`**: `Proofs.R_0010`・`L_0032`・`R_0009`・`L_0029`・`L_0004` と合成し、`Specs.L_0031.stmt` および `¬ MSpace.Goals.Tinf_M3_imp_M1` を直接導出。

## 4. [ChenWang_TopologyKit.lean](ChenWang_TopologyKit.lean) & [ChenWang_HoleSystem.lean](ChenWang_HoleSystem.lean)（第6〜7節の近傍系・穴あけ位相フレームワーク）
- **`NhdSystem Y`**: 基本近傍系 `B : Y → Set (Set Y)` から位相 $\tau$ を直接構成し、基底レベルで stratifiability と `¬ Tinf` を判定。
- **`HoleSystem Y`**: 層状分割列 `W : ℕ → Y → Set Y`（`W_of_H_axioms` により `Defs.D_0007.H q (n + 1)` が直接インスタンス化）と穴族 `Holes y` から基本近傍 $W(n, y) \setminus D$ の位相 $\tau$ を構成し、$W(n, y)$ の自動開閉性（`W_clopen`）・`T1Space`・穴吸収 stratifiability（`isStratifiable_of_hole_absorption` / `isStratifiable_of_uniform_hole_absorption`）・`not_Tinf_of_sep_and_escape` を提供。
- **No-Go 定理 1（`idealHoleSystem` の $M_1$ 崩壊）**: 任意の $W$-閉集合 $H_0$ と $H_0^c$ 上の任意のイデアル $\mathcal{I}$（MAD 生成イデアル等を含む）による穴あけ空間 `idealHoleSystem` は、常に stratifiable（`idealHoleSystem_isStratifiable`）であるだけでなく、すべての点 $y_0$ で単層 CP 開外基を持ち（`idealHoleSystem_hasCPOuterBase`）、空間全体が常に $M_1$ 空間になる（`idealHoleSystem_isM1`）ことを証明。したがって `Specs.L_0031` の真の反例には、$H_0$ の外にも非孤立点を持つ多層構造、または $H_0$ に交わる穴が不可欠であることが形式的に確定した。
