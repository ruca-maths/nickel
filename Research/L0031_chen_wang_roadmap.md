# `L_0031`（Chen–Wang 反例トラック `R_0009` + `R_0010`）検証済み子補題群

本ディレクトリには、親機の新トラック（`R_0009` + `R_0010`: `L_0029` ✅・`L_0032` ✅・未解決リーフ `L_0031`、および `Defs/D_0001`〜`D_0011`）に向けた **Lean 4 カーネル検証済みモジュール 13 本** を収録している。すべて `sorry` なし・警告なし・標準公理（`propext`, `Classical.choice`, `Quot.sound`）のみで検証済みである。

## 1. [ChenWang_Tree2_Instance.lean](ChenWang_Tree2_Instance.lean)（第2〜3節の具体実現と多座標橋渡し）
- **`QTree := List (OrderDual ℕ+)`** 上で `NoMaxOrder QTree`、`qtree_two_points`、`qtree_equiv_nat : Nonempty (ℕ ≃ QTree)` を構成。
- **`qtreeTree2 : Defs.D_0003.Tree2 QTree`**: `Defs.D_0002.Tree`・`Defs.D_0003.Tree2` の全公理の純組合せ的具体実現と `qtree_I_coD`（`Defs.D_0009.I_coD` の具体インスタンス化）。
- **`H_isDiscreteFam` / `H_isTopologicalBasis` / `H_inter_eq_singleton`**: `Defs.D_0011.xtop`（Baire 型積位相 $\rho$）上で $\{H(n, c)\}_c$ が離散開閉分割・開閉開基をなし、$\bigcap_n H(n+1, \operatorname{code}(n+1, q^{-1} \circ x)) = \{x\}$ となること。
- **`rho_t1Space` / `rho_t3Space` / `xtop_le_rhoProd`**: 半開区間位相 $\rho'$ の $T_3$ 性と $\rho \le \rho'^{\mathbb{N}}$。
- **`ICyl_clopen` / `ICyl_coD` / `ICyl_laminar` / `H_subset_unique_ICyl`**: 多座標柱状ブロック `ICyl T n a p` が c.o.D 層状細分をなし、各 `H q n c` が一意な `ICyl T n a p` に含まれること（第2〜3節と第4節 $L_n$ 被覆の橋渡し）。
- **`qtree_mem_QStar` / `qtree_Ico_shrink` / `qtree_I_isTopologicalBasis` / `qtree_ICyl_isTopologicalBasis` / `qtree_rhoProd_inter_eq_singleton`**: `QTree` 上で区間族 $\{[p, p_a)\}$ と多座標柱状族 `ICyl` がそれぞれ $\rho'$・$\rho'^{\mathbb{N}}$ の開閉開基をなし、単調減少な開閉柱状列の交わりが 1 点 $\{x\}$ に収束すること。
- **`Env` / `Env_clopen` / `Env_mono_of_H_subset` / `Env_succ_subset` / `qtree_Env_inter_eq_singleton`**: `Defs.D_0007.H_sub_index`（Prop 3.1.4）と `Defs.D_0005.prop_2_2_5` を合成し、各 $H(n, c)$ の標準 `ICyl` 包絡 `Env T q n c` が包含関係を保存し、任意の点 $x$ に沿って $\{x\}$ へ縮小することを証明。

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

## 5. [ChenWang_OuterBase_Localization.lean](ChenWang_OuterBase_Localization.lean)（`HasCPOuterBase` の局所化定理と No-Go 定理 2）
- **`hasCPOuterBase_inter_clopen` / `hasCPOuterBase_iff_clopen_subtype` / `not_hasCPOuterBase_local_escape`**: `HasCPOuterBase y₀` が開閉近傍 $W \ni y_0$ への制限・部分空間化と完全に同値であり、`¬ HasCPOuterBase y₀` ならば任意の開閉近傍 $W$ の内部 $W \setminus \{y_0\}$ に CP 破綻点 $z$ が存在すること。
- **`hasCPOuterBase_of_isolated_compl` / `hasCPOuterBase_of_clopen_nhd_isolated_compl` / `exists_nonisolated_in_clopen_of_not_hasCPOuterBase`**: 任意の位相空間において $y_0$ のある開閉近傍 $W$ で $W \setminus \{y_0\}$ の全点が孤立していれば `HasCPOuterBase y₀` が成り立つ（よって `L_0031` 反例の $y_0$ は必ず他の非孤立点の集積点）。
- **`hasCPOuterBase_of_no_nonisolated_hole_interior`（No-Go 定理 2）** & **`exists_nonisolated_hole_interior_of_not_hasCPOuterBase`**: 層状開分割 $W(n, y)$ と基本近傍系 $\{W(n, y_0) \setminus D \mid D \in \mathrm{Holes}\}$ を持つ任意の位相空間において、あるレベル $N$ で「どの穴 $D$ の内部 $\operatorname{int} D$ も $W(N, y_0)$ 内の非孤立点を含まない」ならば `HasCPOuterBase y₀` が成り立つ（`idealHoleSystem_hasCPOuterBase` の大幅な一般化）。対偶として、層状穴あけによる `L_0031` 反例では**すべての $N$ について** $W(N, y_0) \setminus \{y_0\}$ の非孤立点を内部に含む穴 $D$ が不可欠。

## 6. [ChenWang_NonCP_Model.lean](ChenWang_NonCP_Model.lean)（有限 $\Delta$-系補題と `¬ HasCPOuterBase` の初の具体モデル `BoxFan I`）
- **`delta_system_of_card_eq` / `exists_infinite_delta_system`**: 非可算有限集合族に対する有限 $\Delta$-系補題の純 ZFC 証明。
- **`cantorCube_not_hasCPOuterBase`**: 任意の非可算添字集合 $I$ に対し、Cantor 立方体 $I \to \mathrm{Bool}$ の零点が `¬ Defs.D_0001.HasCPOuterBase` を満たすことを証明。
- **`BoxFan I := Option (ℕ × (I → Bool))`**: `Specs.L_0031` の stratifiability 以外の**全条件**を具体的に満たす 0 次元 $T_3$ 空間を構成し、`boxFan_t3Space`・`boxFan_W_clopen`・`boxFan_W_inter`（$\bigcap_n W_n = \{\mathrm{none}\}$）・`boxFan_not_hasCPOuterBase`・`boxFan_not_hasSigmaCPLocalBase`（`Proofs.L_0032` 経由）・`boxFan_not_isM1`（`Proofs.L_0029` 経由）をすべてカーネル検証済みで証明。

## 7. [ChenWang_Refinement_Stratifiable.lean](ChenWang_Refinement_Stratifiable.lean)（細分位相の Stratifiability 定理と `xtop` 部分空間直結帰着）
- **`isStratifiable_of_refinement` / `isStratifiable_of_refinement_g`**: stratifiable 位相 $\tau_0$ の任意の細分 $\tau \le \tau_0$ に対し、単調 $\tau$-開作用素 $R_n(F)$（または $\tau$-開 $g$-関数 $g_n(y)$）が $\tau$-閉集合 $F$ とその **$\tau_0$-境界 $\overline{F}^{\tau_0} \setminus F$** のみを分離すれば $(Y, \tau)$ が stratifiable になることを証明（$\tau_0$-閉包の外側は $\tau_0$ が自動分離）。
- **`isStratifiable_of_laminar_clopen_partition` / `xtop_isStratifiable` / `xtop_subtype_isStratifiable`**: `Defs.D_0011.xtop α` およびその任意の部分空間 $Y \subseteq \mathbb{N} \to \alpha$ が stratifiable であること。
- **`xtop_subtype_refinement_L0031` / `xtop_subtype_refinement_not_Tinf`**: 任意の部分空間 $Y \subseteq \mathbb{N} \to \alpha$ 上の細分位相 $\tau \le \mathrm{xtop}_Y$ に対し、境界分離 $g$-関数と `¬ HasCPOuterBase y₀` から `Specs.L_0031.stmt` および `¬ MSpace.Goals.Tinf_M3_imp_M1` を直接導出。

## 8. [ChenWang_BoxFan_Equiv.lean](ChenWang_BoxFan_Equiv.lean)（`BoxFanGen` による厳密同値 `L_0020 ↔ L_0031 ↔ L_0030`・`L_0019` 迂回定理）
- **`BoxFanGen Z := Option (ℕ × Z)`**（基点 $z_0 \in Z$ に対する一般化ボックス扇）を構成し、`boxFanGen_isStratifiable`（Heath–Lutzer–Zenor 単調正規性作用素を経由して、**任意の** stratifiable 空間 $Z$ に対し `BoxFanGen Z` が常に stratifiable になること）を証明。
- **`boxFanGen_W_clopen` / `boxFanGen_W_inter`**: 頂点 `none` は常に減少開閉近傍列 $\bigcap_n W_n = \{\mathrm{none}\}$ を持つ。
- **`boxFanGen_hasCPOuterBase_iff`**: 対角化議論により、**任意の位相空間 $(Z, z_0)$ について** `HasCPOuterBase (none : BoxFanGen Z) ↔ HasCPOuterBase z₀` が厳密に成り立つことを証明。
- **`L0020_iff_L0031` / `L0020_iff_L0030` / `L0030_iff_L0031`**: 親機の 3 つの反例仕様 `L_0020`・`L_0030`・`L_0031` がすべて ZFC で完全に同値であることを確立。
- **`L0020_imp_not_Tinf` / `Tinf_imp_L0019`**: Mizokami (2004) / `L_0019` / `L_0028` を一切経由せずに `Specs.L_0020.stmt → ¬ MSpace.Goals.Tinf_M3_imp_M1`（および対偶 `Tinf → L_0019`）を直接導出。
- **`boxFanGen_isM1_iff`**: `MSpace.IsM1 (BoxFanGen Z) ↔ MSpace.IsM1 Z ∧ Defs.D_0001.HasCPOuterBase z₀`（`BoxFanGen` が `L_0019` の関手的テストベッドであることの完全特徴付け）。

## 9. [ChenWang_OuterBase_Permanence.lean](ChenWang_OuterBase_Permanence.lean)（`HasCPOuterBase` の永続性・障害定理）
- **`hasCPOuterBase_of_decreasing_base` / `hasCPOuterBase_of_firstCountable`**: 任意の $T_3$ 空間で第 1 可算点（近傍フィルターが可算生成）は常に `HasCPOuterBase` を持つ（したがって `L_0020` / `L_0030` / `L_0031` の反例点 $y_0$ は非第 1 可算）。
- **`hasCPOuterBase_of_compact_nhd_gDelta` / `stratifiable_no_compact_nhd_of_not_hasCPOuterBase`**: 任意の stratifiable 空間でコンパクト近傍を持つ点は第 1 可算かつ `HasCPOuterBase` を満たす（よって反例点 $y_0$ はコンパクト近傍を持たない）。
- **`hasCPOuterBase_prod` / `hasCPOuterBase_of_isClosedMap_isOpenMap`**: `HasCPOuterBase` は有限直積および連続開閉写像で保存される。

## 10. [ChenWang_SigmaCP_Permanence.lean](ChenWang_SigmaCP_Permanence.lean)（開部分空間・可算積に対する `HasCPOuterBase` / `HasSigmaCPLocalBase` 永続性）
- **`hasCPOuterBase_open_subspace` / `hasCPOuterBase_iff_open_subspace` / `hasSigmaCPLocalBase_open_subspace`**: 任意の開部分空間への遺伝性と、正則空間における純粋局所性。
- **`hasSigmaCPLocalBase_of_isClosedMap_isOpenMap` / `hasSigmaCPLocalBase_prod`**: 連続開閉写像および有限直積での保存性。
- **`hasSigmaCPLocalBase_countable_pi` / `hasCPOuterBase_countable_pi_of_clopen_gDelta`**: 可算積 $\prod_{k \in \mathbb{N}} X_k$ における `HasSigmaCPLocalBase` の保存性、および各座標が開閉 $G_\delta$ 点を持つときの単層 `HasCPOuterBase` の保存性（`Proofs.L_0032` 結合）。

## 11. [HeathJunnila_M1_ClosedSubspace.lean](HeathJunnila_M1_ClosedSubspace.lean)（Heath–Junnila 1981 & Borges 1966：`M₁` 閉部分空間・遺伝・レトラクト問題と `Tinf` の厳密同値）
- **`HeathJunnila X := X × Option ℕ`**（孤立層 `some n` + 極限層 `none`）を構成し、`heathJunnila_t3Space`・`heathJunnila_isM1_of_isM2`・`heathJunnila_isM1_of_isM3`（任意の $M_2$/$M_3$ 空間 $X$ が $M_1$ 空間 `HeathJunnila X` の閉部分空間・連続レトラクトとして埋め込まれること、`hjLimitHomeomorph` / `hjRetract`）を証明。
- **`isStratifiable_subtype`**（Borges 1966）: stratifiable 空間の任意の部分空間は stratifiable。
- **`Tinf_iff_closed_subspace_M1` / `Tinf_iff_hereditary_M1` / `Tinf_iff_retract_M1`**: Ceder の未解決問題 `Tinf`（$M_3 \Rightarrow M_1$）が「$M_1$ の閉部分空間は $M_1$ か」「$M_1$ の任意の部分空間は $M_1$ か」「$M_1$ の連続レトラクトは $M_1$ か」の 3 問題とすべて完全に同値であることを確立。

## 12. [CollapseQuotient_OuterBase.lean](CollapseQuotient_OuterBase.lean)（閉集合縮約商 $X/F$ の Stratifiability と閉集合 CP 開外基定理）
- **`CollapseQuotient X F := Option { x : X // x ∉ F }`**: 閉集合 $F$ を 1 点 `none` に潰す縮約商を構成し、`collapseProj_isClosedMap`・`collapseQuotient_t1Space`・`collapseQuotient_isStratifiable`（Heath–Lutzer–Zenor 単調正規性作用素による stratifiability の保存）を証明。
- **`collapseQuotient_hasCPOuterBase_iff`**: 商空間の点 `none` が単層 CP 開外基を持つことと、元空間の閉集合 $F$ が単層 CP 開外基を持つことが厳密同値。
- **`closed_hasCPOuterBase_of_not_L0020`**: `¬ Specs.L_0020.stmt` のもとで、任意の stratifiable 空間の任意の非空閉集合が単層 CP 開外基を持つことを導出。
