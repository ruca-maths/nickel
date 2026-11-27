# `L_0031`（Chen–Wang 反例トラック `R_0009` + `R_0010`）検証済み子補題群

本ディレクトリには、親機の新トラック（`R_0009` + `R_0010`: `L_0029` ✅・`L_0032` ✅・未解決リーフ `L_0031`、および `Defs/D_0001`〜`D_0032`）に向けた **Lean 4 カーネル検証済みモジュール 40 本** を収録している。すべて `sorry` なし・警告なし・標準公理（`propext`, `Classical.choice`, `Quot.sound`）のみで検証済みである。

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

## 13. [ChenWang_Clopen_Shells.lean](ChenWang_Clopen_Shells.lean)（開閉族 CP 特徴付けと開閉殻分解二分法）
- **`closurePreserving_iff_sUnion_isClosed_of_clopen` / `isM1_of_clopen_basis_sUnion_closed`**: 開閉集合族の closure-preserving 性が「任意部分和が閉」と同値であり、$\sigma$-部分和閉な開閉開基を持つ $T_1$ 空間は自動的に $T_3$ かつ $M_1$。
- **`isM1_of_countable_clopen_M1_cover` / `isM1_of_clopen_shells_and_hasCPOuterBase`**: 可算個の開閉 $M_1$ 部分空間で覆われる $T_3$ 空間は $M_1$。特に開閉殻 `clopenShell W n`（$W_0^c, W_n \setminus W_{n+1}$）がすべて $M_1$ で $y_0$ が `HasCPOuterBase y₀` を持てば全体が $M_1$。
- **`L0031_or_shell_not_isM1`**: 開閉 $G_\delta$ 点 $y_0$ を持つ非 $M_1$ stratifiable 空間は、$(Y, y_0)$ 自身が `Specs.L_0031.stmt` の証人となるか、ある開閉殻 `clopenShell W n` が既に非 $M_1$ であるかの二分法を満たす。

## 14. [Stratifiable_Sigma_And_Wedge.lean](Stratifiable_Sigma_And_Wedge.lean)（任意濃度直和 `Sigma` および基点付きウェッジ `Wedge` の永続性）
- **`isStratifiable_sigma` / `isM1_sigma`**: 任意濃度の直和 $\Sigma_{i \in \iota} X_i$ は `IsStratifiable` および `IsM1` を保存。
- **`Wedge X x₀` / `wedge_isStratifiable`**: 任意濃度 $\iota$（可算・非可算を問わず）の基点付きウェッジ（一般化扇 $S_\omega, S_{\omega_1}, S_{\mathfrak{c}}$ を含む）が常に stratifiable であることを証明。
- **`wedge_hasCPOuterBase_iff`**: `HasCPOuterBase (none : Wedge X x₀) ↔ ∀ i, HasCPOuterBase (x₀ i)`。
- **`wedge_isM1_of_isM1_and_hasCPOuterBase`**: 各枝が $M_1$ で基点が CP 開外基を持てば、任意濃度のウェッジ全体が $M_1$（よって任意濃度の点列扇 $S_\kappa$ はすべて $M_1$）。

## 15. [Stratifiable_Countable_Pi.lean](Stratifiable_Countable_Pi.lean)（Borges 1966・Ceder 1961 の可算積保存定理）
- **`isStratifiable_prod` / `isStratifiable_countable_pi`**（Borges 1966）: 有限積および可算積 $\prod_{k \in \mathbb{N}} X_k$ が `MSpace.IsStratifiable` を保存することを単調 $g$-関数と `Proofs.L_0017` により証明。
- **`isM1_prod` / `isM1_countable_pi`**（Ceder 1961）: 有限積および可算積 $\prod_{k \in \mathbb{N}} X_k$ が `MSpace.IsM1` を保存することを有限プレフィックス柱状族の帰納的 CP 性と `Denumerable (List ℕ)` により証明。

## 16. [ChenWang_D0013_Compat_Instance.lean](ChenWang_D0013_Compat_Instance.lean)（`Defs.D_0013.Compat` の空虚性反証と `QTree` / `ℚ ∩ [0,1)` 上の修復版実例構成）
- **`compat_not_exists`**: 任意の線形順序 $\alpha$、`T : Defs.D_0003.Tree2 α`、全単射 `q : ℕ ≃ α` に対し **`¬ Defs.D_0013.Compat q T`** を証明（0-indexed な `q : ℕ ≃ α` に対して 1-indexed の不等式 `j < q.symm (T.child p j)` を課したため、`q 1` で必ず矛盾が生じる仕様欠陥を発見）。
- **`CompatRepaired` / `prop_3_2_1_repaired`**: `idx_lt_num` を `idx_le_num : j ≤ q.symm (T.child p j)` に修正しても Proposition 3.2.1 の結論が完全に保たれることを証明。
- **`qtreeEnum` / `qtreeEnum_compatRepaired` / `exists_compatRepaired_qtree`**: `QTree := List (OrderDual ℕ+)` 上の重み次数全単射 `qtreeEnum : ℕ ≃ QTree` を構成し、`CompatRepaired qtreeEnum qtreeTree2` の全 4 公理を満たす具体モデルを確立。
- **`nonempty_qtree_orderIso_ratIco` / `exists_ratIco_tree2_compatRepaired` / `exists_qtree_tree2_compat2` / `exists_ratIco_tree2_compat2`**: Cantor の往復同型定理により `QTree ≃o ℚ ∩ [0, 1)` を構成し、`Defs/D_0013.lean`・`Defs/D_0024.lean` の **`QTree` および `ℚ ∩ [0, 1)` 上の `Tree2` と `Defs.D_0024.Compat2` の存在**を完全に証明。

## 17. [Ito1985_SigmaSpace_M1.lean](Ito1985_SigmaSpace_M1.lean)（Heath 1969・Collectionwise Normality・Ito 1985・局所コンパクト/コンパクト $M_1$・`¬ L_0020 → Tinf`）
- **`stratifiable_discrete_open_expansion`**: 任意の stratifiable 空間における離散閉集合族の離散開拡大（collectionwise normality）を減少 stratification と単調正規性作用素 `Hsep` から直接証明。
- **`stratifiable_has_sigma_discrete_closed_network`**（Heath 1969）: 任意の stratifiable 空間が $\sigma$-離散閉ネットワークを持つ（$\sigma$-空間である）ことを、`Proofs.L_0008`（$M_3 \Rightarrow M_2$）と `A m k x := C_m(x) \ G_k(D_m(x))` により完全形式化。
- **`isM1_of_stratifiable_and_closed_hasCPOuterBase` / `isM1_of_stratifiable_and_network_hasCPOuterBase`**（Ito 1985 閉集合版・一般ネットワーク版）: stratifiable 空間で各閉集合（またはある $\sigma$-離散閉ネットワークの各元）が単層 CP 開外基を持てば $M_1$。
- **`not_L0020_imp_Tinf`**: 縮約商 `CollapseQuot X F` と結合し、**`¬ Specs.L_0020.stmt → MSpace.Goals.Tinf_M3_imp_M1`** を証明。`ChenWang_BoxFan_Equiv.lean` の `L0020_imp_not_Tinf` と合わせて、Ceder の未解決問題 `Tinf` が **`Tinf ↔ ¬ L_0020 ↔ ¬ L_0030 ↔ ¬ L_0031`** と ZFC 内で厳密同値であることを確立。
- **`stratifiable_has_sigma_closed_discrete_dense` / `isM1_of_stratifiable_locallyCompact` / `isM1_of_stratifiable_compact` / `isM1_of_countable_t3_hasCPOuterBase`**: stratifiable 空間の $\sigma$-閉離散稠密部分集合（`Proofs.L_0026` の $M_3$ への一般化）、局所コンパクト・コンパクト stratifiable 空間の $M_1$ 性、および可算 $T_3$ 空間での CP 外基 $\Rightarrow M_1$ を証明。

## 18. [Ito1985_ClosedSet_Criteria.lean](Ito1985_ClosedSet_Criteria.lean)（閉集合 CP 外基の代数閉包性と構造的 $M_1$ 判定定理）
- **`hasCPOuterBaseSet_singleton_iff` / `hasCPOuterBaseSet_union` / `hasCPOuterBaseSet_finset_biUnion`**: 任意の位相空間で `HasCPOuterBaseSet` が有限和で閉じ、1 点集合では `Defs.D_0001.HasCPOuterBase` と同値であること。
- **`hasCPOuterBaseSet_sUnion_discrete` / `hasCPOuterBaseSet_of_closed_discrete`**: stratifiable 空間で離散閉集合族の和（および各点が CP 外基を持つ閉離散部分集合）が `HasCPOuterBaseSet` を保存すること。
- **`hasCPOuterBaseSet_of_compact_with_compact_nhd`**: stratifiable 空間でコンパクト近傍を持つ任意のコンパクト集合が減少可算（したがって CP）開外基を持つこと。
- **`isM1_of_stratifiable_sigma_closed_discrete` / `isM1_of_stratifiable_locallyCompact_compl`**: $\sigma$-閉離散な stratifiable 空間（各点 CP 外基あり）は $M_1$、および 1 点 $y_0$ を除いて局所コンパクトな stratifiable 空間は `HasCPOuterBase y₀ → IsM1 X`（対偶：非 $M_1$ ならば自動的に `¬ HasCPOuterBase y₀`）を満たすことを証明。

## 19. [Borges_PerfectMap_And_ClosedSum.lean](Borges_PerfectMap_And_ClosedSum.lean)（Borges 1966：完全写像による像と局所有限閉被覆の層化可能性保存）
- **`isStratifiable_of_perfectMap`**: stratifiable 空間からの完全連続全射（閉連続全射かつ各ファイバーがコンパクト）の $T_1$ 像は常に stratifiable。
- **`isStratifiable_of_locallyFinite_closed_cover` / `isStratifiable_of_union_closed`**: 局所有限な閉 stratifiable 部分空間族で覆われる $T_1$ 空間（特に 2 つの閉 stratifiable 部分空間の和 $X = F_1 \cup F_2$）は常に stratifiable。

## 20. [M1_OpenSubspace_And_LocallyM1.lean](M1_OpenSubspace_And_LocallyM1.lean)（$M_1$ の開部分空間遺伝性と局所 $M_1$ パラコンパクト／層化可能空間定理）
- **`isM1_open_subspace`**: $M_1$ 空間の任意の開部分空間は $M_1$。
- **`isM1_of_locallyFinite_shrunk_open_M1_cover` / `isM1_of_paracompact_locallyM1` / `isM1_of_stratifiable_locallyM1`**: 局所有限な収縮開 $M_1$ 被覆を持つ $T_3$ 空間、特に任意の局所 $M_1$ パラコンパクト $T_3$ 空間・局所 $M_1$ stratifiable 空間は常に $M_1$（`Proofs.L_0005` 結合）。
- **`exists_point_no_M1_open_nhd_of_not_isM1`**: 対偶として、任意の非 $M_1$ stratifiable 空間には「いかなる開近傍も $M_1$ にならない点 $x_0$」が必ず存在する（`Tinf` の局所化定理）。

## 21. [M1_Permanence_And_Retracts.lean](M1_Permanence_And_Retracts.lean)（$M_1$/層化可能空間の永続性定理と Jones の補題）
- **`isM1_of_sigma_locallyFinite_basis` / `isM1_of_secondCountable_t3`**: $\sigma$-局所有限開基を持つ $T_3$ 空間（Nagata–Smirnov）および第 2 可算 $T_3$ 空間は常に $M_1$。
- **`isM1_of_isClosedMap_isOpenMap` / `isStratifiable_of_isClosedMap_isOpenMap`**: 閉開連続全射は $M_1$（$T_3$ 値域）および stratifiable（$T_1$ 値域、コンパクトファイバー不要）を保存。
- **`isM1_of_homeomorph` / `isStratifiable_of_homeomorph`**: 同相不変性。
- **`jones_lemma` / `not_normalSpace_of_dense_closedDiscrete`**: 正規空間における稠密集合 $Q$ と閉離散集合 $D$ に対する単射 $\mathcal{P}(D) \hookrightarrow \mathcal{P}(Q)$ および濃度障害による非正規性判定（Sorgenfrey 平面が非正規・非層化であることの基盤）。

## 22. [Sorgenfrey_Not_Stratifiable.lean](Sorgenfrey_Not_Stratifiable.lean)（Sorgenfrey 直線 `(ℝ, Defs.D_0009.rho ℝ)` の非層化性・非 $M_1$ 性）
- **`ratGrid_dense` / `antiDiag_closed_discrete` / `sorgenfrey_prod_not_normal`**: Sorgenfrey 平面 `(ℝ, rho ℝ) × (ℝ, rho ℝ)` において $\mathbb{Q} \times \mathbb{Q}$ が可算稠密かつ反対角線 $\{(x, -x)\}$ が連続体濃度の閉離散集合であることから、Jones の補題により非正規であることを証明。
- **`sorgenfrey_not_isStratifiable` / `sorgenfrey_not_isM1`**: 有限積の層化可能性保存と層化可能 $\Rightarrow$ 正規から、Sorgenfrey 直線 `(ℝ, Defs.D_0009.rho ℝ)` が stratifiable でも $M_1$ でもないことをカーネル検証済みで確定（可算順序 `QTree`/`ℚ ∩ [0,1)` 上の `rho` が第 2 可算 $M_1$ であるのとの対比）。

## 23. [Stratifiable_Hereditary_And_GDeltaDiag.lean](Stratifiable_Hereditary_And_GDeltaDiag.lean)（層化可能・$M_2$・$M_3$ の遺伝性と $G_\delta$-対角線定理）
- **`isStratifiable_subtype` / `isM3_subtype` / `isM2_subtype`**: stratifiable・$M_3$・$M_2$ が任意の部分空間に遺伝することを証明（$M_1$ の遺伝性が `Tinf` と同値であることとの対比）。
- **`paracompact_subtype_of_isStratifiable` / `perfectlyNormal_subtype_of_isStratifiable`**: stratifiable 空間は遺伝的パラコンパクトかつ遺伝的完全正規。
- **`gDelta_diagonal_of_isStratifiable`**: 任意の stratifiable 空間は $G_\delta$-対角線 `IsGδ (Set.diagonal X)` を持つ。

## 24. [Borges_Adjunction_Space.lean](Borges_Adjunction_Space.lean)（Borges 1966 Theorem 3.7：接着空間 $X \cup_f Y$ の層化可能性保存）
- **`AdjunctionSpace X Y A` / `adjTop`**: 閉部分集合 $A \subseteq X$ と任意の連続貼り合わせ写像 $f : A \to Y$（閉写像不要）による位相押し出し $X \cup_f Y$ の商位相と開閉集合の特徴付け。
- **`adjunctionSpace_t1Space` / `adjunctionSpace_isStratifiable`**: $X, Y$ が stratifiable ならば任意の閉部分集合 $A \subseteq X$ と連続写像 $f : A \to Y$ に対する接着空間 $X \cup_f Y$ が常に stratifiable であることを証明（縮約商 $X/A$ の大幅な一般化）。

## 25. [Borges_WeakTopology_DirectLimit.lean](Borges_WeakTopology_DirectLimit.lean)（Borges 1966 Theorem 7.2：可算増大閉被覆の弱位相／帰納極限の層化可能性）
- **`isStratifiable_of_weak_increasing_closed_cover`**: 増大する閉 stratifiable 部分空間列 $F_0 \subseteq F_1 \subseteq \cdots$（$\bigcup_m F_m = X$）による弱位相（可算 CW 複体・$\mathbb{R}^\infty$・$k_\omega$-空間を含む）を持つ $T_1$ 空間 $X$ が常に stratifiable であることを、1 ステップ単調開拡大 `extStep` と閉包分離帰納延長 `extStep_sep_extend` により完全形式化。

## 26. [KOmega_Stratifiable_IsM1.lean](KOmega_Stratifiable_IsM1.lean)（Dickson の補題と $k_\omega$ 層化可能空間の $M_1$ 定理）
- **`dickson_fin_nat`**: $\mathbb{N}^d$ の任意部分集合が有限個の下界支配元を持つこと（Dickson の補題）を純組合せ的帰納法で証明。
- **`kOmega_stratifiable_and_closed_outerBase`**: 増大コンパクト stratifiable 層 $K_0 \subseteq K_1 \subseteq \cdots$ の弱位相空間（$k_\omega$ 層化可能空間：$\mathbb{R}^\infty$、$S_\omega$、任意の可算 CW 複体を含む）において、空間自身が stratifiable であり、かつ**任意の閉集合** $C \subseteq X$ が Dickson の補題＋厳密閉包トレースにより単層 CP 開外基を持つことを証明。
- **`isM1_of_kOmega_stratifiable`**: Ito (1985) 閉集合版と結合し、任意の $k_\omega$ 層化可能空間が $M_1$ 空間であることを完全証明。

## 27. [Borges_ClosedImage_And_MonotoneNormal.lean](Borges_ClosedImage_And_MonotoneNormal.lean)（Borges 1966 Theorem 3.1・Heath–Lutzer–Zenor 1973 Theorem 2.5：閉連続像の層化可能性保存）
- **`IsMonotonicallyNormal` / `IsSemiStratifiable` / `isStratifiable_iff_monotonicallyNormal_and_semiStratifiable`**（Heath–Lutzer–Zenor 1973）: 層化可能空間 $\iff$ 単調正規かつ半層化可能の完全同値を形式化。
- **`t1Space_of_isClosedMap` / `monotonicallyNormal_of_isClosedMap` / `semiStratifiable_of_isClosedMap`**: 任意の閉連続全射が $T_1$・単調正規性・半層化可能性を保存することを証明。
- **`isStratifiable_of_isClosedMap`**（Borges 1966 Theorem 3.1）: コンパクトファイバーの仮定なしで、**任意の**閉連続全射 $f : X \to Y$ が層化可能性を保存することを完全証明（`Borges_PerfectMap_And_ClosedSum.lean` および `CollapseQuotient_OuterBase.lean` の大幅な一般化）。

## 28. [Ind0_SigmaDiscrete_And_Countable.lean](Ind0_SigmaDiscrete_And_Countable.lean)（$\sigma$-閉離散・可算正規／層化可能空間の強 0 次元性 $\operatorname{Ind} X = 0$）
- **`IsStronglyZeroDim` / `stronglyZeroDim_of_normal_sigma_closedDiscrete`**: 閉離散集合の可算和 $X = \bigcup_n F_n$ で覆われる任意の正規空間において、任意の互いに素な閉集合が閉開集合で分離される（$\operatorname{Ind} X = 0$）ことを帰納的閉包分離により証明。
- **`stronglyZeroDim_of_stratifiable_sigma_closedDiscrete` / `stronglyZeroDim_of_countable_normal_t1` / `stronglyZeroDim_of_countable_stratifiable`**: 任意の $\sigma$-閉離散層化可能空間および任意の可算層化可能空間が強 0 次元であることを導出。
- **`clopen_basis_of_stronglyZeroDim`**: 強 0 次元 $T_1$ 空間は閉開集合からなる開基を持つことを証明。

## 29. [Heath1966_Nagata_Spaces.lean](Heath1966_Nagata_Spaces.lean)（Heath 1966：Nagata 空間 $\iff$ 第 1 可算かつ層化可能空間）
- **`IsNagataSpace` / `isNagataSpace_iff_firstCountable_and_isStratifiable`**（Heath 1966 Theorem 1）: 対称 $g$-関数による Nagata 空間の定義と、「第 1 可算かつ層化可能」との完全同値を証明。
- **`isNagataSpace_of_metricSpace` / `hasCPOuterBase_of_isNagataSpace`**: 距離空間は Nagata 空間であり、Nagata 空間の各点は必ず単層 CP 開外基を持つ（したがって Nagata 空間は `L_0020` / `L_0030` / `L_0031` の反例にならない）。
- **`isNagataSpace_subtype` / `isNagataSpace_prod`**: 任意の部分空間および有限積での永続性。

## 30. [MoritaHanaiStone_PerfectMetric_IsM1.lean](MoritaHanaiStone_PerfectMetric_IsM1.lean)（Morita–Hanai–Stone 1956：距離空間の完全像・コンパクト境界閉像・第 1 可算閉像はすべて $M_1$）
- **`closurePreserving_compl_sUnion_of_locallyFinite` / `isM1_of_sigma_locallyFinite_star_closed_cover`**: 任意の局所有限閉族 $\mathcal{H}$ の補集合族 $\{(\bigcup \mathcal{S})^c \mid \mathcal{S} \subseteq \mathcal{H}\}$ が局所有限トレースにより自動的に closure-preserving になることを証明し、$\sigma$-局所有限星型閉被覆から直接 $M_1$ 性を導出。
- **`isM1_of_perfectMap_from_metricSpace`**: 距離空間の完全連続像（コンパクトファイバーを持つ閉連続全射の像）は常に $M_1$ 空間。
- **`isM1_of_closedMap_compact_frontier_from_metricSpace` / `isCompact_frontier_of_closedMap_firstCountable` / `isM1_of_closedMap_firstCountable_from_metricSpace`**（Morita–Hanai–Stone 1956 完全版）: 距離空間からの閉連続全射において、各ファイバー境界 $\partial f^{-1}(\{y\})$ がコンパクト（特に像空間 $Y$ が第 1 可算）ならば、閉距離部分空間への制限により完全写像へ帰着され、$Y$ が常に $M_1$ 空間になることを完全証明。

## 31. [Lasnev_Decomposition.lean](Lasnev_Decomposition.lean)（Lašnev 分解定理 1965・距離空間の閉像の Fréchet–Urysohn 性）
- **`frechetUrysohn_of_closedMap_from_metricSpace`**: 任意の距離空間の閉連続像は常に Fréchet–Urysohn 空間であることを証明。
- **`hasDecreasingOpenBase_of_compact_frontier`**: 距離空間の閉連続像において、ファイバー境界 $\partial f^{-1}(\{y\})$ がコンパクトな点 $y$ は減少可算開局所基を持つことを証明。
- **`lasnev_decomposition_completeMetric`**（Lašnev 1965）: 完備距離空間の任意の閉連続像 $Y$ が $Y = Y_0 \cup \bigcup_n D_n$ と分解され、各 $D_n$ は閉離散集合であり、かつ $Y_0$ のすべての点 $y$ がコンパクトファイバー境界・第 1 可算性・単層 CP 開外基 `Defs.D_0001.HasCPOuterBase y` を満たすことを完全証明。

## 32. [Whitney_Metric_ClosedOuterBase.lean](Whitney_Metric_ClosedOuterBase.lean)（Whitney 分解定理：距離空間の任意の閉集合は CP 開外基を持つ）
- **`metric_closed_hasCPOuterBase`**: 任意の距離空間 $X$ とその**任意の閉部分集合** $F \subseteq X$ に対し、補集合 $X \setminus F$ 上の Whitney 型局所有限開細分（$B(a, r_a)$ with $B(a, 3 r_a) \subseteq F^c$）を用いて、$F$ の単層 closure-preserving 開外基を直接構成。

## 33. [CollapseQuotient_Metric_IsM1.lean](CollapseQuotient_Metric_IsM1.lean)（距離空間の任意の閉縮約商 $X / F$ は $M_1$ 空間）
- **`collapseQuot_t3Space`**: 任意の正規 $T_1$ 空間 $X$ と非空閉集合 $F \subseteq X$ に対し縮約商 $X/F$ は $T_3$。
- **`collapseQuot_metric_isM1`**: 任意の距離空間 $X$ と任意の非空閉集合 $F \subseteq X$ に対し、Whitney 分解による単層 CP 開外基と距離殻 $H_k$ 上の局所有限開細分を結合することで、縮約商 $X/F$ が頂点 `none` に CP 開外基を持ち、かつ空間全体が常に **`M₁` 空間**であることを無条件に証明（$\mathbb{R}/\mathbb{Z}$、$\mathbb{R}^d/\mathbb{Z}^d$、$\ell^2/F$ 等の非第 1 可算・非局所コンパクト・非 $k_\omega$ 商空間をすべて包含）。

## 34. [HCP_FrechetUrysohn_And_Lasnev_OuterBase.lean](HCP_FrechetUrysohn_And_Lasnev_OuterBase.lean)（HCP 補集合 CP 定理と任意の Lašnev 空間の全点 CP 開外基定理）
- **`IsHCP` / `isHCP_image_of_locallyFinite_isClosedMap`**: 閉連続写像による局所有限族の像が遺伝的閉包保存（HCP）であることを証明。
- **`closurePreserving_compl_sUnion_of_isHCP_frechetUrysohn`**（HCP 補集合 CP 定理）: 任意の $T_1$ Fréchet–Urysohn 空間において、任意の HCP 族 $\mathcal{H}$ の補集合族 $\{(\bigcup_{i \in S} H_i)^c \mid S\}$ が自動的に closure-preserving になることを証明。
- **`lasnev_every_point_hasCPOuterBase`**: 任意の距離空間（完備性不要）の任意の閉連続像（Lašnev 空間）の**すべての点** $y_0$ が単層 CP 開外基 `Defs.D_0001.HasCPOuterBase y₀` を持つことを Whitney 分解＋HCP 補集合 CP 定理により完全証明（したがって Lašnev 空間は `L_0020` / `L_0030` / `L_0031` の反例になり得ない）。

## 35. [Slaughter1973_CompleteMetric_Lasnev_IsM1.lean](Slaughter1973_CompleteMetric_Lasnev_IsM1.lean)（Slaughter 1973：完備距離空間の任意の閉連続像は $M_1$ 空間）
- **`closedMetric_discrete_open_expansion`**: 距離空間の任意の閉連続像における閉離散部分集合の離散開拡大（単調正規性作用素経由）。
- **`slaughter_completeMetric_closedMap_isM1`**: Lašnev 分解（閉離散層 $D_m$ とコンパクトファイバー層 $Y_0$）、HCP 補集合 CP 定理、および離散開拡大＋各点 CP 開外基を統合し、任意の完備距離空間の任意の閉連続像 $Y$ が常に **`MSpace.IsM1 Y`** であることを完全証明。

## 36. [Gruenhage1978_SigmaDiscrete_Stratifiable_IsM1.lean](Gruenhage1978_SigmaDiscrete_Stratifiable_IsM1.lean)（Gruenhage 1978：すべての $\sigma$-離散層化可能空間および可算層化可能空間は $M_1$ 空間）
- **`hasCPOuterBase_of_stratifiable_sigma_closedDiscrete`**: 任意の $\sigma$-閉離散層化可能空間において、$\operatorname{Ind} X = 0$・離散閉開拡大・減少 stratification を組み合わせて、**すべての点** $x_0$ に単層 closure-preserving 閉開外基 `Defs.D_0001.HasCPOuterBase x₀` を構成。
- **`isM1_of_stratifiable_sigma_closedDiscrete` / `isM1_of_stratifiable_sigma_discrete`**（Gruenhage 1978）: 任意の $\sigma$-離散層化可能空間（閉性を仮定しない離散部分空間の可算和 $X = \bigcup_n D_n$）が $F_\sigma$-還元を経て常に **`MSpace.IsM1 X`** であることを完全証明。
- **`isM1_of_countable_stratifiable`**: 任意の**可算**層化可能空間は常に **`M₁` 空間**である（したがって `Tinf` / `L_0020` / `L_0030` / `L_0031` の反例は必ず非可算かつ非 $\sigma$-離散でなければならない）。

## 37. [Borges1966_CompactMetrizable_And_Cosmic.lean](Borges1966_CompactMetrizable_And_Cosmic.lean)（Borges 1966 / Šneider 1945 / Michael 1966：コンパクト層化可能空間の距離化可能性と可分層化可能空間の cosmic 性）
- **`countable_closed_network_of_compact_stratifiable`**: コンパクト層化可能空間では任意の離散閉族が有限となり、可算閉ネットワークを持つこと。
- **`secondCountable_of_compact_stratifiable` / `metrizableSpace_of_compact_stratifiable` / `metrizableSpace_compact_subtype_of_isStratifiable`**（Borges 1966 / Šneider 1945）: 任意のコンパクト層化可能空間（および任意の層化可能空間の任意のコンパクト部分集合）が常に**第 2 可算**かつ**距離化可能**（`MetrizableSpace`）であることを完全証明。
- **`countable_closed_network_of_separable_stratifiable` / `hereditarily_separable_of_separable_stratifiable` / `hereditarily_lindelof_of_separable_stratifiable`**（Borges 1966 / Michael 1966）: 任意の可分層化可能空間が可算閉ネットワークを持つ（cosmic 空間である）こと、およびその任意の部分空間が可分かつ Lindelöf（遺伝的可分・遺伝的 Lindelöf）であることを完全証明。

## 38. [Gruenhage_ClosedOuterBase_SigmaDiscreteCompl.lean](Gruenhage_ClosedOuterBase_SigmaDiscreteCompl.lean)（一般化 Gruenhage 外基定理：補集合が $\sigma$-離散な閉集合の CP 閉開外基と第 2 可算／コンパクト核 $M_1$ 定理）
- **`hasCPClopenOuterBase_of_sigma_closedDiscrete_compl` / `hasCPClopenOuterBase_of_sigma_discrete_compl`**: 任意の層化可能空間 $X$ において、補集合 $X \setminus A$ が $\sigma$-離散（特に可算）な**任意の閉集合** $A \subseteq X$ が単層 closure-preserving **閉開**外基を持つことを証明（$A$ や $X$ 自体の 0 次元性・$\sigma$-離散性不要）。
- **`closurePreserving_inter_open_of_clopen`**: 閉開 CP 族と任意の部分集合 $D$ との交わりが常に CP 性を保存すること。
- **`hasCPOuterBase_of_sigma_discrete_punctured_nhd`**: 層化可能空間で $U \setminus \{x_0\}$ が $\sigma$-離散な開近傍 $U$ を持つ任意の点 $x_0$ が `Defs.D_0001.HasCPOuterBase x₀` を満たすこと。
- **`isM1_of_stratifiable_secondCountable_closed_sigma_discrete_compl`**: 補集合 $X \setminus A$ が $\sigma$-離散な第 2 可算閉部分空間 $A$（特に任意のコンパクト核や有限核）を持つ層化可能空間が常に **`MSpace.IsM1 X`** であることを完全証明。

## 39. [ChenWang_Ptop_And_Sec5_LnCover.lean](ChenWang_Ptop_And_Sec5_LnCover.lean)（`Defs.D_0029`〜`D_0032` 直結：`ptop` 距離化・層化可能性、細分位相 `L_0031`/`¬ Tinf` 橋渡し、第 5 節穿孔 `lnc` 被覆）
- **`rho_secondCountable` / `rho_t3Space` / `ptop_secondCountable` / `ptop_t3Space` / `ptop_metrizable` / `ptop_isStratifiable` / `ptop_node_isStratifiable`**: 任意の可算 `NoMaxOrder` 線形順序 $\alpha$（特に `Defs.D_0028.Node`）に対し、修正版積位相 `Defs.D_0029.ptop α` およびその任意の部分空間 $Y \subseteq \mathbb{N} \to \alpha$ が第 2 可算・$T_3$・距離化可能・層化可能であることを証明。
- **`ptop_subtype_refinement_isStratifiable` / `ptop_subtype_refinement_L0031_and_not_Tinf`**: 任意の部分空間 $Y \subseteq \mathbb{N} \to \alpha$ 上の細分位相 $\tau \le \mathrm{ptop}_Y$（Chen–Wang §6–§7 の直接設定）において、`ptop`-境界分離 $g$-関数と `¬ HasCPOuterBase y₀` から `gfun q T (n+1) y₀` を介して `Specs.L_0031.stmt` および `¬ MSpace.Goals.Tinf_M3_imp_M1` を直接導出。
- **`lnc_diff_cover_point` / `lnc_diff_iUnion_eq` / `lnc_diff_clopen_disjoint` / `prop_4_8_star_clopen`**: `Defs.D_0031.lnc`・`Defs.D_0032.prop_4_8` 上で、穿孔セル $g(m, y_0) \setminus H(n, x)$ が $\bigcup_{\ell \ge m} \bigcup \mathrm{lnc}(\ell, g(m, y_0) \setminus H(n, x))$ の厳密和となること（§5 の基盤）、および系 4.9 の星近傍が `ptop`-閉開であり全中心 $H(\ell, z) \subseteq H(n, x)$ を満たすことを完全証明。
