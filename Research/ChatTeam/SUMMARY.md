# Chat Team Research Sync (2026-11-27)

通常チャット AI 3 体（かえる＝担当 A、青＝担当 B、金魚＝担当 C）による並行研究のうち、ローカル Lean 4.36.0 でエラー 0・警告 0 にてコンパイル検証を通過したコードと、裏取り済みの主要知見を同期する。

## 1. 検証済み Lean 4 モジュール（エラー 0・警告 0・`sorry` 0）

### `Research/ChatTeam/L0028_Helpers.lean`（かえる + 青）
- `regularClosed_closure_of_isOpen`: 開集合の閉包は正則閉。
- `exists_regularClosed_cp_nhds_of_isOpen_singleton`: 孤立点での `L_0028` 成立。
- `sigma_closed_discrete_dense_diff_singleton`: 非孤立点 `x` を除いた `D n \ {x}` の閉離散性・稠密性保存。
- `discrete_open_expansion`（かえる）: パラコンパクト $T_3$ 空間における閉離散集合 $D$ の離散開膨張（collectionwise normality）。
- `regularClosed_cp_nhds_of_open_cp_base`（青, `L_0028a`）: CP 開近傍基から正則閉 CP 閉近傍基への帰着。
- `closurePreserving_sUnion_closure`（青, `L_0028c`）: CP 族の任意和閉包の CP 性。
- `closurePreserving_iUnion_of_shrinking`（青, `L_0028b`）: 減少開近傍列 $W_n$ による層別 CP 統合補題。
- `isRegularOpen_iUnion_of_locallyFinite_disjoint_frontier`（かえる）: 境界が対ごとに素な局所有限正則開族の任意部分和は正則開。
- `regularOpenDiscreteExpansionSeq_of_step`（かえる）: Mizokami (1985) Lemma 5（`RegularOpenRefinementStep_stmt`）から Lemma 6（`RegularOpenDiscreteExpansionSeq_stmt`）への完全帰納法。
- `shrinkingStrat`, `mizokami_lemma_1_5`, `mizokami_lemma_1_5_singleton`（青）: Mizokami (2003, arXiv:math/0312457) Lemma 1.5（一般閉集合 $M$ および 1 点 $\{x\}$ 上で閉包が漏れない $X \setminus M$ の開膨張 $S(B)$）。
- `atomClosed`, `openAvoidingCP` 関連補題群（青）: Mizokami (2003) Lemma 1.2 の原子閉細分 $E(N)$ および CP 避け開膨張のコア補題群。
- `IsDiscreteFamily`, `exists_closed_exhaustion_interior`, `mizokami_lemma_1_2`（青）: Mizokami (2003, arXiv:math/0312457) Lemma 1.2 全文（2 段ずらし点有限化による $\sigma$-離散閉被覆と点有限・$\sigma$-離散開膨張）。
- `exists_locallyFinite_refinement_with_closed_shrinking`, `regularOpenRefinementStep_of_singleInsert_aux`（カエル）: パラコンパクト $T_3$ 空間での Shrinking Lemma、極限ステップ還元、および `WellOrderingRel` 上の超限帰納法による「1 個追加補題 ⇒ `RegularOpenRefinementStep_stmt`」。
- `isRegularOpen_iUnion_iff_frontier_escape`, `singleInsert_iff_frontier_escape_cond`（カエル）: 任意部分和が正則開であることの完全な局所特徴づけと 1 個追加の逃げ道条件。
- `singleRegularOpenInsert_singleton_normal`, `singleRegularOpenInsert_secondCountable`（カエル）: 正規空間での $|A|=1$ 版および第二可算空間での `SingleRegularOpenInsert` の完全形式化（Urysohn 局所最大値の高々可算除外）。

### `Research/ChatTeam/L0031_ClopenShell_Hereditary.lean`（金魚）
- `decClopen`, `shell`, `decClopen_antitone`, `decClopen_isClopen`, `shell_isClopen`, `clopen_inter_closure`, `exists_shell_of_ne`: clopen-$G_\delta$ 頂点の標準 clopen 殻分解。
- `closurePreserving_iff_forall_shell`（定理 1A）: 頂点近傍族の CP 性と各殻 $S_n$ への制限の CP 性の完全同値性。
- `closurePreserving_of_finiteMaximalSubunion`: 有限極大元和性質（逆 WQO）⇒ CP。
- `hasCPOuterBase_of_discrete_shells`（定理 2A(1)）: 各殻が離散ならば `HasCPOuterBase y`。
- `hasCPOuterBase_of_reverseWQO_shells`（定理 2A(2)）: 各殻に逆 WQO 族があり近傍フィルタを共終生成すれば `HasCPOuterBase y`。
- `isStratifiable_iff_shells`（定理 1B）: clopen-$G_\delta$ 頂点空間の stratifiability を各殻の $T_1$ 性＋殻分離型 Heath $g$-関数系（`IsShellHeathSystem`）の存在と完全同値化（`L_0014`・`L_0017` 接続）。
- `hasCPOuterBase_of_inducing_clopen_CP`（定理 2B(1)）: 終域に clopen CP 局所基があるとき、任意の位相的埋め込み（部分空間を含む）の始域も `HasCPOuterBase` を持つ。

## 2. 確定した文献裏取り・No-Go 知見

1. **$C_k(\mathbb{N}^\mathbb{N}, \mathbb{R})$ の反例候補からの正式除外（かえる＋一次裏取り）**:
   - K. Tamano (2008), *A base, a quasi-base, and a monotone normality operator for $C_k(P)$*, Topology Proc. 32, 277–290 および Gruenhage サーベイ Theorem 7.3 により、任意の Polish 空間 $X$ に対して $C_k(X, \mathbb{R})$ は $M_1$ 空間である。
   - したがって `CkBaireReal` は `L_0030` の反例にならない（未解決のまま残るのは hereditarily $M_1$ 性および $\mu$-space 性）。
2. **$C_k(X, 2)$（任意の Polish 空間 $X$ およびその任意の部分空間）の反例候補からの除外（金魚）**:
   - 任意の非空 Polish 空間 $X$ は $\mathbb{N}^\mathbb{N}$ からの連続 compact-covering 全射 $\pi : \mathbb{N}^\mathbb{N} \to X$ を持ち、引き戻し $\pi^* : C_k(X, 2) \to C_k(\mathbb{N}^\mathbb{N}, 2)$ が位相的埋め込みになるため、`hasCPOuterBase_of_inducing_clopen_CP` と既検証の $C_k(\mathbb{N}^\mathbb{N}, 2)$ 結果から全点が clopen CP 開外基を持つ。
3. **`L_0028` の新規 No-Go 4（青）**:
   - $\mathscr{C}_n := \{B \in \mathscr{B}_n \mid B \subseteq W_n\}$ は定理 B・C により厳密に CP になるが、$\mathbb{R}$ 上で $\mathscr{B}_n$ の添字付けを遅らせるだけで $\mathscr{C}_n = \{\emptyset\}$ となり近傍基性が崩壊する。
4. **Mizokami (1985) Lemma 5–6 / Gruenhage (1980) Lemma 4.4 の構造解析（カエル＋一次裏取り）**:
   - 原出典は Gruenhage (1980), *On the $M_3 \Rightarrow M_1$ question*, Topology Proc. 5, Lemma 4.4。
   - 一般のパラコンパクト $T_3$ 空間で Shrinking Lemma と超限帰納法還元が Lean 4 で完全形式化済み（`SingleRegularOpenInsert` のみに縮減）。
   - 任意部分和が正則開であることの完全な局所特徴づけ（$\forall p,\; p \notin \operatorname{int}(\bigcup_{C \in \mathscr{F}_p} \overline{C})$）を発見・証明。
   - 第二可算空間（$\mathbb{R}^2$ 単位円盤テスト含む）では Urysohn 閾値法で完全証明、非可分ハリネズミ空間 $J(\omega_1)$ でも成立確認、$|\mathscr{A}|=1$ は正規空間一般で成立。残る核心は非可分空間での一般証明（あるいは $\sigma$-離散網による代替構成）。
