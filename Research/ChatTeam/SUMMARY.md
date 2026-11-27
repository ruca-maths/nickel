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

### `Research/ChatTeam/L0031_ClopenShell_Hereditary.lean`（金魚）
- `decClopen`, `shell`, `decClopen_antitone`, `decClopen_isClopen`, `shell_isClopen`, `clopen_inter_closure`, `exists_shell_of_ne`: clopen-$G_\delta$ 頂点の標準 clopen 殻分解。
- `closurePreserving_iff_forall_shell`（定理 1A）: 頂点近傍族の CP 性と各殻 $S_n$ への制限の CP 性の完全同値性。
- `closurePreserving_of_finiteMaximalSubunion`: 有限極大元和性質（逆 WQO）⇒ CP。
- `hasCPOuterBase_of_discrete_shells`（定理 2A(1)）: 各殻が離散ならば `HasCPOuterBase y`。
- `hasCPOuterBase_of_inducing_clopen_CP`（定理 2B(1)）: 終域に clopen CP 局所基があるとき、任意の位相的埋め込み（部分空間を含む）の始域も `HasCPOuterBase` を持つ。

## 2. 確定した文献裏取り・No-Go 知見

1. **$C_k(\mathbb{N}^\mathbb{N}, \mathbb{R})$ の反例候補からの正式除外（かえる＋一次裏取り）**:
   - K. Tamano (2008), *A base, a quasi-base, and a monotone normality operator for $C_k(P)$*, Topology Proc. 32, 277–290 および Gruenhage サーベイ Theorem 7.3 により、任意の Polish 空間 $X$ に対して $C_k(X, \mathbb{R})$ は $M_1$ 空間である。
   - したがって `CkBaireReal` は `L_0030` の反例にならない（未解決のまま残るのは hereditarily $M_1$ 性および $\mu$-space 性）。
2. **$C_k(X, 2)$（任意の Polish 空間 $X$ およびその任意の部分空間）の反例候補からの除外（金魚）**:
   - 任意の非空 Polish 空間 $X$ は $\mathbb{N}^\mathbb{N}$ からの連続 compact-covering 全射 $\pi : \mathbb{N}^\mathbb{N} \to X$ を持ち、引き戻し $\pi^* : C_k(X, 2) \to C_k(\mathbb{N}^\mathbb{N}, 2)$ が位相的埋め込みになるため、`hasCPOuterBase_of_inducing_clopen_CP` と既検証の $C_k(\mathbb{N}^\mathbb{N}, 2)$ 結果から全点が clopen CP 開外基を持つ。
3. **`L_0028` の新規 No-Go 4（青）**:
   - $\mathscr{C}_n := \{B \in \mathscr{B}_n \mid B \subseteq W_n\}$ は定理 B・C により厳密に CP になるが、$\mathbb{R}$ 上で $\mathscr{B}_n$ の添字付けを遅らせるだけで $\mathscr{C}_n = \{\emptyset\}$ となり近傍基性が崩壊する。
4. **Mizokami (1985) Lemma 5–6 / Gruenhage (1980) Lemma 4.4 の構造解析（かえる＋一次裏取り）**:
   - 原出典は Gruenhage (1980), *On the $M_3 \Rightarrow M_1$ question*, Topology Proc. 5, Lemma 4.4。
   - 一般のパラコンパクト $T_3$ 空間で超限帰納法の極限ステップは無条件に閉じ、「1 個追加補題」へ完全還元されることを証明。さらに第二可算空間（$\mathbb{R}^2$ 単位円盤テスト含む）では Urysohn 関数の非可算個の閾値から可算個の禁止値を除くことで完全証明。非可分空間での単一閾値の反例（$\bigoplus_{t \in (0,1)} [0,1]_t$）も特定済み。
