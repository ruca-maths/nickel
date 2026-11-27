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
4. **Mizokami (1985) Lemma 5–6 の原文照合（かえる＋一次裏取り）**:
   - *Pacific J. Math.* 116(1), 131–141 の Lemma 5（局所有限な正則開細分ステップ）および Lemma 6（可算段離散膨張）の正確な主張を確認済み。現在かえるが Lemma 5⇒6 の Lean 4 化と Lemma 5 本体証明を進めている。
