# L0028 調査メモ：閉近傍基の正則化

**状態：部分的な帰着。L0028 は未解決のまま。** 既存の仮定から導ける範囲を記録し、closure-preserving の結論を証明したとは主張しない。

## 目標

リポジトリの [L0028 仕様](https://github.com/ruca-maths/nickel/blob/main/Specs/L_0028.lean) は、M1 空間 `X`、各層が閉離散な稠密集合 `D = ⋃ₙ Dₙ`、点 `x` における closure-preserving な閉近傍基 `𝓚` を仮定し、`x` における closure-preserving な正則閉近傍基を求める。

各 `K ∈ 𝓚` に対して

\[
  r(K) = \overline{\operatorname{int} K}, \qquad
  \mathcal K_r = \{r(K):K\in\mathcal K\}.
\]

この構成の初等的な部分は次の通り成立する。

1. `r(K)` は定義から閉であり、`cl(int(cl(int K))) = cl(int K)` より正則閉である。
2. 開集合 `int K` が `r(K)` に含まれるので、`x ∈ int K` なら `x ∈ int(r(K))` である。
3. `𝓚ᵣ` は近傍基のままである。開近傍 `U ∋ x` に対して、正則性から `x ∈ V` かつ `cl(V) ⊆ U` となる開集合 `V` をとる。近傍基性より `K ∈ 𝓚` で `K ⊆ V` を満たすものがあり、`r(K) ⊆ cl(V) ⊆ U` となる。

したがって L0028 の残りは、この正則化そのもの、またはそこから作る細分族が closure-preserving であることの証明である。

## 素朴な証明が止まる箇所

部分族 `𝓖 ⊆ 𝓚` について、入力の closure-preserving 性から

\[
  \overline{\bigcup_{K\in\mathcal G}K}=\bigcup_{K\in\mathcal G}K.
\]

`r(K) ⊆ K` なので、これは `cl(⋃_{K∈𝓖} r(K)) ⊆ ⋃_{K∈𝓖} K` までは与える。しかし閉包を `⋃_{K∈𝓖} r(K)` の中に入れるものではない。従って、単調性と入力族の CP 等式だけでは、必要な等式

\[
  \overline{\bigcup\mathcal H}=\bigcup\mathcal H
  \quad\text{for every }\mathcal H\subseteq\mathcal K_r.
\]

この段階では、稠密な σ-閉離散集合 `D` の追加構造を明示的に使う細分・選択の議論が有望である。目標は、基性を保ちつつ、選んだ正則化族の任意の和集合の極限点を、その族のいずれかの元に割り当てること。すでに検証済みの [L0027 の証明](https://github.com/ruca-maths/nickel/blob/main/Proofs/L_0027.lean) によれば、CP 正則閉近傍基が得られれば、その内部を取って CP 開外基を作れる。

## 形式化の次のチェックポイント

次の有用な Lean 小目標は、正則空間と近傍基の仮定から `r(K) = closure (interior K)` の上記3性質を形式化し、CP 性は別の未証明条件として分離すること。決定的な後続証明では `Dₙ` を使って細分族の CP 性を示す必要がある。各出力が正則閉であることや、族が依然として基であることだけでは L0028 は解決しない。

## 文献との関係

リポジトリの状況説明は、この段階を Mizokami の2004年論文 [“On closed subsets of M1-spaces”](https://doi.org/10.1016/j.topol.2003.12.007) の中核としている。公開抄録は、M1 空間の任意の閉部分集合が closure-preserving な開近傍基を持つという、より広い結果を述べる。一方、閲覧可能な抄録から証明の詳細は確認できないため、このメモは上記の帰着までを成果とし、Mizokami の証明を再現したとは扱わない。
