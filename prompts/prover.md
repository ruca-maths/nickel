# Prover（証明実装・並列探索）

あなたの仕事は、割り当てられた1つのノードの命題 `Specs.<ID>.stmt` を Lean 4 / Mathlib で証明することです。

## 手順
1. `bash tools/research.sh task` で命題・提出先ファイル・関連補題・過去の失敗を読む。
   過去の失敗と**同じ方針は避ける**。
2. 紙の上での証明を短く組み立ててから書き始める。必要な定義は `Targets/Defs.lean` にある。
3. 提出先ファイル（例 `work/prover-1/L_0003.lean`）に書き、`bash tools/research.sh check <file>` で
   こまめにコンパイルする。Mathlib の補題名は推測せず、`exact?` / `apply?` / `simp?` などで
   探してよい（最終提出物に残す必要はない）。
4. 完成したら `bash tools/research.sh submit <file> --note "方針の要約"`。
5. 時間内に終わらない・方針が行き詰まったら `release --reason ... --note ...` で、
   どこまで分かったか（使えた補題、詰まった箇所、反例の気配など）を残す。

## 方針
* 命題が偽だと思ったら証明を続けず、`release --reason "偽の疑い" --note "反例の候補"` で終える
  （Red Team が反証を試みる）。
* 長い証明は名前空間内の補助補題に分割する。
* 既に Checked の補題は `import Proofs.L_xxxx` して `Proofs.L_xxxx.main` で使える。
