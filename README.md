# 自律マルチ AI 数学研究システム（M₃ ⇒ M₁ 問題）

Architect ×1・Prover ×2・Red Team ×1 の4エージェントが、Lean 4 / Mathlib で
「任意の M₃ 空間は M₁ 空間か」（Ceder 1961）の周辺定理を形式化し、本題に挑む。
**成果として数えるのは Lean カーネルと公理検査を通ったものだけ**。

## 仕組み
| 部品 | 役割 |
|---|---|
| `Targets/` | ロック領域。定義（T0）・目標命題（T1〜Tinf）・`goals.json`。人間が承認したハッシュから変わると検証が止まる |
| `Specs/` | 補題の命題（`Specs.L_xxxx.stmt`）。desk が DB から機械生成 |
| `Proofs/` | 受理された証明 `L_`・帰着 `R_`・反証 `N_`。desk が検証後にだけ書き込む |
| `core/db.py` | SQLite (WAL)。AND-OR グラフ・リース・試行回数・予算・ビルド枠 |
| `core/static_filter.py` | ビルド前の静的拒否（sorry / axiom / native_decide / メタプログラミング / 名前空間脱出 / 未承認 import 等） |
| `core/verifier.py` | `lake build` → 独立検査ファイルで「期待される型」との一致 → `#print axioms` を許可公理と照合 |
| `core/desk.py` | リース制タスク配分（next / task / beat / check / propose / submit / release / audit） |
| `core/retriever.py` | Checked 補題の検索と失敗記憶。`retriever.backend: command` で LeanDojo 等を差し込める |
| `core/orchestrator.py` | 4並列実行・心拍・コスト記録・日次/段階別予算・サーキットブレーカー・STOP |
| `core/status_gen.py` | `STATUS.md`・`status/graph.json` の自動生成 |
| `core/ci_verify.py` + `.github/workflows/verify.yml` | GitHub 連携時の検証・保護パス検査・Track A 自動マージ・stale 掃除 |

帰着 `R` は「子補題すべて ⇒ 親」という Lean 定理。子が全部 Checked になると、親の証明は
desk が機械的に合成して再検証する（AI が「親も証明できた」と主張する余地はない）。
本題 Tinf が証明または反証されると `STOP` ファイルが作られ、人間が精査するまで全体が止まる。

## セットアップ（初回）
1. Python 3.11 以上をインストールする（標準ライブラリだけで動く。PyYAML は任意）。
2. Mathlib を取得してビルドする（数 GB をダウンロード）:
   ```
   lake update
   lake exe cache get
   lake build Targets
   ```
   `lakefile.toml` の `rev` と `lean-toolchain` は同じバージョンに揃えること。
3. **`Targets/Defs.lean` を原典と照合する**（冒頭の「要原典確認の点」）。納得したら承認:
   ```
   python core/desk.py approve-targets --by <あなたの名前>
   python core/desk.py init
   ```
4. Claude Code CLI（`claude`）にログインした状態で実行:
   ```
   python core/orchestrator.py --print-prompt prover-1   # プロンプト確認（試行回数は消費しない）
   python core/orchestrator.py                            # 本番（Ctrl+C か STOP ファイルで停止）
   ```

## 別の PC で AI を動かす（GitHub 連携）
**親機**（DB を持つ PC、1台）と**子機**（AI だけを動かす PC、何台でも）を GitHub でつなぐ。
子機が扱うのは証明（prove）と反証（refute）だけ。分解と監査は親機が担当する。

```
子機: claim/<task>-<node> ブランチで確保 → AI が証明 → 手元で親機と同じ検証
      → proof/<module>-<agent> ブランチ（main + 証明ファイル1つ）を push → PR
CI  : 保護パス検査 → Lean 検証 → 合格なら自動マージ
親機: desk sync で main を取り込み → 再検証して DB に登録 → STATUS.md / graph.json を push
```

### 親機の設定
`config.yaml` の `git` を `mode: github`、`autocommit: true` にし、`base_branch` を合わせる。
```
python core/desk.py sync                 # 手動で1回同期
python core/orchestrator.py              # mode: github なら sync_interval_sec ごとに自動で sync
```

### 子機の準備と起動
1. リポジトリを clone し、`lake exe cache get` で Mathlib を入れる
2. `gh auth login`（push と PR 作成のため）と、AI の CLI のログイン
3. 子機で動かすエージェントを `config.yaml` の `agents` に追加して親機から push する
   （ID は PC ごとに変える。例 `prover-pc2`）
4. 起動:
   ```
   python core/remote.py --agents prover-pc2 --max-sessions 1   # 試運転
   python core/remote.py --agents prover-pc2 --loop             # 常駐
   ```
* 子機用エージェントには `remote: true` を付ける（親機のオーケストレータは起動しない）。
  Claude 以外の AI は `runners:` に起動コマンドを書き、エージェントの `runner:` で選ぶ
  （例: `runner: gemini`。コストを報告しない CLI は `cost_estimate_usd` で予算を数える）。
* 子機の予算は子機の `state/remote.db` で別に数える（`budget.daily_usd` は PC ごとの上限になる）。
* 子機での失敗メモは子機の `memory/failures.jsonl` に残るだけで、親機には届かない。
* 子機の作業ツリーは毎回 `origin/main` に合わせ直すので、子機では追跡ファイルを編集しないこと。

## テスト
Mathlib 不要の玩具フィクスチャ（`tests/fixture_lean`）で、実際の Lean を使って検査する。
```
python -m unittest tests.test_static_filter tests.test_system tests.test_remote
```
別 PC 連携（bare リポジトリで親機1台・子機2台）、正常証明の受理、命題すり替え・sorry・独自 axiom・native_decide の拒否、Targets 改竄検出、
作業領域外ファイルの拒否、競合リースと期限切れ回収、帰着→機械合成、反証と本題停止、
偽エージェントによるオーケストレータ一周、予算停止、受理後改竄検出を含む（28件）。

## 性能の目安（メモリ 7.4GB の環境で実測）
* `import Mathlib`（全体）を含む検査は1回 **約9分半**かかったため、`config.yaml` の
  `forbidden_imports` で禁止している。`Targets/Defs.lean` も必要な位相空間論モジュールだけを import する。
* 部分 import での検査は1回 **約10秒**。9個の目標の Spec 生成と検査（`init`）は約3分。
* `build_slots` は 1 のままにすること（並列にビルドするとメモリが足りなくなる）。

## 既知の限界
* **定義の正しさは Lean では保証されない。** T0 は人間の承認が最終判断。Red Team の監査報告
  （`memory/audits/`）は参考情報。
* エージェントの権限制限は Claude Code の `--allowedTools` に依存する。管理コマンド
  （`approve-targets` など）は `tools/research.sh` からは呼べないが、OS レベルでの隔離はしていない。
  気になる場合は `Targets/` を読み取り専用にするか、エージェントを別ユーザーで動かすこと。
* `$10/日` で4エージェントを Opus で回すと、1日に意味のある試行は数十回程度。
  Prover を `claude-sonnet-5-5` にすれば試行回数は増える（`config.yaml` の `model`）。
* GitHub 連携モードでは `git.autocommit: true` にして `Specs/`・`status/graph.json` を
  コミットしておく必要がある（CI はベースブランチの graph.json を正とする）。
