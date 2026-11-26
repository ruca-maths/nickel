#!/usr/bin/env bash
# エージェントが叩く統一ラッパー CLI。管理コマンド（approve-targets / init 等）は公開しない。
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PY="${RESEARCH_PYTHON:-python3}"
cmd="${1:-help}"
shift || true
case "$cmd" in
  task|next|beat|check|define|propose|submit|release|audit|context|lemmas|status)
    exec "$PY" "$ROOT/core/desk.py" "$cmd" "$@" ;;
  help|-h|--help)
    cat <<'USAGE'
usage: bash tools/research.sh <command> [args]
  task                         現在のタスク情報を表示
  context <L_xxxx>             ノードの情報（命題・関連補題・過去の失敗）
  lemmas [--query 語]          Checked 補題の一覧／検索
  check <file>                 静的フィルタ＋コンパイル（受理はしない）
  define <defs.lean>           (Architect) 定義モジュールを登録（namespace Defs.NEW）
  propose <children.json>      (Architect) 子補題を登録（negate: true で反証側の分解）
  submit <file> [--note 要約]  最終提出（リース終了）
  release --reason 理由 [--note 知見]   断念（リース終了）
  audit <report.md>            (Red Team) 監査報告を提出
  next --agent ID --role ROLE  手動運用時のタスク取得
  beat                         手動運用時のリース延長
  status                       全体状況
USAGE
    ;;
  *) echo "unknown command: $cmd（help を参照）" >&2; exit 2 ;;
esac
