"""オーケストレータ試験用の偽エージェント。標準入力のプロンプトからタスク JSON を
取り出し、既知のタスクなら正しい証明を書いて desk に提出する。最後に claude -p 互換の
JSON（total_cost_usd 付き）を出力する。"""
import json
import os
import re
import subprocess
import sys
from pathlib import Path

DESK = Path(__file__).resolve().parent.parent / "core" / "desk.py"
KNOWN = {"Toy.Goals.G1": "Toy.Goals.G1", "Toy.Goals.G2": "Toy.Goals.G2"}

prompt = sys.stdin.buffer.read().decode("utf-8")
if os.environ.get("FAKE_LIMIT"):  # 利用上限エラーを模擬（claude -p の出力形式）
    print(json.dumps({"type": "result", "is_error": True, "api_error_status": 429, "total_cost_usd": 0,
                      "result": "You've hit your 5-hour limit · resets 6:30am (Asia/Tokyo)"}))
    sys.exit(1)
task = json.loads(re.findall(r"```json\n(.*?)\n```", prompt, re.S)[-1])
root = Path(os.environ["RESEARCH_CONFIG"]).resolve().parent
if root.name == "state":  # 子機設定は state/remote_config.json
    root = root.parent

stmt = task.get("context", {}).get("stmt")
if task.get("task") == "prove" and stmt in KNOWN:
    nid = task["context"]["node"]
    f = root / task["file"]
    f.parent.mkdir(parents=True, exist_ok=True)
    f.write_text(f"import Specs.{nid}\nnamespace Proofs.{nid}\n"
                 f"theorem main : Specs.{nid}.stmt := by\n  unfold Specs.{nid}.stmt {KNOWN[stmt]}\n"
                 f"  intro n\n  rfl\nend Proofs.{nid}\n", encoding="utf-8")
    subprocess.run([sys.executable, str(DESK), "submit", str(f), "--note", "fake"], check=False,
                   stdout=subprocess.DEVNULL)
print(json.dumps({"type": "result", "result": "done", "total_cost_usd": 0.05}))
