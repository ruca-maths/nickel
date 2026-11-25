"""設定ファイル読み込み。PyYAML があれば使い、無ければ本システムの config.yaml が
使う範囲（ネストしたマッピング・ブロックリスト・インラインリスト・スカラー）だけを
扱う最小パーサで読む。"""
from __future__ import annotations

import json
import os
import re
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parent.parent


def _scalar(tok: str) -> Any:
    tok = tok.strip()
    if tok == "" or tok in ("null", "~"):
        return None
    if tok in ("true", "True"):
        return True
    if tok in ("false", "False"):
        return False
    if tok[0] in "\"'":
        if tok[0] == '"':
            return json.loads(tok)
        return tok[1:-1].replace("''", "'")
    if tok.startswith("["):
        return _inline_list(tok)
    if re.fullmatch(r"-?\d+", tok):
        return int(tok)
    if re.fullmatch(r"-?\d+\.\d*", tok):
        return float(tok)
    return tok


def _split_top(s: str) -> list[str]:
    out, buf, q, depth = [], "", None, 0
    for ch in s:
        if q:
            buf += ch
            if ch == q:
                q = None
            continue
        if ch in "\"'":
            q = ch
        elif ch == "[":
            depth += 1
        elif ch == "]":
            depth -= 1
        elif ch == "," and depth == 0:
            out.append(buf)
            buf = ""
            continue
        buf += ch
    if buf.strip():
        out.append(buf)
    return out


def _inline_list(tok: str) -> list:
    inner = tok.strip()[1:-1]
    return [_scalar(x) for x in _split_top(inner)]


def _strip_comment(line: str) -> str:
    q = None
    for i, ch in enumerate(line):
        if q:
            if ch == q:
                q = None
        elif ch in "\"'":
            q = ch
        elif ch == "#" and (i == 0 or line[i - 1] in " \t"):
            return line[:i]
    return line


def mini_yaml(text: str) -> Any:
    lines = []
    for raw in text.splitlines():
        s = _strip_comment(raw).rstrip()
        if s.strip():
            lines.append((len(s) - len(s.lstrip(" ")), s.strip()))
    pos = 0

    def parse_block(indent: int) -> Any:
        nonlocal pos
        if pos >= len(lines):
            return None
        if lines[pos][1].startswith("- "):
            res = []
            while pos < len(lines) and lines[pos][0] == indent and lines[pos][1].startswith("- "):
                body = lines[pos][1][2:]
                if re.match(r"^[\w.\-]+:(\s|$)", body):
                    # リスト要素がマッピング: 先頭行を同じ子インデントの行として扱う
                    lines[pos] = (indent + 2, body)
                    res.append(parse_block(indent + 2))
                else:
                    res.append(_scalar(body))
                    pos += 1
            return res
        res: dict = {}
        while pos < len(lines) and lines[pos][0] == indent:
            m = re.match(r"^([\w.\-]+):\s*(.*)$", lines[pos][1])
            if not m:
                raise ValueError(f"YAML 解析失敗: {lines[pos][1]!r}")
            key, rest = m.group(1), m.group(2)
            pos += 1
            if rest:
                res[key] = _scalar(rest)
            elif pos < len(lines) and lines[pos][0] > indent:
                res[key] = parse_block(lines[pos][0])
            elif pos < len(lines) and lines[pos][0] == indent and lines[pos][1].startswith("- "):
                res[key] = parse_block(indent)
            else:
                res[key] = None
        return res

    return parse_block(lines[0][0]) if lines else {}


def load_config(path: str | os.PathLike | None = None) -> dict:
    p = Path(path or os.environ.get("RESEARCH_CONFIG") or REPO_ROOT / "config.yaml")
    text = p.read_text(encoding="utf-8")
    if text.lstrip().startswith("{"):
        cfg = json.loads(text)
        cfg["_path"] = str(p)
        cfg["_root"] = str(p.resolve().parent)
        return cfg
    try:
        import yaml  # type: ignore

        cfg = yaml.safe_load(text)
    except ImportError:
        cfg = mini_yaml(text)
    cfg["_path"] = str(p)
    cfg["_root"] = str(p.resolve().parent)
    return cfg


def resolve(cfg: dict, rel: str) -> Path:
    """config からの相対パスを config.yaml のディレクトリ基準で解決する。"""
    q = Path(rel)
    return q if q.is_absolute() else Path(cfg["_root"]) / q
