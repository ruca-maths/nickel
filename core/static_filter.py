"""ビルド前の静的フィルタ。

コメントと文字列リテラルを除去したコード本体だけを検査し、不正になり得る構文を
即座に拒否する。これは「安く早く落とす」ための第一関門であり、健全性の最終保証は
verifier のカーネル検査と `#print axioms` が担う（二重化）。
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field

# 識別子として現れたら即拒否する語（単語単位で照合）
BANNED_WORDS = [
    "sorry", "admit", "sorryAx", "axiom", "unsafe", "partial", "opaque",
    "implemented_by", "extern", "native_decide", "native", "ofReduceBool", "ofReduceNat",
    "macro", "macro_rules", "syntax", "elab", "elab_rules", "notation", "infix", "infixl",
    "infixr", "prefix", "postfix", "declare_syntax_cat", "initialize", "builtin_initialize",
    "run_cmd", "run_tac", "run_elab", "run_meta", "by_elab", "export", "debug",
    "skipKernelTC", "Lean", "csimp", "unsafeCast", "mutual", "import",
]
# 属性 @[...] / attribute [...] の中で禁止する語
BANNED_ATTRS = {"implemented_by", "extern", "csimp", "export", "init", "builtin_init",
                "macro", "command_elab", "term_elab", "tactic", "env_extension",
                "never_extract", "builtin_command_elab", "builtin_term_elab", "builtin_tactic"}
# 許可する set_option（値の上限は呼び出し側の cap）
NUMERIC_OPTIONS = {"maxHeartbeats", "synthInstance.maxHeartbeats", "maxRecDepth",
                   "synthInstance.maxSize"}
FREE_OPTION_PREFIXES = ("linter.", "pp.", "trace.")
FREE_OPTIONS = {"autoImplicit", "relaxedAutoImplicit"}

# Spec（命題テキスト）でさらに禁止する語
SPEC_EXTRA_WORDS = [
    "theorem", "lemma", "def", "instance", "example", "abbrev", "structure", "class",
    "inductive", "namespace", "end", "section", "open", "variable", "universe",
    "attribute", "set_option", "by", "where", "deriving", "noncomputable", "private",
    "protected", "local", "scoped", "omit", "include",
]

IDENT_CHAR = r"[\w'!?₀-₉ₐ-ₜᵢ-ᵪⱼ]"


@dataclass
class FilterResult:
    ok: bool
    violations: list[str] = field(default_factory=list)
    imports: list[str] = field(default_factory=list)

    def __bool__(self) -> bool:
        return self.ok


def strip_comments_and_strings(src: str) -> tuple[str, list[str]]:
    """コメント・文字列・文字リテラルを空白に置換したコードを返す（改行は保存）。
    閉じていないコメント/文字列は問題として報告する。"""
    out: list[str] = []
    problems: list[str] = []
    i, n = 0, len(src)

    def blank(s: str) -> str:
        return "".join("\n" if ch == "\n" else " " for ch in s)

    while i < n:
        ch = src[i]
        if src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(blank(src[i:j]))
            i = j
        elif src.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/-", j):
                    depth += 1
                    j += 2
                elif src.startswith("-/", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            if depth:
                problems.append("閉じていないブロックコメント")
            out.append(blank(src[i:j]))
            i = j
        elif ch == '"' or (ch == "r" and re.match(r'r#*"', src[i:]) and
                           (i == 0 or not re.match(IDENT_CHAR, src[i - 1]))):
            if ch == "r":
                m = re.match(r'r(#*)"', src[i:])
                hashes = m.group(1)
                end = src.find('"' + hashes, i + len(m.group(0)))
                j = n if end < 0 else end + 1 + len(hashes)
                if end < 0:
                    problems.append("閉じていない文字列")
            else:
                j = i + 1
                while j < n and src[j] != '"':
                    j += 2 if src[j] == "\\" else 1
                if j >= n:
                    problems.append("閉じていない文字列")
                j = min(j + 1, n)
            out.append(blank(src[i:j]))
            i = j
        elif ch == "'" and (i == 0 or not re.match(IDENT_CHAR, src[i - 1])):
            m = re.match(r"'(\\.[^']*|[^'\\])'", src[i:])
            if m:
                out.append(blank(m.group(0)))
                i += len(m.group(0))
            else:
                out.append(ch)
                i += 1
        else:
            out.append(ch)
            i += 1
    return "".join(out), problems


def _word_re(w: str) -> re.Pattern:
    return re.compile(r"(?<![\w.'!?])" + re.escape(w) + r"(?![\w'!?])")


_BANNED_RE = [(w, _word_re(w)) for w in BANNED_WORDS]
_SPEC_RE = [(w, _word_re(w)) for w in SPEC_EXTRA_WORDS]


def _common_checks(code: str, max_heartbeats: int) -> list[str]:
    v: list[str] = []
    for w, rx in _BANNED_RE:
        if w == "import":
            continue
        if rx.search(code):
            v.append(f"禁止語 `{w}`")
    if re.search(r"#[A-Za-z_]", code):
        v.append("`#` コマンド（#eval / #print / #exit 等）は禁止")
    if "«" in code or "»" in code:
        v.append("«» による識別子エスケープは禁止")
    if re.search(r"(?<![\w.])_root_", code):
        v.append("`_root_` は禁止")
    if re.search(r"\+\s*native|\bnative\s*:=", code):
        v.append("native 評価は禁止")
    for m in re.finditer(r"@\[([^\]]*)\]|\battribute\s*\[([^\]]*)\]", code):
        body = m.group(1) if m.group(1) is not None else m.group(2)
        for word in re.findall(r"[A-Za-z_][\w.]*", body):
            if word in BANNED_ATTRS:
                v.append(f"禁止属性 `{word}`")
    for m in re.finditer(r"\bset_option\s+([\w.]+)\s+(\S+)", code):
        name, val = m.group(1), m.group(2)
        if name in NUMERIC_OPTIONS:
            if not val.isdigit() or int(val) == 0 or int(val) > max_heartbeats:
                v.append(f"set_option {name} {val} は許可範囲外（1〜{max_heartbeats}）")
        elif name in FREE_OPTIONS or name.startswith(FREE_OPTION_PREFIXES):
            pass
        else:
            v.append(f"set_option {name} は許可されていない")
    return v


def parse_imports(code: str) -> tuple[list[str], str, list[str]]:
    """先頭の import 列を取り出す。戻り値: (imports, 残りのコード, 問題)。"""
    imports: list[str] = []
    rest = code
    problems: list[str] = []
    pat = re.compile(r"\s*import\s+([A-Za-z_][\w.]*)")
    while True:
        m = pat.match(rest)
        if not m:
            break
        imports.append(m.group(1))
        rest = rest[m.end():]
    if _word_re("import").search(rest):
        problems.append("import はファイル先頭にのみ書ける")
    return imports, rest, problems


def check_proof(src: str, module_id: str, *, allowed_prefixes: list[str],
                allowed_modules: set[str], max_heartbeats: int = 1_000_000,
                forbidden_imports: list[str] | None = None, lib: str = "Proofs") -> FilterResult:
    """証明ファイル Proofs/<module_id>.lean（lib="Defs" なら定義ファイル Defs/<module_id>.lean）の静的検査。
    定義ファイルは theorem main を要求しない。"""
    code, problems = strip_comments_and_strings(src)
    v = list(problems)
    imports, rest, p2 = parse_imports(code)
    v += p2
    for imp in imports:
        ok = imp in allowed_modules or any(imp == p or imp.startswith(p + ".")
                                           for p in allowed_prefixes)
        if imp.startswith(("Proofs.", "Defs.")) and imp not in allowed_modules:
            ok = False  # 証明・定義モジュールは受理済みのものだけ
        if not ok:
            v.append(f"import `{imp}` は許可されていない（Checked でない証明か、許可外モジュール）")
        elif imp in (forbidden_imports or []):
            v.append(f"import `{imp}` は禁止（重すぎる。必要な部分モジュールだけを import すること）")
    v += _common_checks(rest, max_heartbeats)

    ns = f"{lib}.{module_id}"
    body = rest.strip()
    m_ns = re.match(r"namespace\s+([\w.]+)\s", body + "\n")
    if not m_ns or m_ns.group(1) != ns:
        v.append(f"import の直後は `namespace {ns}` でなければならない")
    m_end = re.search(r"\bend\s+([\w.]+)\s*$", body)
    if not m_end or m_end.group(1) != ns:
        v.append(f"ファイル末尾は `end {ns}` でなければならない")
    if len(re.findall(r"\bnamespace\s+" + re.escape(ns) + r"(?![\w.])", body)) != 1:
        v.append(f"`namespace {ns}` はちょうど1回だけ書く")
    # 名前空間を途中で閉じて外側に宣言を置くことを禁止
    closing = {lib, module_id, ns}
    ends = re.findall(r"\bend\s+([\w.]+)", body)
    if sum(1 for e in ends if e in closing) != 1:
        v.append(f"`end {ns}` 以外の方法で名前空間 {ns} を閉じてはならない")
    if lib == "Proofs" and not re.search(r"\btheorem\s+main\b", body):
        v.append("`theorem main` が見つからない")
    return FilterResult(ok=not v, violations=v, imports=imports)


def check_spec_text(text: str, max_len: int = 4000) -> FilterResult:
    """Architect が提案する命題テキスト（Lean の項）の静的検査。"""
    v: list[str] = []
    if len(text) > max_len:
        v.append(f"命題が長すぎる（{len(text)} > {max_len} 文字）")
    code, problems = strip_comments_and_strings(text)
    if code != text:
        v.append("命題にコメントや文字列リテラルを含めてはならない")
    v += problems
    v += _common_checks(code, 0)
    if "set_option" in code:
        v.append("命題に set_option は書けない")
    for w, rx in _SPEC_RE:
        if rx.search(code):
            v.append(f"命題に `{w}` は書けない")
    if ":=" in code:
        v.append("命題に `:=` は書けない")
    if _word_re("import").search(code):
        v.append("命題に import は書けない")
    if not code.strip():
        v.append("命題が空")
    return FilterResult(ok=not v, violations=v)
