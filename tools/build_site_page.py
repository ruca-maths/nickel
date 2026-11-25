"""site/template.html（Artifact 用の埋め込み版）から、GitHub Pages 用の index.html を作る。

index.html は開くたびに status/site.json を読むので、データが変わっても作り直す必要はない。
ページのデザインを変えたときだけ実行する:  python tools/build_site_page.py
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
s = (ROOT / "site" / "template.html").read_text(encoding="utf-8")


def sub(a: str, b: str) -> None:
    global s
    assert s.count(a) == 1, a
    s = s.replace(a, b)


sub('<script id="data" type="application/json">/*DATA*/</script>\n', "")
sub('(() => {\n  const D = JSON.parse(document.getElementById("data").textContent);', "function render(D) {")
sub('    exhausted: { label: "試行上限", cls: "s-dead", v: "--dead", bg: "--dead-bg" },\n  };',
    '    exhausted: { label: "試行上限", cls: "s-dead", v: "--dead", bg: "--dead-bg" },\n'
    '    work: { label: "作業中", cls: "s-work", v: "--work", bg: "--work-bg" },\n  };\n'
    '  const busy = new Set((D.running || []).map((r) => r.node));')
sub('  const stateOf = (n) => (n.status === "open" && n.exhausted ? "exhausted" : n.status);',
    '  const stateOf = (n) => (n.status !== "open" ? n.status : busy.has(n.id) ? "work" '
    ': n.exhausted ? "exhausted" : "open");')
sub('["checked", "open", "refuted", "exhausted"]', '["checked", "work", "open", "refuted", "exhausted"]')
sub('<span>スナップショット: ${esc(D.generated_at)} 時点（親機の <span class="mono">status/graph.json</span> と DB から生成）。</span>',
    '<span>データ: ${esc(D.generated_at)} 時点（親機が sync のたびに <span class="mono">status/site.json</span> '
    'を更新。開き直すと最新になります）。本日の支出 $${Number(D.spent_today || 0).toFixed(2)}。</span>')
sub("})();\n</script>",
    "}\n\n"
    'fetch("status/site.json", { cache: "no-store" })\n'
    "  .then((r) => { if (!r.ok) throw new Error(r.status); return r.json(); })\n"
    "  .then(render)\n"
    "  .catch((e) => {\n"
    '    document.getElementById("verdict").innerHTML =\n'
    "      `<span class=\"pill s-refuted\">データを読めません</span><span>status/site.json を取得できませんでした"
    "（${String(e)}）。少し待って開き直してください。</span>`;\n"
    "  });\n</script>")
# GitHub Pages では文書の骨組みが付かないので自前で付ける
s = ('<!doctype html>\n<html lang="ja">\n<head>\n<meta charset="utf-8">\n'
     '<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">\n') + s
sub("</style>\n\n<div class=\"wrap\">", "</style>\n</head>\n<body>\n<div class=\"wrap\">")
s = s.rstrip() + "\n</body>\n</html>\n"
(ROOT / "index.html").write_text(s, encoding="utf-8")
print("index.html を生成しました", len(s), "文字")
