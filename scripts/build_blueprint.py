#!/usr/bin/env python3
"""Validate every \\lean{...} declaration in blueprint/src/content.tex against lean/
and build an interactive HTML + JSON Lean Blueprint dependency graph at build/site/blueprint/.
"""
from __future__ import annotations

import html
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TEX_PATH = ROOT / "blueprint" / "src" / "content.tex"
LEAN_DIR = ROOT / "lean"
OUT_DIR = ROOT / "build" / "site" / "blueprint"

ENV_RE = re.compile(
    r"\\begin\{(theorem|lemma|proposition|corollary|definition)\}(?:\[([^\]]*)\])?(.*?)\\end\{\1\}",
    re.S,
)
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
LEAN_RE = re.compile(r"\\lean\{([^}]+)\}")
USES_RE = re.compile(r"\\uses\{([^}]+)\}")
DECL_RE = re.compile(r"^\s*(?:private\s+|noncomputable\s+|protected\s+)*(?:theorem|lemma|def|structure|abbrev|inductive|instance)\s+([A-Za-z0-9_.']+)", re.M)
NS_RE = re.compile(r"^\s*namespace\s+([A-Za-z0-9_.]+)", re.M)


def index_lean_declarations() -> set[str]:
    found: set[str] = set()
    for lean_file in LEAN_DIR.rglob("*.lean"):
        if ".lake" in lean_file.parts:
            continue
        text = lean_file.read_text(encoding="utf-8", errors="replace")
        namespaces = NS_RE.findall(text)
        for m in DECL_RE.finditer(text):
            short = m.group(1)
            found.add(short)
            for ns in namespaces:
                found.add(f"{ns}.{short}")
    return found


def parse_blueprint(tex: str) -> list[dict]:
    nodes = []
    for m in ENV_RE.finditer(tex):
        kind, title, body = m.group(1), (m.group(2) or "").strip(), m.group(3)
        label_m = LABEL_RE.search(body)
        label = label_m.group(1).strip() if label_m else f"node-{len(nodes)}"
        lean_decls = []
        for lm in LEAN_RE.finditer(body):
            lean_decls.extend(x.strip() for x in lm.group(1).split(",") if x.strip())
        uses = []
        for um in USES_RE.finditer(body):
            uses.extend(x.strip() for x in um.group(1).split(",") if x.strip())
        leanok = "\\leanok" in body
        prose = re.sub(r"\\(label|lean|uses)\{[^}]*\}", "", body)
        prose = prose.replace("\\leanok", "").replace("\\mathlibok", "").strip()
        prose = re.sub(r"\s+", " ", prose)
        nodes.append(
            {
                "id": label,
                "kind": kind,
                "title": title or label,
                "lean": lean_decls,
                "uses": uses,
                "leanok": leanok,
                "summary": prose[:320],
            }
        )
    return nodes


def render_html(nodes: list[dict]) -> str:
    rows = []
    for n in nodes:
        badge = '<span class="ok">Lean 4 verified</span>' if n["leanok"] else '<span class="wip">Paper / open</span>'
        decls = ", ".join(f"<code>{html.escape(d)}</code>" for d in n["lean"]) or "<em>—</em>"
        deps = ", ".join(f'<a href="#{html.escape(u)}">{html.escape(u)}</a>' for u in n["uses"]) or "<em>root</em>"
        rows.append(
            f'<article class="card" id="{html.escape(n["id"])}">'
            f'<div class="hdr"><span class="kind">{html.escape(n["kind"].upper())}</span>'
            f'<h3>{html.escape(n["title"])}</h3>{badge}</div>'
            f'<p class="sum">{html.escape(n["summary"])}</p>'
            f'<div class="meta"><b>Lean:</b> {decls}<br/><b>Uses:</b> {deps}</div>'
            f"</article>"
        )
    return f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8"/><meta name="viewport" content="width=device-width,initial-scale=1"/>
<title>Pauli Contextuality Lab · Lean 4 Blueprint</title>
<style>
body{{font-family:system-ui,-apple-system,Segoe UI,Roboto,sans-serif;background:#0b1020;color:#e2e8f0;margin:0;padding:2rem;line-height:1.5}}
main{{max-width:1100px;margin:0 auto}}
h1{{margin:0 0 .4rem;font-size:2rem;color:#f8fafc}}
.sub{{color:#94a3b8;margin-bottom:1.5rem}}
.grid{{display:grid;grid-template-columns:repeat(auto-fill,minmax(320px,1fr));gap:1rem}}
.card{{background:#131c33;border:1px solid #23304f;border-radius:12px;padding:1rem}}
.hdr{{display:flex;flex-wrap:wrap;align-items:center;gap:.5rem;margin-bottom:.5rem}}
.hdr h3{{margin:0;font-size:1.05rem;flex:1}}
.kind{{font-size:.7rem;font-weight:700;padding:.15rem .45rem;border-radius:6px;background:#1e293b;color:#38bdf8}}
.ok{{font-size:.72rem;font-weight:700;padding:.15rem .5rem;border-radius:999px;background:#064e3b;color:#6ee7b7}}
.wip{{font-size:.72rem;font-weight:700;padding:.15rem .5rem;border-radius:999px;background:#451a03;color:#fcd34d}}
.sum{{font-size:.88rem;color:#cbd5e1;margin:.4rem 0 .7rem}}
.meta{{font-size:.8rem;color:#94a3b8}}
code{{background:#0f172a;padding:.1rem .3rem;border-radius:4px;color:#7dd3fc}}
a{{color:#38bdf8;text-decoration:none}}
</style></head><body><main>
<p><a href="../">← Back to Pauli Contextuality Lab</a></p>
<h1>Lean 4.35.0 Dependency Blueprint</h1>
<p class="sub">{len(nodes)} formal nodes across Tracks 1–3 (`HoggarBound`, `ContextualityTensor`, `Evidence`). Every <code>\\lean{{...}}</code> tag below is statically checked against <code>lean/</code>.</p>
<section class="grid">{''.join(rows)}</section>
</main></body></html>
"""


def main() -> int:
    if not TEX_PATH.is_file():
        print(f"ERROR: missing {TEX_PATH}", file=sys.stderr)
        return 1
    nodes = parse_blueprint(TEX_PATH.read_text(encoding="utf-8"))
    decls = index_lean_declarations()

    missing = []
    for n in nodes:
        for d in n["lean"]:
            short = d.split(".")[-1]
            if d not in decls and short not in decls:
                missing.append((n["id"], d))

    if missing:
        print(f"ERROR: blueprint references missing Lean declarations: {missing}", file=sys.stderr)
        return 1

    OUT_DIR.mkdir(parents=True, exist_ok=True)
    (OUT_DIR / "index.html").write_text(render_html(nodes), encoding="utf-8")
    (OUT_DIR / "blueprint.json").write_text(json.dumps({"nodes": nodes}, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: Blueprint validated {len(nodes)} nodes ({sum(len(n['lean']) for n in nodes)} Lean decl refs) -> {OUT_DIR}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
