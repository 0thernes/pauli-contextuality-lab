#!/usr/bin/env python3
"""Validate every \\lean{...} declaration in blueprint/src/content.tex against lean/
and build an interactive SVG DAG + searchable, dependency-cone-highlighted HTML/JSON
Lean 4 Blueprint with direct GitHub line links at build/site/blueprint/.
"""
from __future__ import annotations

import html
import json
import re
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
TEX_PATH = ROOT / "blueprint" / "src" / "content.tex"
LEAN_DIR = ROOT / "lean"
OUT_DIR = ROOT / "build" / "site" / "blueprint"
REPO_BLOB_BASE = "https://github.com/0thernes/pauli-contextuality-lab/blob/main/lean"

SEC_OR_ENV_RE = re.compile(
    r"\\section\{([^}]+)\}|\\begin\{(theorem|lemma|proposition|corollary|definition)\}(?:\[([^\]]*)\])?(.*?)\\end\{\2\}",
    re.S,
)
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
LEAN_RE = re.compile(r"\\lean\{([^}]+)\}")
USES_RE = re.compile(r"\\uses\{([^}]+)\}")
DECL_LINE_RE = re.compile(
    r"^\s*(?:private\s+|noncomputable\s+|protected\s+)*(?:theorem|lemma|def|structure|abbrev|inductive|instance)\s+([A-Za-z0-9_.']+)"
)
NS_LINE_RE = re.compile(r"^\s*namespace\s+([A-Za-z0-9_.]+)\s*$")
END_LINE_RE = re.compile(r"^\s*end(?:\s+([A-Za-z0-9_.]+))?\s*$")


def index_lean_declarations() -> tuple[dict[str, tuple[str, int]], dict[str, tuple[str, int]]]:
    """Index all Lean declarations under lean/ to exact (relative_posix_path, 1-based line)."""
    exact: dict[str, tuple[str, int]] = {}
    short_map: dict[str, tuple[str, int]] = {}
    for lean_file in sorted(LEAN_DIR.rglob("*.lean")):
        if ".lake" in lean_file.parts:
            continue
        rel = lean_file.relative_to(LEAN_DIR).as_posix()
        text = lean_file.read_text(encoding="utf-8", errors="replace")
        ns_stack: list[list[str]] = []
        for lineno, line in enumerate(text.splitlines(), 1):
            nm = NS_LINE_RE.match(line)
            if nm:
                ns_stack.append(nm.group(1).split("."))
                continue
            em = END_LINE_RE.match(line)
            if em and ns_stack:
                target = em.group(1)
                if target is None:
                    ns_stack.pop()
                else:
                    parts = target.split(".")
                    if ns_stack[-1] == parts:
                        ns_stack.pop()
                    else:
                        flat = [p for frame in ns_stack for p in frame]
                        if len(flat) >= len(parts) and flat[-len(parts) :] == parts:
                            remaining = len(parts)
                            while remaining > 0 and ns_stack:
                                top = ns_stack.pop()
                                remaining -= len(top)
                continue
            dm = DECL_LINE_RE.match(line)
            if dm:
                short = dm.group(1)
                loc = (rel, lineno)
                flat_ns = [p for frame in ns_stack for p in frame]
                full = ".".join([*flat_ns, short]) if flat_ns else short
                exact.setdefault(full, loc)
                # Also index suffix matches for nested namespaces (e.g. `HoggarBound.foo`)
                for i in range(1, len(flat_ns)):
                    exact.setdefault(".".join([*flat_ns[i:], short]), loc)
                short_map.setdefault(short, loc)
    return exact, short_map


def resolve_decl_location(
    decl: str,
    exact: dict[str, tuple[str, int]],
    short_map: dict[str, tuple[str, int]],
) -> tuple[str, int] | None:
    if decl in exact:
        return exact[decl]
    # Try suffix matching against exact keys
    suffix = "." + decl
    for key, loc in exact.items():
        if key.endswith(suffix):
            return loc
    short = decl.split(".")[-1]
    if short in short_map:
        return short_map[short]
    return None


def classify_track(section: str) -> str:
    low = section.lower()
    if "track 1" in low:
        return "track1"
    if "track 2" in low:
        return "track2"
    if "track 3" in low:
        return "track3"
    return "bridge"


def parse_blueprint(tex: str) -> list[dict[str, Any]]:
    nodes: list[dict[str, Any]] = []
    current_section = "Track 1"
    for m in SEC_OR_ENV_RE.finditer(tex):
        if m.group(1) is not None:
            current_section = m.group(1).strip()
            continue
        kind, title, body = m.group(2), (m.group(3) or "").strip(), m.group(4)
        label_m = LABEL_RE.search(body)
        label = label_m.group(1).strip() if label_m else f"node-{len(nodes)}"
        lean_decls: list[str] = []
        for lm in LEAN_RE.finditer(body):
            lean_decls.extend(x.strip() for x in lm.group(1).split(",") if x.strip())
        uses: list[str] = []
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
                "track": classify_track(current_section),
                "section": current_section,
                "title": title or label,
                "lean": lean_decls,
                "uses": uses,
                "leanok": leanok,
                "summary": prose[:360],
            }
        )
    return nodes


def plain_svg_text(text: str) -> str:
    """Convert short LaTeX title strings into clean Unicode for SVG node labels."""
    s = text.replace(r"\&", "&").replace(r"\_", "_").replace("--", "–")
    repl = [
        (r"$\vert\Psi_{3m}\rangle$", "|Ψ₃ₘ⟩"),
        (r"\vert\Psi_{3m}\rangle", "|Ψ₃ₘ⟩"),
        (r"\Psi_{3m}", "Ψ₃ₘ"),
        (r"\ge", "≥"),
        (r"\le", "≤"),
        (r"\mathbb{F}_2^{2N}", "𝔽₂²ᴺ"),
        (r"\mathbb{F}_2", "𝔽₂"),
        (r"Q^+(9,2)", "Q⁺(9,2)"),
        (r"Q^-(7,2)", "Q⁻(7,2)"),
        (r"\times", "×"),
        (r"\pm", "±"),
    ]
    for old, new in repl:
        s = s.replace(old, new)
    s = s.replace("$", "").replace("{", "").replace("}", "")
    return re.sub(r"\s+", " ", s).strip()


def clean_html_math(text: str) -> str:
    """Escape HTML while cleaning text-mode LaTeX escapes outside $...$ for MathJax rendering."""
    parts = text.split("$")
    out: list[str] = []
    for idx, part in enumerate(parts):
        if idx % 2 == 0:
            cleaned = part.replace(r"\&", "&").replace(r"\_", "_").replace("--", "–")
            out.append(html.escape(cleaned))
        else:
            out.append("$" + html.escape(part) + "$")
    return "".join(out)


def render_svg_dag(nodes: list[dict[str, Any]]) -> str:
    by_id: dict[str, dict[str, Any]] = {n["id"]: n for n in nodes}
    depth_cache: dict[str, int] = {}

    def depth(nid: str, seen: set[str]) -> int:
        if nid in depth_cache:
            return depth_cache[nid]
        if nid in seen or nid not in by_id:
            return 0
        seen2 = seen | {nid}
        deps = [u for u in by_id[nid]["uses"] if u in by_id]
        d = 0 if not deps else 1 + max(depth(u, seen2) for u in deps)
        depth_cache[nid] = d
        return d

    layers: dict[int, list[dict[str, Any]]] = {}
    for n in nodes:
        d = depth(n["id"], set())
        layers.setdefault(d, []).append(n)

    max_cols = max((len(v) for v in layers.values()), default=1)
    node_w, node_h = 188, 48
    gap_x, gap_y = 22, 46
    pad_x, pad_y = 24, 24
    width = max(920, pad_x * 2 + max_cols * node_w + max(0, max_cols - 1) * gap_x)
    height = pad_y * 2 + len(layers) * node_h + max(0, len(layers) - 1) * gap_y

    coords: dict[str, tuple[float, float]] = {}
    for lvl in sorted(layers):
        row = layers[lvl]
        row_w = len(row) * node_w + max(0, len(row) - 1) * gap_x
        start_x = (width - row_w) / 2.0
        y = float(pad_y + lvl * (node_h + gap_y))
        for idx, n in enumerate(row):
            x = float(start_x + idx * (node_w + gap_x))
            coords[n["id"]] = (x, y)

    track_colors = {
        "track1": ("#0c4a6e", "#38bdf8"),
        "track2": ("#14532d", "#4ade80"),
        "track3": ("#4c1d95", "#c084fc"),
        "bridge": ("#78350f", "#fbbf24"),
    }

    edges_svg: list[str] = []
    for n in nodes:
        x2, y2 = coords[n["id"]]
        cx2, cy2 = x2 + node_w / 2.0, y2
        for u in n["uses"]:
            if u not in coords:
                continue
            x1, y1 = coords[u]
            cx1, cy1 = x1 + node_w / 2.0, y1 + node_h
            mid_y = (cy1 + cy2) / 2.0
            edges_svg.append(
                f'<path class="dag-edge" data-from="{html.escape(u)}" data-to="{html.escape(n["id"])}" '
                f'd="M {cx1:.1f} {cy1:.1f} C {cx1:.1f} {mid_y:.1f}, {cx2:.1f} {mid_y:.1f}, {cx2:.1f} {cy2:.1f}" '
                f'fill="none" stroke="#475569" stroke-width="1.5" marker-end="url(#arrow)"/>'
            )

    nodes_svg: list[str] = []
    for n in nodes:
        x, y = coords[n["id"]]
        fill, stroke = track_colors.get(n["track"], ("#1e293b", "#94a3b8"))
        short_title = plain_svg_text(n["title"])
        if len(short_title) > 27:
            short_title = short_title[:25].rstrip() + "…"
        sub = f'{n["kind"]} · {len(n["lean"])} Lean decls'
        nodes_svg.append(
            f'<a href="#{html.escape(n["id"])}" class="dag-node" data-id="{html.escape(n["id"])}" '
            f'data-track="{html.escape(n["track"])}" data-title="{html.escape(plain_svg_text(n["title"]))}">'
            f'<rect x="{x:.1f}" y="{y:.1f}" width="{node_w}" height="{node_h}" rx="9" '
            f'fill="{fill}" stroke="{stroke}" stroke-width="1.5"/>'
            f'<text x="{x + 10:.1f}" y="{y + 20:.1f}" fill="#f8fafc" font-size="11.5" font-weight="600">'
            f"{html.escape(short_title)}</text>"
            f'<text x="{x + 10:.1f}" y="{y + 36:.1f}" fill="#cbd5e1" font-size="10">'
            f"{html.escape(sub)}</text></a>"
        )

    return (
        f'<svg id="dag" viewBox="0 0 {width} {height}" width="100%" role="img" '
        f'aria-label="Interactive Lean 4 theorem dependency graph">'
        f'<defs><marker id="arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" '
        f'orient="auto-start-reverse"><path d="M 0 1 L 10 5 L 0 9 z" fill="#64748b"/></marker>'
        f'<marker id="arrow-hi" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" '
        f'orient="auto-start-reverse"><path d="M 0 1 L 10 5 L 0 9 z" fill="#38bdf8"/></marker></defs>'
        f'{"".join(edges_svg)}{"".join(nodes_svg)}</svg>'
    )


def render_html(nodes: list[dict[str, Any]]) -> str:
    total_decls = sum(len(n["lean"]) for n in nodes)
    bridge_targets = sum(len(n["lean"]) for n in nodes if n["track"] == "bridge")
    counts = {
        "all": len(nodes),
        "track1": sum(1 for n in nodes if n["track"] == "track1"),
        "track2": sum(1 for n in nodes if n["track"] == "track2"),
        "track3": sum(1 for n in nodes if n["track"] == "track3"),
        "bridge": sum(1 for n in nodes if n["track"] == "bridge"),
    }
    svg = render_svg_dag(nodes)
    graph_data = {
        n["id"]: {"uses": n["uses"], "title": plain_svg_text(n["title"])} for n in nodes
    }
    graph_json = json.dumps(graph_data, ensure_ascii=False)
    rows: list[str] = []
    for n in nodes:
        badge = '<span class="ok">Lean 4 verified</span>' if n["leanok"] else '<span class="wip">Paper / open</span>'
        decl_chips: list[str] = []
        for link in n["lean_links"]:
            tip = f'{link["file"]}:L{link["line"]}'
            decl_chips.append(
                f'<a class="decl-link" href="{html.escape(link["url"])}" target="_blank" rel="noopener" '
                f'title="{html.escape(tip)}"><code>{html.escape(link["name"])}</code></a>'
            )
        decls = " ".join(decl_chips) or "<em>—</em>"
        deps = ", ".join(f'<a href="#{html.escape(u)}">{html.escape(u)}</a>' for u in n["uses"]) or "<em>root</em>"
        search_blob = " ".join(
            [n["id"], plain_svg_text(n["title"]), n["summary"], " ".join(n["lean"])]
        ).lower()
        rows.append(
            f'<article class="card" id="{html.escape(n["id"])}" data-track="{html.escape(n["track"])}" '
            f'data-search="{html.escape(search_blob)}">'
            f'<div class="hdr"><span class="kind">{html.escape(n["kind"].upper())}</span>'
            f'<h3>{clean_html_math(n["title"])}</h3>{badge}</div>'
            f'<p class="sum">{clean_html_math(n["summary"])}</p>'
            f'<div class="meta"><b>Lean ({len(n["lean"])}):</b> <span class="decl-list">{decls}</span><br/>'
            f'<b>Uses:</b> {deps} &middot; <button type="button" class="cone-btn" data-cone="{html.escape(n["id"])}">Highlight cone</button></div>'
            f"</article>"
        )
    return f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8"/><meta name="viewport" content="width=device-width,initial-scale=1"/>
<title>Pauli Contextuality Lab · Lean 4 Dependency Blueprint</title>
<script>window.MathJax={{tex:{{inlineMath:[["$","$"]]}}}};</script>
<script defer src="https://cdnjs.cloudflare.com/ajax/libs/mathjax/3.2.2/es5/tex-chtml-full.min.js" integrity="sha384-dCtf/9Xgzj8edI30iIEsxNfjUQ0zj2AXa3eUdgjsx8odUmpURZx5Z7aDZmV781et" crossorigin="anonymous"></script>
<style>
body{{font-family:system-ui,-apple-system,Segoe UI,Roboto,sans-serif;background:#0b1020;color:#e2e8f0;margin:0;padding:1.75rem;line-height:1.5}}
main{{max-width:1240px;margin:0 auto}}
h1{{margin:0 0 .35rem;font-size:2rem;color:#f8fafc}}
.sub{{color:#94a3b8;margin-bottom:1rem}}
.toolbar{{display:flex;flex-wrap:wrap;gap:.5rem;margin-bottom:.85rem;align-items:center}}
.btn{{background:#131c33;border:1px solid #334155;color:#e2e8f0;padding:.4rem .8rem;border-radius:999px;cursor:pointer;font-size:.82rem;font-weight:600}}
.btn.active{{background:#0284c7;border-color:#38bdf8;color:#fff}}
.search{{flex:1 1 240px;min-width:210px;background:#0f172a;border:1px solid #334155;color:#f8fafc;padding:.45rem .8rem;border-radius:999px;font-size:.84rem}}
.search:focus{{outline:2px solid #38bdf8;outline-offset:1px}}
.cone-status{{display:none;align-items:center;justify-content:space-between;gap:.75rem;flex-wrap:wrap;background:#111d36;border:1px solid #38bdf8;border-radius:10px;padding:.5rem .85rem;margin-bottom:.75rem;font-size:.84rem;color:#e2e8f0}}
.cone-status.visible{{display:flex}}
.cone-clear{{background:#1e293b;border:1px solid #475569;color:#f8fafc;padding:.25rem .65rem;border-radius:999px;cursor:pointer;font-size:.76rem;font-weight:600}}
.dag-wrap{{background:#0f172a;border:1px solid #1e293b;border-radius:14px;padding:.75rem;overflow-x:auto;margin-bottom:1.5rem}}
.dag-node rect{{transition:opacity .15s,stroke-width .15s,stroke .15s}}
.dag-node:hover rect{{stroke-width:2.5;filter:brightness(1.18)}}
.dag-node.cone-focus rect{{stroke:#ffffff!important;stroke-width:3!important}}
.dag-node.cone-up rect{{stroke:#fbbf24!important;stroke-width:2.5!important}}
.dag-node.cone-down rect{{stroke:#4ade80!important;stroke-width:2.5!important}}
.dag-edge{{transition:opacity .15s,stroke .15s,stroke-width .15s}}
.dag-edge.cone-active{{stroke:#38bdf8!important;stroke-width:2.4!important;opacity:1!important}}
.grid{{display:grid;grid-template-columns:repeat(auto-fill,minmax(350px,1fr));gap:1rem}}
.card{{background:#131c33;border:1px solid #23304f;border-radius:12px;padding:1rem;scroll-margin-top:1rem;transition:border-color .15s,box-shadow .15s,opacity .15s}}
.card:target,.card.cone-focus{{border-color:#38bdf8;box-shadow:0 0 0 2px rgba(56,189,248,.35)}}
.card.cone-up{{border-color:#fbbf24}}
.card.cone-down{{border-color:#4ade80}}
.hdr{{display:flex;flex-wrap:wrap;align-items:center;gap:.5rem;margin-bottom:.45rem}}
.hdr h3{{margin:0;font-size:1.02rem;flex:1;color:#f8fafc}}
.kind{{font-size:.68rem;font-weight:700;padding:.15rem .45rem;border-radius:6px;background:#1e293b;color:#38bdf8}}
.ok{{font-size:.7rem;font-weight:700;padding:.15rem .5rem;border-radius:999px;background:#064e3b;color:#6ee7b7}}
.wip{{font-size:.7rem;font-weight:700;padding:.15rem .5rem;border-radius:999px;background:#451a03;color:#fcd34d}}
.sum{{font-size:.87rem;color:#cbd5e1;margin:.35rem 0 .65rem}}
.meta{{font-size:.78rem;color:#94a3b8;overflow-wrap:anywhere}}
.decl-list{{display:inline-flex;flex-wrap:wrap;gap:.25rem;vertical-align:middle}}
.decl-link{{text-decoration:none}}
.decl-link code{{background:#0f172a;border:1px solid #1e293b;padding:.08rem .32rem;border-radius:4px;color:#7dd3fc;transition:border-color .15s,color .15s}}
.decl-link:hover code{{border-color:#38bdf8;color:#e0f2fe}}
.cone-btn{{background:transparent;border:1px solid #334155;color:#cbd5e1;border-radius:999px;padding:.1rem .5rem;font-size:.72rem;cursor:pointer;margin-left:.25rem}}
.cone-btn:hover{{border-color:#38bdf8;color:#fff}}
code{{background:#0f172a;padding:.1rem .3rem;border-radius:4px;color:#7dd3fc}}
a{{color:#38bdf8;text-decoration:none}}
.legend{{display:flex;flex-wrap:wrap;gap:1rem;font-size:.8rem;color:#94a3b8;margin-bottom:.6rem}}
.dot{{display:inline-block;width:10px;height:10px;border-radius:3px;margin-right:.35rem;vertical-align:middle}}
</style></head><body><main>
<p><a href="../">&larr; Back to Pauli Contextuality Lab</a></p>
<h1>Lean 4.35.0 Dependency Blueprint</h1>
<p class="sub">{len(nodes)} formal nodes &middot; {total_decls} statically verified Lean declarations linked to exact GitHub source lines across Tracks 1&ndash;3 (<code>HoggarBound</code>, <code>ContextualityTensor</code>, <code>Evidence</code>) and the {bridge_targets}-target 6-kernel Comparator Bridge. Hover or click any graph node to inspect its dependency cone, or click any Lean declaration chip to open its source line on GitHub.</p>
<div class="legend">
  <span><i class="dot" style="background:#38bdf8"></i>Track 1: Spectral Bounds &amp; Conjecture E</span>
  <span><i class="dot" style="background:#4ade80"></i>Track 2: Disjoint Mermin (Muller &amp; Saniga Sec. 6)</span>
  <span><i class="dot" style="background:#c084fc"></i>Track 3: Sequential Evidence</span>
  <span><i class="dot" style="background:#fbbf24"></i>6-Kernel Comparator Bridge</span>
</div>
<div class="toolbar" role="group" aria-label="Filter and search blueprint">
  <button class="btn active" data-filter="all">All ({counts["all"]})</button>
  <button class="btn" data-filter="track1">Track 1 ({counts["track1"]})</button>
  <button class="btn" data-filter="track2">Track 2 ({counts["track2"]})</button>
  <button class="btn" data-filter="track3">Track 3 ({counts["track3"]})</button>
  <button class="btn" data-filter="bridge">6-Kernel Bridge ({counts["bridge"]})</button>
  <input id="search" class="search" type="search" placeholder="Search theorems or Lean declarations…" aria-label="Search blueprint nodes"/>
</div>
<div id="cone-status" class="cone-status" role="status" aria-live="polite">
  <span id="cone-text"></span>
  <button type="button" id="cone-clear" class="cone-clear">Clear cone</button>
</div>
<section class="dag-wrap">{svg}</section>
<section class="grid">{"".join(rows)}</section>
<script>
const GRAPH = {graph_json};
const btns = document.querySelectorAll('.btn[data-filter]');
const cards = document.querySelectorAll('.card[data-track]');
const svgNodes = document.querySelectorAll('.dag-node[data-track]');
const svgEdges = document.querySelectorAll('.dag-edge');
const searchInput = document.getElementById('search');
const coneStatus = document.getElementById('cone-status');
const coneText = document.getElementById('cone-text');
const coneClear = document.getElementById('cone-clear');

let activeTrack = 'all';
let pinnedCone = null;

function computeCone(rootId) {{
  const up = new Set();
  const down = new Set();
  const qUp = [...(GRAPH[rootId]?.uses || [])];
  while (qUp.length) {{
    const cur = qUp.shift();
    if (!cur || up.has(cur) || !GRAPH[cur]) continue;
    up.add(cur);
    for (const p of GRAPH[cur].uses || []) qUp.push(p);
  }}
  const rev = {{}};
  for (const [id, info] of Object.entries(GRAPH)) {{
    for (const u of info.uses || []) {{
      if (!rev[u]) rev[u] = [];
      rev[u].push(id);
    }}
  }}
  const qDown = [...(rev[rootId] || [])];
  while (qDown.length) {{
    const cur = qDown.shift();
    if (!cur || down.has(cur)) continue;
    down.add(cur);
    for (const nxt of rev[cur] || []) qDown.push(nxt);
  }}
  return {{ up, down }};
}}

function applyView(hoverId = null) {{
  const q = (searchInput.value || '').trim().toLowerCase();
  const focusId = hoverId || pinnedCone;
  const cone = focusId ? computeCone(focusId) : null;
  const visible = new Set();

  cards.forEach(c => {{
    const trackOk = activeTrack === 'all' || c.dataset.track === activeTrack;
    const queryOk = !q || (c.dataset.search || '').includes(q);
    const show = trackOk && queryOk;
    c.style.display = show ? '' : 'none';
    if (show) visible.add(c.id);
    c.classList.remove('cone-focus', 'cone-up', 'cone-down');
    if (cone) {{
      if (c.id === focusId) c.classList.add('cone-focus');
      else if (cone.up.has(c.id)) c.classList.add('cone-up');
      else if (cone.down.has(c.id)) c.classList.add('cone-down');
    }}
  }});

  svgNodes.forEach(n => {{
    const id = n.dataset.id;
    n.classList.remove('cone-focus', 'cone-up', 'cone-down');
    if (cone) {{
      const inCone = id === focusId || cone.up.has(id) || cone.down.has(id);
      if (id === focusId) n.classList.add('cone-focus');
      else if (cone.up.has(id)) n.classList.add('cone-up');
      else if (cone.down.has(id)) n.classList.add('cone-down');
      n.style.opacity = inCone ? '1' : '0.16';
    }} else {{
      n.style.opacity = visible.has(id) ? '1' : '0.18';
    }}
  }});

  svgEdges.forEach(e => {{
    const a = e.dataset.from;
    const b = e.dataset.to;
    e.classList.remove('cone-active');
    if (cone) {{
      const inA = a === focusId || cone.up.has(a) || cone.down.has(a);
      const inB = b === focusId || cone.up.has(b) || cone.down.has(b);
      const activeEdge = inA && inB && !((cone.up.has(a) && cone.down.has(b)) || (cone.down.has(a) && cone.up.has(b)));
      if (activeEdge) {{
        e.classList.add('cone-active');
        e.setAttribute('marker-end', 'url(#arrow-hi)');
      }} else {{
        e.style.opacity = '0.09';
        e.setAttribute('marker-end', 'url(#arrow)');
      }}
    }} else {{
      e.style.opacity = (visible.has(a) && visible.has(b)) ? '0.9' : '0.12';
      e.setAttribute('marker-end', 'url(#arrow)');
    }}
  }});

  if (focusId && cone) {{
    const title = GRAPH[focusId]?.title || focusId;
    coneText.textContent = `${{pinnedCone ? 'Pinned' : 'Preview'}} cone: ${{title}} · ${{cone.up.size}} upstream prerequisite(s) (gold) · ${{cone.down.size}} downstream corollary/target(s) (green)`;
    coneStatus.classList.add('visible');
  }} else {{
    coneStatus.classList.remove('visible');
  }}
}}

btns.forEach(b => b.addEventListener('click', () => {{
  activeTrack = b.dataset.filter;
  btns.forEach(x => x.classList.toggle('active', x === b));
  applyView();
}}));
searchInput.addEventListener('input', () => applyView());
svgNodes.forEach(n => {{
  n.addEventListener('mouseenter', () => applyView(n.dataset.id));
  n.addEventListener('mouseleave', () => applyView(null));
  n.addEventListener('click', () => {{
    pinnedCone = n.dataset.id;
    applyView();
  }});
}});
document.querySelectorAll('.cone-btn[data-cone]').forEach(btn => {{
  btn.addEventListener('click', () => {{
    pinnedCone = pinnedCone === btn.dataset.cone ? null : btn.dataset.cone;
    applyView();
    if (pinnedCone) document.querySelector('.dag-wrap').scrollIntoView({{ behavior: 'smooth', block: 'nearest' }});
  }});
}});
coneClear.addEventListener('click', () => {{ pinnedCone = null; applyView(); }});
</script>
</main></body></html>
"""


def main() -> int:
    if not TEX_PATH.is_file():
        print(f"ERROR: missing {TEX_PATH}", file=sys.stderr)
        return 1
    nodes = parse_blueprint(TEX_PATH.read_text(encoding="utf-8"))
    exact, short_map = index_lean_declarations()

    missing: list[tuple[str, str]] = []
    for n in nodes:
        lean_links: list[dict[str, Any]] = []
        for d in n["lean"]:
            loc = resolve_decl_location(d, exact, short_map)
            if loc is None:
                missing.append((n["id"], d))
            else:
                rel, lineno = loc
                lean_links.append(
                    {
                        "name": d,
                        "file": f"lean/{rel}",
                        "line": lineno,
                        "url": f"{REPO_BLOB_BASE}/{rel}#L{lineno}",
                    }
                )
        n["lean_links"] = lean_links

    node_ids = {n["id"] for n in nodes}
    bad_uses = [(n["id"], u) for n in nodes for u in n["uses"] if u not in node_ids]

    if missing:
        print("Blueprint validation FAILED — missing Lean declarations:", file=sys.stderr)
        for nid, d in missing:
            print(f"  [{nid}] {d}", file=sys.stderr)
        return 1
    if bad_uses:
        print("Blueprint validation FAILED — broken \\uses references:", file=sys.stderr)
        for nid, u in bad_uses:
            print(f"  [{nid}] uses unknown label {u}", file=sys.stderr)
        return 1

    OUT_DIR.mkdir(parents=True, exist_ok=True)
    (OUT_DIR / "index.html").write_text(render_html(nodes), encoding="utf-8")
    (OUT_DIR / "blueprint.json").write_text(json.dumps(nodes, indent=2) + "\n", encoding="utf-8")
    total_decls = sum(len(n["lean"]) for n in nodes)
    print(f"PASS: Blueprint validated {len(nodes)} nodes ({total_decls} Lean decls with exact GitHub #L links) -> {OUT_DIR}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
