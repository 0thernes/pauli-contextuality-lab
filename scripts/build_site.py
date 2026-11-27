#!/usr/bin/env python3
"""Assemble and link-check the single unified GitHub Pages site at build/site/.

Mounts:
  /                       Unified landing portal for all 3 tracks
  /blueprint/             Lean 4.35.0 interactive dependency Blueprint
  /c3-lab/                Track 1 interactive C3 exact-certificate browser lab
  /independent-review/    Track 1 independent review explorer
  /disjoint-mermin/       Track 2 interactive 4-qubit Mermin-square lab
  /sequential-evidence/   Track 3 interactive sequential evidence lab
  /papers/                All 3 research preprints (PDF, HTML, and figures)
  /results/               Referenced audit reports for interactive explorers
  /vendor/moonlab/        Single deduplicated Moonlab WASM runtime
"""
from __future__ import annotations

import re
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SITE = ROOT / "build" / "site"


def copy_if_dir(src: Path, dst: Path) -> None:
    if not src.is_dir():
        return
    if dst.exists():
        shutil.rmtree(dst)
    shutil.copytree(src, dst)


def copy_if_file(src: Path, dst: Path) -> None:
    if not src.is_file():
        return
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, dst)


def render_portal() -> str:
    version = (ROOT / "VERSION").read_text(encoding="utf-8").strip()
    return f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8"/>
  <meta name="viewport" content="width=device-width,initial-scale=1"/>
  <title>Pauli Contextuality Lab · v{version}</title>
  <meta name="description" content="Machine-checked Lean 4.35.0 &amp; 6-kernel verified research laboratory for Pauli contextuality: spectral floor, |Psi_{{3m}}&gt;, Jonah Conjecture E, disjoint Mermin degrees, and sequential contextuality evidence."/>
  <meta property="og:title" content="Pauli Contextuality Lab"/>
  <meta property="og:description" content="2,452 exhaustively audited Lean 4.35.0 theorems, 24-target 6-kernel comparator, 29-node interactive SVG Blueprint, and 4 browser labs."/>
  <meta property="og:type" content="website"/>
  <style>
    :root {{ color-scheme: dark; }}
    body {{ font-family: system-ui, -apple-system, Segoe UI, Roboto, sans-serif; background: #0b1020; color: #e2e8f0; margin: 0; line-height: 1.55; }}
    header {{ background: linear-gradient(135deg, #0f172a, #172554); border-bottom: 1px solid #1e3a8a; padding: 3rem 1.5rem 2.5rem; }}
    .wrap {{ max-width: 1080px; margin: 0 auto; }}
    .eyebrow {{ color: #38bdf8; font-size: .82rem; font-weight: 700; letter-spacing: .12em; text-transform: uppercase; }}
    h1 {{ margin: .35rem 0 .6rem; font-size: 2.4rem; color: #f8fafc; }}
    .lead {{ font-size: 1.05rem; color: #cbd5e1; max-width: 780px; }}
    .pills {{ display: flex; flex-wrap: wrap; gap: .6rem; margin-top: 1.25rem; }}
    .pill {{ display: inline-block; padding: .45rem .9rem; border-radius: 999px; background: #1e293b; border: 1px solid #334155; color: #f8fafc; text-decoration: none; font-size: .88rem; font-weight: 600; }}
    .pill.primary {{ background: #0284c7; border-color: #38bdf8; }}
    main {{ padding: 2rem 1.5rem 4rem; }}
    .grid {{ display: grid; grid-template-columns: repeat(auto-fit, minmax(300px, 1fr)); gap: 1.25rem; margin-top: 1.25rem; }}
    .card {{ background: #111827; border: 1px solid #1f2937; border-radius: 14px; padding: 1.35rem; display: flex; flex-direction: column; justify-content: space-between; }}
    .tag {{ font-size: .72rem; font-weight: 700; color: #38bdf8; letter-spacing: .08em; text-transform: uppercase; }}
    h2 {{ margin: .35rem 0 .5rem; font-size: 1.25rem; color: #f8fafc; }}
    .card p {{ color: #cbd5e1; font-size: .92rem; }}
    .links {{ display: flex; flex-wrap: wrap; gap: .5rem; margin-top: .9rem; }}
    .links a {{ font-size: .84rem; color: #7dd3fc; text-decoration: none; background: #0f172a; border: 1px solid #1e293b; padding: .35rem .65rem; border-radius: 8px; }}
    .note {{ margin-top: 2.2rem; padding: 1rem 1.25rem; border-left: 3px solid #f59e0b; background: #172033; border-radius: 0 10px 10px 0; font-size: .9rem; color: #cbd5e1; }}
    footer {{ border-top: 1px solid #1e293b; padding: 1.5rem; text-align: center; color: #94a3b8; font-size: .85rem; }}
    footer a {{ color: #7dd3fc; text-decoration: none; }}
  </style>
</head>
<body>
  <header>
    <div class="wrap">
      <div class="eyebrow">Lean 4.35.0 · Mathlib v4.35.0 · 6-Kernel Verified · v{version}</div>
      <h1>Pauli Contextuality Lab</h1>
      <p class="lead">Unified, machine-checked research laboratory for spectral bounds on Pauli contextuality, floor-saturating states, Jonah&rsquo;s Conjecture E, exact disjoint Mermin configuration degrees, and finite-horizon sequential contextuality certificates.</p>
      <div class="pills">
        <a class="pill primary" href="blueprint/">Lean 4 Blueprint</a>
        <a class="pill" href="papers/spectral-bounds/unified-contextuality.pdf">Track 1 Paper (PDF)</a>
        <a class="pill" href="papers/disjoint-mermin/contextuality-tensor.pdf">Track 2 Paper (PDF)</a>
        <a class="pill" href="papers/sequential-evidence/whitepaper.pdf">Track 3 Paper (PDF)</a>
        <a class="pill" href="https://github.com/0thernes/pauli-contextuality-lab">GitHub Repository</a>
      </div>
    </div>
  </header>
  <main class="wrap">
    <div class="grid">
      <article class="card">
        <div>
          <div class="tag">Track 1 · lean/HoggarBound/</div>
          <h2>Spectral Bounds, Saturating States &amp; Conjecture E</h2>
          <p>Hoggar/Kramers spectral floor, infinite pure-CCZ determinant family |&Psi;<sub>3m</sub>&rang;, classical N=4,5 exact ladders, exact four-qubit C3 binary optima (368 vs 344, gap 24), and Jonah&rsquo;s Conjecture E across all nine vertex cases for all N &ge; 4.</p>
        </div>
        <div class="links">
          <a href="papers/spectral-bounds/unified-contextuality.pdf">Unified PDF</a>
          <a href="papers/spectral-bounds/unified-contextuality.html">Unified HTML</a>
          <a href="papers/spectral-bounds/c3-spectral-counterexample.pdf">C3 Note PDF</a>
          <a href="c3-lab/">C3 Exact Lab</a>
          <a href="independent-review/">Independent Explorer</a>
          <a href="exports/hyperbolic-quasi-quadric-135/">Quasi-Quadric 135 (Qontextium Export)</a>
        </div>
      </article>

      <article class="card">
        <div>
          <div class="tag">Track 2 · lean/ContextualityTensor/</div>
          <h2>Disjoint Mermin Configurations</h2>
          <p>Exact closed-form contextuality degrees d<sub>k</sub> = (7<sup>k</sup> &minus; 5<sup>k</sup>)/2 for k disjoint Peres&ndash;Mermin squares and (6<sup>k</sup> &minus; 4<sup>k</sup>)/2 for k Mermin pentagrams, answering Section 6 of Muller &amp; Saniga (arXiv:2609.19862v1).</p>
        </div>
        <div class="links">
          <a href="papers/disjoint-mermin/contextuality-tensor.pdf">Paper PDF</a>
          <a href="disjoint-mermin/">4-Qubit Live Lab</a>
        </div>
      </article>

      <article class="card">
        <div>
          <div class="tag">Track 3 · lean/Evidence/</div>
          <h2>Sequential Contextuality Evidence</h2>
          <p>Sharp setting-bias bound for the Peres&ndash;Mermin square, finite adaptive-tree supermartingale wealth bound, and constructive counterexample (97.24% naive vs 0.89% bias-aware false rejection at nominal 1%).</p>
        </div>
        <div class="links">
          <a href="papers/sequential-evidence/whitepaper.pdf">Paper PDF</a>
          <a href="sequential-evidence/">Sequential Lab</a>
        </div>
      </article>
    </div>

    <div class="note">
      <strong>Verification &amp; Epistemic Disclosure:</strong> All manuscripts are unreviewed research preprints by Alexander S. Donahue (independent researcher, Spokane, WA, USA; ORCID <a href="https://orcid.org/0009-0006-8168-9648" style="color:#fcd34d">0009-0006-8168-9648</a>), produced with AI assistance under human direction. Lean 4.35.0 proofs depend strictly on <code>[propext, Classical.choice, Quot.sound]</code>; browser simulations run on classical WebAssembly state-vector code (Moonlab), not quantum hardware.
    </div>
  </main>
  <footer>
    Apache-2.0 (code) &middot; CC-BY-4.0 (manuscripts &amp; docs) &middot;
    <a href="https://github.com/0thernes/pauli-contextuality-lab">Source on GitHub</a> &middot;
    <a href="blueprint/">Lean Blueprint</a>
  </footer>
</body>
</html>
"""


def verify_internal_links(site_root: Path) -> list[tuple[str, str, str]]:
    broken: list[tuple[str, str, str]] = []
    for html_file in sorted(site_root.rglob("*.html")):
        txt = html_file.read_text(encoding="utf-8", errors="ignore")
        for attr, href in re.findall(r'(href|src)="([^"]+)"', txt):
            if href.startswith(("http://", "https://", "mailto:", "#", "data:", "javascript:")):
                continue
            clean = href.split("#", 1)[0].split("?", 1)[0]
            if not clean:
                continue
            if clean.startswith("/pauli-contextuality-lab/"):
                target = site_root / clean[len("/pauli-contextuality-lab/"):]
            elif clean.startswith("/"):
                target = site_root / clean.lstrip("/")
            else:
                target = (html_file.parent / clean).resolve()
            if not target.exists():
                broken.append((html_file.relative_to(site_root).as_posix(), attr, href))
    return broken


def main() -> int:
    SITE.mkdir(parents=True, exist_ok=True)
    (SITE / ".nojekyll").write_text("", encoding="utf-8")
    (SITE / "index.html").write_text(render_portal(), encoding="utf-8")

    copy_if_dir(ROOT / "tracks" / "spectral-bounds" / "web" / "c3-lab", SITE / "c3-lab")
    copy_if_dir(ROOT / "tracks" / "spectral-bounds" / "web" / "independent-review", SITE / "independent-review")
    copy_if_dir(ROOT / "tracks" / "disjoint-mermin" / "web", SITE / "disjoint-mermin")
    copy_if_dir(ROOT / "tracks" / "sequential-evidence" / "web", SITE / "sequential-evidence")
    copy_if_dir(ROOT / "third_party" / "moonlab", SITE / "vendor" / "moonlab")
    copy_if_file(ROOT / "NOTICE", SITE / "vendor" / "NOTICE.md")

    # Mount relative runtime & receipt files expected by Track 2 web lab
    if (SITE / "disjoint-mermin").is_dir():
        copy_if_dir(ROOT / "third_party" / "moonlab", SITE / "disjoint-mermin" / "vendor" / "moonlab")
        copy_if_file(ROOT / "NOTICE", SITE / "disjoint-mermin" / "vendor" / "NOTICE.md")
        copy_if_file(
            ROOT / "tracks" / "disjoint-mermin" / "results" / "stack_report.json",
            SITE / "disjoint-mermin" / "results" / "stack_report.json",
        )

    # Mount referenced Track 1 audit files for c3-lab and independent-review explorers
    for fname in (
        "frontier-c3-lean-audit.md",
        "lean-audit.md",
        "independent_validation.json",
        "stack-independent-audit.md",
        "literature-audit.md",
    ):
        copy_if_file(ROOT / "tracks" / "spectral-bounds" / "results" / fname, SITE / "results" / fname)

    # Mount hyperbolic quasi-quadric 135 / 1,095 / 75 Qontextium export bundle
    exp_src = ROOT / "tracks" / "spectral-bounds" / "results" / "hyperbolic-quasi-quadric-135"
    exp_dst = SITE / "exports" / "hyperbolic-quasi-quadric-135"
    if exp_src.is_dir():
        copy_if_dir(exp_src, exp_dst)
        exp_index = """<!doctype html>
<html lang="en"><head><meta charset="utf-8"/><meta name="viewport" content="width=device-width,initial-scale=1"/>
<title>Hyperbolic Quasi-Quadric in W(7,2) · 135 / 1,095 / 75 Qontextium Export</title>
<style>
body{font-family:system-ui,-apple-system,Segoe UI,Roboto,sans-serif;background:#0b1020;color:#e2e8f0;margin:0;padding:2rem;line-height:1.6}
main{max-width:920px;margin:0 auto}
h1,h2{color:#f8fafc}
a{color:#38bdf8;text-decoration:none}
a:hover{text-decoration:underline}
code,pre{background:#0f172a;border:1px solid #1e293b;border-radius:8px;color:#7dd3fc}
code{padding:.12rem .35rem}
pre{padding:.85rem 1rem;overflow-x:auto}
table{width:100%;border-collapse:collapse;margin:1rem 0;font-size:.92rem}
th,td{border-bottom:1px solid #1e293b;padding:.55rem .7rem;text-align:left}
th{color:#94a3b8;font-weight:700}
</style></head><body><main>
<p><a href="../../">&larr; Back to Pauli Contextuality Lab</a></p>
<h1>Hyperbolic Quasi-Quadric in W(7,2): 135 Observables, 1,095 Contexts, 75 Violated Contexts</h1>
<p>Exact, machine-verified dataset for the four-qubit floor-saturating hyperbolic quasi-quadric S<sub>B</sub> &sub; W(7,2) (<code>data/flat/n4_pivot.txt</code>, kernel-certified in Lean 4 via <code>HoggarBound.pivot_card</code>, <code>HoggarBound.pivot_contexts</code>, and <code>HoggarBound.pivot_degree</code>).</p>
<h2>Direct Download (Qontextium-Ready &amp; Annotated Formats)</h2>
<table>
<thead><tr><th>File</th><th>Format &amp; Contents</th></tr></thead>
<tbody>
<tr><td><a href="qa_hyperbolic_quasi_quadric_135_contexts.txt">qa_hyperbolic_quasi_quadric_135_contexts.txt</a></td><td>All 1,095 contexts (735 positive, 360 negative) in native Qontextium <code>--import assignment</code> format (<code>P1,P2,P3</code>, no header).</td></tr>
<tr><td><a href="qa_hyperbolic_quasi_quadric_135_violated_75.txt">qa_hyperbolic_quasi_quadric_135_violated_75.txt</a></td><td>All 75 violated contexts (15 diagonal abstract-doily + 60 external generator-star lines) in native Qontextium format.</td></tr>
<tr><td><a href="observables_135.txt">observables_135.txt</a></td><td>All 135 four-qubit Pauli observables with optimal &plusmn;1 witness signs, ambient degrees (35 / 23), violated degrees (7 / 1), and diagonal generator anchors.</td></tr>
<tr><td><a href="contexts_1095.csv">contexts_1095.csv</a></td><td>Annotated CSV of all 1,095 commuting triples with operator-product sign, violation flag, and diagonal-subspace incidence count.</td></tr>
<tr><td><a href="violated_75.csv">violated_75.csv</a></td><td>Annotated CSV of all 75 violated triples grouped into the 15 diagonal abstract-doily lines and 15 four-line external generator stars.</td></tr>
<tr><td><a href="hyperbolic_quasi_quadric_135.json">hyperbolic_quasi_quadric_135.json</a></td><td>Complete structured JSON bundle including the ovoid construction from Q<sup>+</sup>(7,2) and explicit Sp(2N,2) witness isomorphism certificates for Q<sup>&minus;</sup>(7,2), W(7,2), and Q<sup>+</sup>(9,2).</td></tr>
</tbody>
</table>
<h2>Qontextium Commands</h2>
<pre>./qontextium --import assignment qa_hyperbolic_quasi_quadric_135_contexts.txt --solver sat --no-interaction
./qontextium --import assignment qa_hyperbolic_quasi_quadric_135_violated_75.txt</pre>
<h2>75 = 15 + 60 Violated-Context Geometry</h2>
<p>The 15 pure-Z observables D<sub>15</sub> &cong; PG(3,2) all pairwise commute (105/105 pairs; all 35 ambient lines are +I), forming a maximal totally isotropic PG(3,2) subspace of W(7,2). Its 15 violated lines form an <em>abstract doily</em> GQ(2,2) as a point-line incidence structure (a symplectic linear line complex inside PG(3,2)), <strong>not</strong> a symplectic four-qubit doily (where collinearity coincides with commutation and an odd number of lines are negative). Alone, those 15 positive lines are noncontextual and are forced into violation by the 120 external observables; all 512 projective odd-imaginary flat states of Proposition 6 violate the exact same 15 diagonal lines. Each of the remaining 60 violated lines (48 +I, 12 &minus;I) meets D<sub>15</sub> in exactly one point p and carries two external observables of violated degree 1 (60 &times; 2 = 120, pairwise disjoint on external points). Through each diagonal point p &isin; D<sub>15</sub> pass exactly 4 external violated lines whose 8 external points share a single nonzero X-support a(p), pairwise commute (28/28 pairs), and together with the 7-point Fano plane p<sup>&perp;</sup><sub>doily</sub> form a maximal totally isotropic PG(3,2) generator G<sub>p</sub> &sub; S<sub>B</sub> in which the 7 violated lines through p are literally the complete 7-line star of p in G<sub>p</sub>.</p>
</main></body></html>
"""
        (exp_dst / "index.html").write_text(exp_index, encoding="utf-8", newline="\n")

    # Copy PDF, HTML, and figure directories for all 3 tracks
    for track in ("spectral-bounds", "disjoint-mermin", "sequential-evidence"):
        src = ROOT / "papers" / track
        dst = SITE / "papers" / track
        if src.is_dir():
            dst.mkdir(parents=True, exist_ok=True)
            for ext in ("*.pdf", "*.html", "*.md"):
                for f in src.glob(ext):
                    shutil.copy2(f, dst / f.name)
            for fig_dir in ("figures", "c3-figures"):
                copy_if_dir(src / fig_dir, dst / fig_dir)

    broken = verify_internal_links(SITE)
    if broken:
        print(f"ERROR: {len(broken)} broken local link(s) in {SITE}:", file=sys.stderr)
        for page, attr, href in broken:
            print(f"  {page}: {attr}={href!r}", file=sys.stderr)
        return 1

    print(f"PASS: Unified Pages site assembled & link-checked (0 broken links) at {SITE}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
