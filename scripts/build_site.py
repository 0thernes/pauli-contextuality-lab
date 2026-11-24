#!/usr/bin/env python3
"""Assemble the single unified GitHub Pages site at build/site/.

Mounts:
  /                       Unified landing portal for all 3 tracks
  /blueprint/             Lean 4.35.0 interactive dependency Blueprint
  /c3-lab/                Track 1 interactive C3 exact-certificate browser lab
  /independent-review/    Track 1 independent review explorer
  /disjoint-mermin/       Track 2 interactive 4-qubit Mermin-square lab
  /sequential-evidence/   Track 3 interactive sequential evidence lab
  /papers/                All 3 research preprints (PDF & HTML)
  /vendor/moonlab/        Single deduplicated Moonlab WASM runtime
"""
from __future__ import annotations

import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SITE = ROOT / "build" / "site"


def copy_if_dir(src: Path, dst: Path) -> None:
    if not src.is_dir():
        return
    if dst.exists():
        shutil.rmtree(dst)
    shutil.copytree(src, dst)


def render_portal() -> str:
    version = (ROOT / "VERSION").read_text(encoding="utf-8").strip()
    return f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8"/>
  <meta name="viewport" content="width=device-width,initial-scale=1"/>
  <title>Pauli Contextuality Lab · v{version}</title>
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
      <div class="eyebrow">Lean 4.35.0 · Mathlib v4.35.0 · Exact Arithmetic · v{version}</div>
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
          <a href="c3-lab/">C3 Exact Lab</a>
          <a href="independent-review/">Independent Explorer</a>
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
      <strong>Verification &amp; Epistemic Disclosure:</strong> All manuscripts are unreviewed research preprints by Alexander S. Donahue (independent researcher, ORCID <a href="https://orcid.org/0009-0006-8168-9648" style="color:#fcd34d">0009-0006-8168-9648</a>), produced with AI assistance under human direction. Lean 4.35.0 proofs depend strictly on <code>[propext, Classical.choice, Quot.sound]</code>; browser simulations run on classical WebAssembly state-vector code (Moonlab), not quantum hardware.
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


def main() -> int:
    SITE.mkdir(parents=True, exist_ok=True)
    (SITE / ".nojekyll").write_text("", encoding="utf-8")
    (SITE / "index.html").write_text(render_portal(), encoding="utf-8")

    copy_if_dir(ROOT / "tracks" / "spectral-bounds" / "web" / "c3-lab", SITE / "c3-lab")
    copy_if_dir(ROOT / "tracks" / "spectral-bounds" / "web" / "independent-review", SITE / "independent-review")
    copy_if_dir(ROOT / "tracks" / "disjoint-mermin" / "web", SITE / "disjoint-mermin")
    copy_if_dir(ROOT / "tracks" / "sequential-evidence" / "web", SITE / "sequential-evidence")
    copy_if_dir(ROOT / "third_party" / "moonlab", SITE / "vendor" / "moonlab")
    # Also mount moonlab inside disjoint-mermin/vendor/moonlab if referenced relatively
    if (SITE / "disjoint-mermin").is_dir():
        copy_if_dir(ROOT / "third_party" / "moonlab", SITE / "disjoint-mermin" / "vendor" / "moonlab")

    # Copy PDF & HTML papers
    for track in ("spectral-bounds", "disjoint-mermin", "sequential-evidence"):
        src = ROOT / "papers" / track
        dst = SITE / "papers" / track
        if src.is_dir():
            dst.mkdir(parents=True, exist_ok=True)
            for ext in ("*.pdf", "*.html"):
                for f in src.glob(ext):
                    shutil.copy2(f, dst / f.name)

    print(f"PASS: Unified Pages site assembled at {SITE}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
