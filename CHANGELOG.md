# Changelog

All notable changes to `pauli-contextuality-lab` are documented in this file following [Keep a Changelog](https://keepachangelog.com/en/1.1.0/) and Semantic Versioning.

## [Unreleased]

- External mathematician review and correspondence feedback (M. Saniga, A. Muller, F. Holweck, C. Kelleher, A. Giorgetti).
- Independent clean-machine human replication and line-by-line statement-fidelity sign-off.
- Software Heritage SWHID and Zenodo/HAL DOI registration.

## [2.5.0] — 2026-11-24

### Pass 6 TOC Deep-Dive Hardening (Zero-Warning C11, Full Manuscript Path Sync, Active Web Explorer & Workflow Guards)

- **Zero C11 Compiler Warnings (`-Wall -Wextra`):** Eliminated all 5 compiler warnings in `tracks/spectral-bounds/src/legacy-search/{wcheck.c,geom.h}` (`-Wcomment` nested `/*` inside comment and `-Wunused-function` via `static inline`), achieving zero warnings across all 8 ASan/UBSan C11 engines.
- **Complete Post-Consolidation Manuscript & Live HTML Path Synchronization:** Replaced 163 pre-consolidation Track 1 paths across both `papers/spectral-bounds/unified-contextuality.md` and live GitHub Pages `unified-contextuality.html`, fixed all remaining pre-consolidation script/result paths and historical `hoggar-bound-lab` receipt qualifiers across `unified-contextuality.tex` (plus clickable `mailto:` and live consolidated CI links in Section 9.4), `c3-spectral-counterexample.tex` (plus fixing a grammatical affiliation typo in Section 8 and stale test command in Section 9), `contextuality-tensor.md`, `revtex-v1/main.tex`, `tracks/spectral-bounds/web/c3-lab/README.md`, and the 6 legacy paper-build scripts under `tracks/{spectral-bounds,disjoint-mermin}/scripts/`. Recompiled all 4 PDFs with Tectonic (0 overfull hboxes ≥ 5 pt).
- **Interactive Web Apps & Active Explorer (`/independent-review/`) Upgrade:** Normalized `tracks/spectral-bounds/web/independent-review/data.js` from CRLF to LF; upgraded `independent-review/{index.html,explorer.js}` so every displayed `LEAN THEOREM` links directly to its exact verified line in `lean/HoggarBound/*.lean#L...` on GitHub alongside a direct `/blueprint/` link; updated `c3-lab/index.html` to reflect the all-$N \ge 4$ Lean 4 Conjecture E formalization; and added unified Lab Hub (`../`) and `/blueprint/` navigation links across `tracks/disjoint-mermin/web/index.html` and `tracks/sequential-evidence/web/index.html`.
- **Zero Python Bugbear (`B`) Findings, CRLF Web Guard & CI Concurrency:** Fixed late-binding loop-variable closures (`B023`) in `tracks/spectral-bounds/scripts/{fix_github_math,phase_states}.py` and unused loop variables (`B007`) across `tracks/spectral-bounds/scripts/`; added `concurrency:` cancellation groups to `.github/workflows/{ci,lean-verify}.yml`; and expanded `tests/test_repo_integrity.py` to enforce LF line endings on `.js`/`.mjs`/`.css`/`.html` and verify every `independent-review/explorer.js` theorem `#L` source link against `lean/HoggarBound/*.lean`.

## [2.4.0] — 2026-11-24

### Pass 5 TOC Deep-Dive Hardening (Post-Consolidation Runtime Fixes, Blueprint UX, Web QA & C11)

- **Post-Consolidation Track Script & Monorepo Stack Runner Fixes:** Fixed 12 consolidated track scripts and Node/WASM drivers (`tracks/sequential-evidence/scripts/make_figures.py`, `tracks/spectral-bounds/scripts/{stack_audit,phase_seven_lean,flat_states,phase_states,frontier_c3_axioms,frontier_c3_certificate_audit,analysis,independent_demo_data}.py`, `build.sh`, `src/{moonlab_experiment,moonlab_saturated}.mjs`) so references to shared `third_party/`, `data/`, `lean/`, and `papers/` resolve dynamically via `REPO_ROOT` (with standalone fallback), and added `scripts/run_track_stack.py` to stage isolated native Tsotchke stack runs across all three tracks while keeping the SHA-256-fingerprinted Track 2 & Track 3 `run_stack.py` / `stack_moonlab.mjs` sources byte-identical to their recorded `stack_report.json` provenance receipts.
- **Interactive Lean 4 Blueprint Upgrade (`/blueprint/`):** Upgraded `scripts/build_blueprint.py` so every one of the **140 statically verified Lean declarations** links directly to its exact file and line on GitHub (`.../blob/main/lean/...#L<line>`), added interactive hover/click transitive **dependency-cone highlighting** (upstream prerequisites in amber, downstream corollaries/targets in green) across both the SVG DAG and theorem cards, and added an instant live search filter.
- **Live Browser QA & HTML Paper Fixes:** Fixed broken space-corrupted GitHub tag URLs, stale `<meta>`/`canonical` tags, and double-replaced version strings in `papers/spectral-bounds/unified-contextuality.html`; fixed the `<select id="profile">` caret-wrapping CSS glitch in `tracks/spectral-bounds/web/independent-review/style.css`; updated track branding links in `independent-review/` and `c3-lab/`; updated `papers/sequential-evidence/STATUS.md`; fixed Abstract nested parentheses in `unified-contextuality.tex` and header line-wrapping in `c3-spectral-counterexample.tex`; and recompiled all 4 PDFs with zero overfull hboxes ≥ 5 pt.
- **C11 Memory Hygiene & Expanded ASan/UBSan Coverage:** Added `geom_free()` and complete cleanup across `tracks/spectral-bounds/src/legacy-search/{geom.h,wcheck.c,exhaust.c,tabu.c}`, added OOM checks in `third_level.c`, and expanded `.github/workflows/ci.yml` to compile and execute `wcheck`, `exhaust`, `qgt_hoggar`, and `stack_qrng` under `-Wall -Wextra -fsanitize=address,undefined`.
- **Regression Guards (`tests/test_repo_integrity.py`):** Added automated checks enforcing `README.md` version badge and `unified-metadata.json` version sync, zero malformed/space-corrupted tag URLs in `papers/`, live execution of `phase_seven_lean.py` / `frontier_c3_certificate_audit.py` path resolution, and exact GitHub `#L` links in `blueprint.json`.

## [2.3.0] — 2026-11-24

### Pass 4 TOC Deep-Dive Hardening (Manuscripts, Lean, CI, C11, Site, & Security)

- **Lean 4.35.0 & `HoggarBound.CarrierFamily` Integration:** Added `HoggarBound.CarrierFamily` (2,522 lines, proving Theorem 17 `HoggarBound.C3AllQubits.c3_strict_law_fails_general` and `c3_all_qubits_completion`) directly into `lean/VerifyAll.lean` and `.github/workflows/lean-verify.yml`, expanding our exhaustive `Lean.collectAxioms` audit from **1,920 → 2,206 theorems** (and **158 → 160 explicit `#print axioms`**) with strictly standard axioms `[propext, Classical.choice, Quot.sound]`, and expanding the interactive SVG DAG Blueprint to **24 nodes / 140 statically verified Lean declarations**.
- **Zero-Overflow LaTeX Typesetting across ALL 4 Pauli PDFs:** Fixed a **257.18 pt** Figure 1 right-margin overflow in Track 3 `whitepaper.pdf` (`\pandocbounded` scaling), a **35.67 pt** overflow in Track 2 `contextuality-tensor.pdf`, and all **6** overfull hboxes (up to 38.64 pt) in Track 1 `unified-contextuality.pdf`. All 4 PDFs now compile via Tectonic with **0 overfull hboxes ≥ 5 pt**, 0 undefined refs/cites, and 0 missing glyphs.
- **Companion C3 PDF Scrubbed & Recompiled:** Imported and cleaned `papers/spectral-bounds/c3-spectral-counterexample.tex` (removing the last `0thernes LLC` / `Hoggar Bound Lab` branding and adding ORCID + CC-BY-4.0 metadata) and recompiled `c3-spectral-counterexample.pdf` (`0` overfull hboxes ≥ 5 pt), now also attached to GitHub Releases.
- **100% Live-Verified Paths, Reproduction Commands & Semantic Citations:** Fixed all remaining pre-consolidation reproduction commands and paths across Track 1 `unified-contextuality.tex/.html/.md`, Track 2 `contextuality-tensor.tex/.md`, Track 3 `whitepaper.tex/.md`, `papers/disjoint-mermin/STATUS.md`, `ARXIV-SOURCE.md`, `tracks/spectral-bounds/web/independent-review/README.md`, `render_paper.mjs`, `unified-citation.bib`, and `unified-metadata.json` (**14 broken local Markdown links → 0**). Live semantic API verification confirmed **69/69** citations (43 arXiv + 19 Crossref DOIs + 6 DataCite/Zenodo DOIs across both repos) match real authors, titles, and years.
- **CI, C11, Python & Security Hardening:** Added `set -o pipefail`, a character-level nested-comment & string-aware Lean forbidden-token lexer, and live `results/lean-axioms-ci.log` verification (`--require-exhaustive`) to `lean-verify.yml`; added explicit `timeout-minutes:` to all workflows; fixed heap leaks & null checks in `tracks/spectral-bounds/src/orbits7.c` and added `orbits7` ASan/UBSan compilation to `ci.yml`; fixed `.NET CurrentDirectory` bug in `scripts/Audit-Repo.ps1`; normalized 5 CRLF `.lean` files to LF; fixed `.gitleaks.toml` with `regexTarget = "line"`; fixed Python `B020`/`F401`/`ISC004` findings; and expanded `tests/test_repo_integrity.py` with case-exact Markdown link, CRLF, `lakefile.toml` version, and legacy-licence regression gates.

## [2.2.0] - 2026-11-24

### Added & Upgraded
- **Interactive 24-node SVG DAG Lean Blueprint (`blueprint/src/content.tex` + `scripts/build_blueprint.py`):** expanded from 13 nodes / 48 refs to **24 formal nodes & 138 statically verified Lean declarations** across Tracks 1–3 and the 12-target 6-kernel Comparator Bridge, rendered as an interactive, track-filterable SVG dependency graph with clickable jump-to-card nodes at `/blueprint/`.
- **Publication-grade Track 3 PDF (`papers/sequential-evidence/whitepaper.tex` + `whitepaper.pdf`):** compiled via Pandoc + Tectonic with proper PDF Author/Title metadata, ORCID, independent-researcher affiliation, `CC-BY-4.0` license, and canonical `pauli-contextuality-lab` links.
- **Expanded integrity regression tests (`tests/test_repo_integrity.py`):** automatically enforce live repo-path existence across all root docs, live Lean declaration resolution across `README.md`/`CLAIMS.md`/`docs/statement-fidelity.md`, zero legacy LLC strings in active docs/papers, and full single-version consistency.

### Fixed
- **Track 1 Flagship Paper Appendix A (`papers/spectral-bounds/unified-contextuality.tex` & `.pdf`):** replaced all six pre-consolidation reproduction commands (`VerifyNewFormalizations.lean`, `HoggarBound.Solution`, `SaturatedVerification.lean`, `scripts/c3_exact_optima_check.py`, `frontier_c3_browser_test.cjs`) with live, verified `pauli-contextuality-lab` commands (`VerifyAll.lean`, `lake comparator --paranoid`, `scripts/verify_all.py`, `tracks/spectral-bounds/scripts/...`) and updated Section 9.4 with the 1,920-theorem / 6-kernel verification record.
- Fixed dead path in `CLAIMS.md` (`results/n9_rank8_search.tsv` → `tracks/spectral-bounds/results/n9_rank8_search.tsv`), documented Track 2 exact $\mathbb{Z}$-evenness and Track 2/3 non-vacuity in `docs/statement-fidelity.md`, and verified all 20 arXiv IDs & 23 DOIs live online (`scripts/check_citations.py --online`, 43/43 HTTP 200).

## [2.1.0] - 2026-11-24

### Added
- **Exhaustive Lean axiom metaprogram + 158 explicit `#print axioms` declarations** in `lean/VerifyAll.lean`, auditing 100% of historical Track 1 (`VerifyNewFormalizations.lean`, 110 decls + 6 baseline/legacy), Track 2 (`Verification.lean`, 16 decls), Track 3 (`Evidence`, 14 decls), and the 12 `ComparatorTarget` bridges, plus an automatic `Lean.collectAxioms` check over all **1,920 theorems** across `HoggarBound`, `ContextualityTensor`, `Evidence`, and `PauliContextualityLab`.
- **Automated Pages internal link & figure checker** embedded directly in `scripts/build_site.py` and executed on every CI push (`0` broken links/images).
- Surgical `.gitleaks.toml` allowlist extending defaults strictly for Lean proof-term `have key :=` bindings in `lean/` (zero false-positive leak alerts).

### Fixed
- **21 broken local links & missing figures on the unified GitHub Pages site:** mounted `papers/*/figures/`, `papers/spectral-bounds/c3-figures/`, `results/*` audit reports, and `vendor/NOTICE.md`, and fixed relative paths and archived repository URLs across `c3-lab/`, `independent-review/`, `disjoint-mermin/`, `sequential-evidence/`, and `unified-contextuality.html`.
- **C11 heap memory leaks across all `hoggar.c` subcommands** (`cmd_table`, `cmd_verify`, `cmd_search`, `cmd_falsify`, `cmd_exhaust2`, `cmd_lines`) and expanded CI ASan/UBSan execution to run `hoggar_san table/exhaust2/lines/falsify/verify` plus `./build/san/third_level_san`.
- **Zero-warning static analysis:** resolved all 3 `mypy` annotations in `scripts/build_blueprint.py` (`0` ruff errors, `0` mypy errors across all `scripts/`), and added all missing docstrings + `@[nolint unusedArguments]` across `ContextualityTensor.lean` and `Evidence/` (`0` Batteries `runLinter` errors).
- **Security & manuscript hygiene:** bumped `pytest==9.0.3` (closing CVE-2025-71176), recompiled Track 1 (`unified-contextuality.pdf`) and Track 2 (`contextuality-tensor.pdf`) cleanly via Tectonic under `Independent researcher, Spokane, WA, USA` and `CC-BY-4.0`, and cleaned remaining legacy affiliation references in Track 3 `whitepaper.md` and build scripts.

## [2.0.0] - 2026-11-24

### Added
- **Unified three-track repository architecture** consolidating four earlier standalone Pauli contextuality repositories (`0thernes/hoggar-bound-lab`, `0thernes/hoggar-bound`, `0thernes/contextuality-tensor-lab`, `0thernes/contextuality-evidence-lab`) into a single Lean 4.35.0 + Mathlib `v4.35.0` workspace (`lean/`) and modular `tracks/` + `papers/` layout.
- **Legacy witness integration:** Ported `HoggarBound/Witness.lean` (`d(W(5,2)) = 63`, `d(Q^-(5,2)) = 9`) and `HoggarBound/TwoQubit.lean` (`mermin_peres`, `doily_contexts`) from `hoggar-bound` onto `HoggarBound.Kramers`, alongside `tracks/spectral-bounds/src/legacy-search/` (`tabu.c`, `exhaust.c`) and `papers/spectral-bounds/revtex-v1/`.
- **Unified 12-target isolated Challenge/Solution comparator** (`lean/Challenge.lean`, `lean/Solution.lean`, `lean/comparator.json`) spanning all three tracks for 6-kernel `lake comparator --paranoid`.
- **Unified exhaustive axiom audit (`lean/VerifyAll.lean`)** with automated README verbatim sync (`scripts/check_readme_axioms.py`).
- **Build Standard for LLMs v1.1.0 & Defensible Playbook v1.1 verification stack:** `repo.yaml`, `formalization.yaml`, `AGENTS.md`/`CLAUDE.md`/`GEMINI.md`/`.cursor/rules/build-standard.mdc`/`llms.txt`, `CLAIMS.md`, `LIMITATIONS.md`, `REPLICATION.md`, `ROADMAP.md`, `docs/statement-fidelity.md`, `docs/adr/0001..0004`, `blueprint/src/content.tex` + `scripts/build_blueprint.py`, `scripts/arithmetic_audit.py`, `scripts/check_citations.py`, `data/MANIFEST.sha256`, cross-platform CI + C11 ASan/UBSan + Hypothesis property + mutation/fuzz tests, unified GitHub Pages portal (`scripts/build_site.py`), and SLSA provenance release workflow.

### Changed
- **Open dual licensing:** Replaced legacy verification-only ("All rights reserved") license with `Apache-2.0` (`LICENSE`, all code) + `CC-BY-4.0` (`LICENSE-DOCS`, all manuscripts, figures, and documentation), preserving MIT licenses for deduplicated `third_party/` (`NOTICE`).
- **Accurate author attribution:** Standardized author metadata to `Alexander S. Donahue (independent researcher, ORCID 0009-0006-8168-9648)`, removing premature unformed LLC assertions.
- **Deduplicated `third_party/`:** Collapsed four identical copies of Moonlab WASM, QGTL kernels, and `quantum_rng` into a single SHA-256-pinned root `third_party/` directory.

### Lineage (Superseded Archived Repositories)
- `0thernes/hoggar-bound-lab` (`v0.1.0`–`v1.9.0`, Nov 9–24, 2026) → Track 1 (`tracks/spectral-bounds/`, `lean/HoggarBound/`)
- `0thernes/hoggar-bound` (`v1.0.0`, Nov 9, 2026) → Merged into Track 1 (`Witness.lean`, `TwoQubit.lean`, `legacy-search/`, `revtex-v1/`)
- `0thernes/contextuality-tensor-lab` (`v0.1.0`, Nov 10, 2026) → Track 2 (`tracks/disjoint-mermin/`, `lean/ContextualityTensor/`)
- `0thernes/contextuality-evidence-lab` (`v1.0.0`, Nov 10, 2026) → Track 3 (`tracks/sequential-evidence/`, `lean/Evidence/`)
