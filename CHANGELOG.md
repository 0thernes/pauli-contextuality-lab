# Changelog

All notable changes to `pauli-contextuality-lab` are documented in this file following [Keep a Changelog](https://keepachangelog.com/en/1.1.0/) and Semantic Versioning.

## [Unreleased]

- External mathematician review and correspondence feedback (M. Saniga, A. Muller, F. Holweck, C. Kelleher, A. Giorgetti).
- Independent clean-machine human replication and line-by-line statement-fidelity sign-off.
- Software Heritage SWHID and Zenodo/HAL DOI registration.

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
