# Changelog

All notable changes to `pauli-contextuality-lab` are documented in this file following [Keep a Changelog](https://keepachangelog.com/en/1.1.0/) and Semantic Versioning.

## [Unreleased]

- External mathematician review and correspondence feedback (M. Saniga, A. Muller, F. Holweck, C. Kelleher, A. Giorgetti).
- Independent clean-machine human replication and line-by-line statement-fidelity sign-off.
- Software Heritage SWHID and Zenodo/HAL DOI registration.

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
