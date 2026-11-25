# AGENTS.md

Canonical instructions for every coding agent working in `pauli-contextuality-lab` (Codex, OpenCode, Claude Code, Gemini CLI, Antigravity, Cursor, Grok Build, Grok Bot, and others).
`CLAUDE.md`, `GEMINI.md`, `.cursor/rules/build-standard.mdc`, and `llms.txt` only point here. Edit this file, never the pointers.
Full standard: `docs/build-standard.md` (Build Standard for LLMs v1.2.0, 90 items).

## Project

- **Name:** Pauli Contextuality Lab (`pauli-contextuality-lab`)
- **Purpose:** Unified Lean 4.35.0 (Mathlib v4.35.0) and exact-arithmetic verification repository for three Pauli contextuality research tracks:
  1. `tracks/spectral-bounds/` (`lean/HoggarBound/`): Spectral floor (Hoggar/Kramers bound), floor-saturating states including the infinite pure-CCZ determinant family `|Psi_{3m}>`, classical N=4..5 ladders, exact four-qubit C3 binary optima (`368` vs `344`), and Jonah's Conjecture E across all nine vertex cases for every `N >= 4`.
  2. `tracks/disjoint-mermin/` (`lean/ContextualityTensor/`): Exact contextuality degrees `d_k = (7^k - 5^k)/2` (`k` disjoint Peres-Mermin squares) and `(6^k - 4^k)/2` (`k` Mermin pentagrams), answering Section 6 of Muller & Saniga (`arXiv:2609.19862v1`).
  3. `tracks/sequential-evidence/` (`lean/Evidence/`): Exact finite-tree sequential contextuality evidence bounds and constructive setting-bias attack on the Peres-Mermin square (`97.24%` naive vs `0.89%` corrected false rejection at nominal `1%`).
- **Author:** Alexander S. Donahue (independent researcher, ORCID `0009-0006-8168-9648`, `0_0@0thernes.art`)
- **Licenses:** `Apache-2.0` (`LICENSE`, all code) + `CC-BY-4.0` (`LICENSE-DOCS`, all papers/docs/figures) + MIT for vendored `third_party/` (`NOTICE`)
- **Manifest:** `repo.yaml` (schema: `repo-standard.schema.json`), `formalization.yaml` (Palomar-compatible Lean provenance)
- **Status:** Active research preprints — NOT externally peer reviewed; AI-assisted under human direction.

## Layout

- `lean/`: Single unified Lean 4.35.0 + Mathlib v4.35.0 package (`HoggarBound`, `ContextualityTensor`, `Evidence`, `Challenge`, `Solution`, `VerifyAll`, `comparator.json`).
- `tracks/`: Track-specific C11 engines, Python exact verifiers, interactive browser labs (`web/`), and checked JSON receipts (`results/`).
- `papers/`: Publication manuscripts (`spectral-bounds/`, `disjoint-mermin/`, `sequential-evidence/`), PDFs, LaTeX sources, BibTeX, and correspondence guide.
- `data/`: Witness hex masks, flat-state supports, and `data/MANIFEST.sha256`.
- `third_party/`: Single deduplicated vendored Tsotchke stack (`moonlab/`, `qgtl/`, `quantum_rng/`, `SHA256SUMS.json`).
- `blueprint/`: Lean Blueprint LaTeX (`blueprint/src/content.tex`) + declaration-checked dependency graph builder.
- `scripts/`: Unified verification (`verify_all.py`), Blueprint builder (`build_blueprint.py`), static site builder (`build_site.py`), citation/axiom/arithmetic audits, and Build Standard v1.2.0 auditors (`audit-repo.sh`, `Audit-Repo.ps1`).
- `tests/`: Automated Python (exact, Hypothesis property, negative, mutation/fuzz, integrity) and Node.js test suites.
- `docs/`: Architecture, ADRs, statement-fidelity table, threat model, operations, FAQ, glossary, run log, and 10-pass review logs.

## Commands

Run via `just <recipe>` or `bash scripts/dev.sh <recipe>`:

- `just setup`: Install pinned Python dependencies (`requirements.txt`) and fetch pinned Mathlib cache (`lean/`).
- `just build`: Build all three Lean libraries (`HoggarBound`, `ContextualityTensor`, `Evidence`) and compile C11 verifiers with `-Wall -Wextra`.
- `just test`: Run the unified Python (`pytest`) and Node (`node --test`) verification suites across all 3 tracks.
- `just lint`: Run `ruff`, `mypy`, C compiler warnings, and Batteries `lake exe runLinter` (report-only).
- `just sanitizers`: Compile and execute C11 engines under `-fsanitize=address,undefined`.
- `just verify-lean`: Build Lean modules, run exhaustive `#print axioms` audit (`VerifyAll.lean`), check zero forbidden tokens, and run 6-kernel `lake comparator --config comparator.json --paranoid`.
- `just blueprint`: Validate every `\lean{...}` declaration in `blueprint/src/content.tex` and build the dependency graph.
- `just site`: Assemble the unified GitHub Pages portal (`build/site/`) including all 3 browser labs, papers, and `/blueprint/`.
- `just reproduce`: Clean-clone end-to-end exact verification + audits + blueprint + site assembly.
- `just audit`: Score this repository against Build Standard v1.2.0 (`scripts/audit-repo.sh` / `scripts/Audit-Repo.ps1`).
- `just release X.Y.Z`: Bump `VERSION`, update `CHANGELOG.md`/`CITATION.cff`, tag `vX.Y.Z`, and push straight to `main`.

## Hard Rules (Build Standard v1.2.0)

- **R1.** Nothing may gate, block, or slow a commit or push. No branch protection, no required status checks, no commit/tag signing requirements, no git hooks, no push protection, no merge queues, no coverage/lint/SAST/SBOM gates.
- **R2.** Commit and push straight to `main`. No pull requests and no feature branches.
- **R3.** CI is informational. Failures are findings fixed in follow-up commits to `main`.
- **R4.** Banned tools/files: no Dependabot/Renovate, no PR templates, no CodeRabbit, no Copilot review or `.github/copilot-instructions.md`, no `FUNDING.yml`.
- **R5.** One-person lean, not corporate. Prefer one file over a framework, one command over a checklist.
- **R6.** Never fabricate. Every number, claim, axiom output, badge, and test result must come from a real run of current code.
- **R7.** Classify every finding as exactly one of the 10 classes: `bug`, `error`, `issue`, `problem`, `concern`, `dilemma`, `conflict`, `gap`, `hole`, `blindspot` (definitions in `docs/glossary.md`).
- **R8.** Precedence: Owner's explicit instruction > Hard Rules > Build Standard items > ecosystem conventions.

## Known Traps

- **`lean/Challenge.lean` intentional `sorry` stubs:** `Challenge.lean` contains `sorry` ONLY as the isolated statement-only specification checked against sorry-free `Solution.lean` by `lake comparator --config comparator.json --paranoid`. Never put `sorry`, `admit`, `native_decide`, or custom `axiom` in any proof module or `Solution.lean`.
- **Single GitHub Pages site:** `.github/workflows/pages.yml` deploys `build/site/` assembled by `scripts/build_site.py`, mounting `/blueprint/` alongside all three interactive browser labs and papers. Never add a second Pages workflow.
- **PowerShell bracket safety on Windows:** On the author's ReFS Dev Drive (`Z:\[Vibe Coded (AI)]\...`), always use `-LiteralPath` in PowerShell file cmdlets.
- **Honest affiliation & scope:** Always use `Alexander S. Donahue (independent researcher)` (never assert an unformed LLC). Never claim external peer review, journal acceptance, arXiv submission, or Palomar registration unless genuinely completed.
