# ADR 0003: Six-Layer Verification Stack and Single-Site Lean Blueprint

- **Status:** Accepted (2026-11-24)
- **Context:** Single-kernel Lean builds are susceptible to statement-weakening bugs, vacuous hypotheses, and rare kernel soundness bugs (such as Lean bug #14576). In addition, deploying a separate `leanblueprint` Pages workflow collides with an existing GitHub Pages site.
- **Decision:** Pair every Lean library with: (1) explicit `NonVacuity` witness lemmas, (2) an isolated `Challenge.lean` / `Solution.lean` pair audited by 6-kernel `lake comparator --paranoid`, (3) verbatim `#print axioms` output verified in CI against `README.md`, (4) Batteries `runLinter`, (5) exact non-Lean arithmetic + Hypothesis/mutation/fuzz + C11 ASan/UBSan checks, and (6) a declaration-checked Lean Blueprint mounted under `/blueprint/` inside the single unified GitHub Pages build (`scripts/build_site.py`).
- **Consequences:** Mathematicians can inspect the theorem dependency DAG and exact axioms in five seconds without cloning Mathlib, while CI never fights over GitHub Pages ownership.
