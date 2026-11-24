# Architecture

`pauli-contextuality-lab` is organized into four clean layers so that formal proofs, executable verifiers, manuscripts, and web visualizations never tangle or duplicate dependencies:

```text
+-----------------------------------------------------------------------+
|  Layer 4 · Presentation & Publication                                 |
|  papers/ (3 preprints) · blueprint/ (DAG) · scripts/build_site.py     |
+-----------------------------------------------------------------------+
|  Layer 3 · Verification, Audits & Tests                               |
|  tests/ (pytest, Hypothesis, mutation/fuzz, Node) · scripts/*audit*   |
+-----------------------------------------------------------------------+
|  Layer 2 · Three Modular Research Tracks + Deduplicated Stack         |
|  tracks/spectral-bounds/ · tracks/disjoint-mermin/ ·                  |
|  tracks/sequential-evidence/ · data/ · third_party/ (Moonlab/QGTL/QR) |
+-----------------------------------------------------------------------+
|  Layer 1 · Single Unified Lean 4.35.0 + Mathlib v4.35.0 Kernel Core   |
|  lean/HoggarBound · lean/ContextualityTensor · lean/Evidence          |
|  lean/Challenge.lean <-> lean/Solution.lean (6-kernel comparator)     |
+-----------------------------------------------------------------------+
```

## Key Invariants

1. **Single Lean toolchain & Mathlib pin:** `lean/lean-toolchain` (`leanprover/lean4:v4.35.0`) and `lean/lake-manifest.json` (`mathlib` `56a005855ea1`, `batteries` `66e469188fe0`) serve all three formal libraries without cache duplication.
2. **Single vendored simulator stack:** `third_party/` holds exactly one SHA-256-pinned copy of Moonlab (`moonlab.wasm`), QGTL differential geometry kernels, and `quantum_rng` (previously duplicated four times).
3. **Strict kernel vs. computation boundary:** Every headline mathematical claim in `CLAIMS.md` is explicitly tagged (`kernel-checked`, `certificate-checked`, `paper proof`, `numerical_approximation`, or `open`).
4. **Zero-gate CI (Build Standard R1-R3):** All four GitHub Actions workflows (`ci.yml`, `lean-verify.yml`, `pages.yml`, `release.yml`) run on pushes/tags to `main` and report findings without branch protection or merge gates.
