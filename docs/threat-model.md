# Threat Model

As a formal-verification and computational-mathematics repository, the primary threats are **epistemic and verification-integrity failures** rather than network intrusion.

| Threat Vector | Concrete Risk | Mitigation in This Repo |
|---|---|---|
| **Statement weakening / vacuity** | An AI-assisted Lean proof type-checks a weaker or vacuously true theorem than the paper claims. | Isolated `lean/Challenge.lean` checked against `lean/Solution.lean`; explicit `NonVacuity.lean` witnesses; line-by-line `docs/statement-fidelity.md`. |
| **Hidden axioms / `native_decide`** | Soundness bypass via `sorryAx`, custom `axiom`, `@[extern]`, or compiler-trusted evaluation. | Zero-forbidden-token CI scan; exhaustive `VerifyAll.lean` `#print axioms` checked against `[propext, Classical.choice, Quot.sound]`; verbatim output synced to `README.md`. |
| **Single-kernel soundness bug** | A bug in Lean's official C++ kernel (e.g. #14576) accepts an invalid proof. | `lake comparator --config comparator.json --paranoid` runs independent checkers (`leanchecker`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`) in CI. |
| **Floating-point illusion** | Floating-point tolerances mask a non-rigorous bound. | Exact integer/rational certificates for every theorem (`C3ExactOptima.lean`, exact Python integer/SymPy scripts); automated `scripts/arithmetic_audit.py` explicitly labels every floating-point script `numerical_approximation`. |
| **C memory unsafety / UB** | Undefined behavior in C11 census/search engines corrupts counts. | Compiled with `-Wall -Wextra -Werror` and tested under `-fsanitize=address,undefined` in CI; every census result cross-checked by independent Python/Lean verifiers. |
| **Citation hallucination** | Fabricated or broken DOI / arXiv / Zenodo reference. | Automated `scripts/check_citations.py` verifies citation identifiers across all three manuscripts. |
| **Artifact tampering** | Silent drift in datasets, vendored WASM, or release PDFs. | `data/MANIFEST.sha256`, `third_party/SHA256SUMS.json`, tag-triggered `SHA256SUMS`, and GitHub Sigstore SLSA attestations (`actions/attest-build-provenance`). |
