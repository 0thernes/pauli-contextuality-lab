# ADR 0002: Pure-Integer MET-SDP Dual Certificates Inside Lean 4

- **Status:** Accepted (2026-11-24)
- **Context:** Four-qubit case C3 completion optimization (`min_y F(sigma_0, y) = 368` vs `min_y F(sigma_1, y) = 344`) initially relied on floating-point SDP bounds. Floating-point duals cannot be trusted inside a formal kernel without rigorous error enclosures.
- **Decision:** Convert all MET-SDP frustrated-triangle duals (421 and 442 cuts) and the 42-orbit `W(5,2)` duals into exact integer lower-triangular Cholesky + Gershgorin diagonal-dominance certificates checked purely by integer arithmetic inside Lean 4 (`C3ExactOptima.lean`) and independently replayed in exact integer Python (`tracks/spectral-bounds/scripts/c3_exact_optima_check.py`).
- **Consequences:** Zero floating-point trust in the exact optima theorems (`368` and `344`); every Python script using floating-point arithmetic is explicitly audited and labeled `numerical_approximation` in `results/arithmetic-audit.json`.
