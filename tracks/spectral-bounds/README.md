# Track 1 · Spectral Bounds, Floor-Saturating States & Conjecture E

Consolidates the full codebase and formal proofs of `0thernes/hoggar-bound-lab` (`v1.9.0`) together with the legacy unique Lean witnesses (`TwoQubit.lean`, `Witness.lean`), C11 tabu/exhaustive search programs, ILP verifier, and REVTeX preprint from `0thernes/hoggar-bound` (`v1.0.0`).

## Headline Formal Results (`lean/HoggarBound/`)

- **Spectral floor (real, complex, quaternionic/Kramers):** `hoggar_bound`, `hoggar_bound_quaternionic`, asymptotic $d/L \to 1/2$ limits (`full_space_fraction_tendsto_half`, `hyperbolic_fraction_tendsto_half`, `elliptic_fraction_tendsto_half`).
- **Exact small witnesses:** `mermin_peres` ($d(Q^+(3,2)) = 1$), `doily_contexts` ($W(3,2)$), `degree_three_qubit` ($d(W(5,2)) = 63$), `degree_three_qubit_elliptic` ($d(Q^-(5,2)) = 9$).
- **Saturation theory & infinite non-closed contextual family:** `saturation_tfae`, `saturation_mul_isSquare`, `pivot_degree` ($N=4$, degree 75), `phase5_degree` ($N=5$, degree 480), `det6_degree` ($N=6$, degree 2,016), `phase7_degree` ($N=7$, degree 729,344), and **Theorem 13b** (`infinite_nonclosed_saturated_family`, `infinite_nonclosed_family_contextual`) for the pure-CCZ determinant phase family $|\Psi_{3m}\rangle$ for all $m \ge 1$.
- **Classical $N=4, 5$ exact ladders & unconditional bounds:** Symplectic transvection invariance (`transv_violatedLines_eq`), CSS witnesses (`315, 1575, 6975`), unconditional Kramers-lifted bounds `w72_ge_1455` and `q9plus_ge_6444`, master reduction `exact_degrees_n4_n5_of_q7minus_315`, paired with from-scratch C11 42-orbit census (`src/w52_census_verify.c`) and pure-integer dual verifier (`scripts/exact_degrees_n4_n5.py`).
- **Jonah's Conjecture E (all 9 vertex cases, all $N \ge 4$) & exact C3 binary optima:** Universal cubic-trace formula (`trace_completion_cube_universal`), eigenvalue-multiset theorem across all 9 vertex cases (`jonah_conjecture_e_all_nine_cases_spectra`), signed-Clifford orbit transport, cone lift (`corollary18_c11_from_c3`), and **Theorem 16''** pure-integer MET-SDP exact four-qubit C3 optima `corollary16_exact_binary_optima` (**368 vs 344**, exact gap **24**).
- **Non-vacuity & 6-kernel comparator:** `NonVacuity.lean` + unified `lean/Challenge.lean` / `lean/Solution.lean`.

## Directory Contents

- `src/`: C11 geometry, search, census, QGTL, Eshkol, and Moonlab WASM engines (`hoggar.c`, `w52_census_verify.c`, `third_level.c`, `n9_rank8_search.c`, `family7.c`, `legacy-search/{tabu.c,exhaust.c,geom.h,wcheck.c}`).
- `scripts/`: Exact integer/SymPy verifiers (`c3_exact_optima_check.py`, `c3_sdp_dual_check.py`, `conjecture_e*.py`, `norm_phase_family.py`, `exact_degrees_n4_n5.py`, `flat_states.py`, `phase_states.py`, `ilp_qminus.py`, etc.).
- `web/`: Interactive C3 exact-certificate browser lab (`c3-lab/`) and independent review explorer (`independent-review/`).
- `results/`: Checked JSON receipts and verification logs.
- Paper: [`papers/spectral-bounds/`](../../papers/spectral-bounds/).
