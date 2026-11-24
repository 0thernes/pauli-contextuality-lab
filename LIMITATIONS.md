# Limitations, Epistemic Boundaries, and AI-Contribution Disclosure

## 1. Real vs. Metaphor & What Is Not Claimed

- **Not externally peer reviewed:** All three manuscripts in `papers/` are unreviewed research preprints. Passing Lean 4 kernel checks certifies the logical validity of the formalized statements inside Lean — not external referee acceptance, historical priority, or statement-to-literature fidelity.
- **No quantum hardware measurements:** Moonlab (`third_party/moonlab/`) is a classical state-vector simulator compiled to WebAssembly; `quantum_rng` (`third_party/quantum_rng/`) is a seeded classical pseudorandom generator; QGTL (`third_party/qgtl/`) provides classical differential-geometry C kernels. Nothing in this repository is a physical experiment on quantum hardware or certified quantum randomness.
- **Prior work & unreviewed preprint citations:**
  - The spectral floor inequality and Conjecture E stem from unreviewed Zenodo preprints by B. W. Jonah (`doi:10.5281/zenodo.23538829`, `23510634`, `23524332`).
  - Symplectic polar-space degrees and the repeated-disjoint-copy problem come from A. Muller, M. Saniga, F. Holweck, A. Giorgetti, and C. Kelleher (`arXiv:2407.02928`, `arXiv:2609.19862v1`).
  - $d(Q^+(7,2))=315$ is due to Li, Gupta, and Ganesh (`arXiv:2610.26465`); the numerical five-qubit flat state is due to Cieśliński (`arXiv:2610.07172`); the scalar skewness bound is Okumura (1974).
  - Novelty claims (Track 1 Section 5 flat states and $|\Psi_{3m}\rangle$, Track 1 Conjecture E formalization, Track 2 arbitrary-$k$ closed forms) rest on bounded literature searches and do not claim exhaustive historical priority.

## 2. Explicit Kernel Boundary (What Lies Outside Lean 4)

The following items are **not** certified by the Lean 4 kernel and are explicitly tagged as `certificate-checked`, `paper proof`, or `numerical_approximation` in `CLAIMS.md`:

1. **42-orbit `W(5,2)` census (`tracks/spectral-bounds/src/w52_census_verify.c`):** Exhaustive C11 enumeration (17,652,160 classes across 42 orbits) + pure-integer Python duals reproducing Jonah's $(315, 1575, 6975)$. Lean proves the exact master reduction (`exact_degrees_n4_n5_of_q7minus_315`) and unconditional bounds `1455` and `6444`, not the C orbit search itself.
2. **Nine-qubit cyclic-symmetry rank-8 search (`n9_rank8_search.c`):** C11 enumeration of 540,299,769 forms (0 hits).
3. **Single-orbit transitivity input (`Jonah [J3, Theorem B4]`):** Cited paper input for transporting Conjecture E to arbitrary hyperplane classes outside our constructed representatives.
4. **Floating-point scripts:** Every Python file using `numpy` or floating-point arithmetic is automatically classified in `results/arithmetic-audit.json` (`scripts/arithmetic_audit.py`) and never relied upon for a formal proof.
5. **Physical assumptions of Track 3 (`Evidence`):** The finite adaptive-tree theorem assumes a true conditional setting floor $\beta$ and single context-independent value table per trial; no empirical transcript alone can certify those physical assumptions.
6. **Human line-by-line statement fidelity audit:** `formalization.yaml` explicitly records `human_line_by_line_review_recorded: false` until an independent mathematician (or the author line-by-line) signs off on every row of `docs/statement-fidelity.md`.

## 3. AI-Contribution & CRediT Statement

- **Author:** Alexander S. Donahue (independent researcher, ORCID [`0009-0006-8168-9648`](https://orcid.org/0009-0006-8168-9648)). No legal entity or institutional affiliation is claimed.
- **Human contributions (CRediT):** Conceptualization; Methodology; Project administration; Resources (self-funded); Supervision; Validation direction and publication decisions.
- **AI tools used:**
  - **Anthropic Claude:** Initial spectral-floor and saturation studies, Conjecture E paper proofs, disjoint Mermin formulas, sequential evidence proofs and verifiers.
  - **OpenAI Codex:** Independent validation, four-qubit C3 counterexample, manuscript review.
  - **Google Gemini / Antigravity:** Lean 4.35.0 formalizations (Conjecture E all 9 cases, exact C3 optima 368/344, infinite family $|\Psi_{3m}\rangle$, $N=4,5$ ladders, `NonVacuity`, unified monorepo consolidation, Build Standard v1.1.0 & verification stack).
- **Responsibility:** No AI system is listed as an author. Alexander S. Donahue takes full responsibility for all claims, errors, and corrections (`0_0@0thernes.art`).
- **Conflict of interest:** None declared (self-funded independent research).
