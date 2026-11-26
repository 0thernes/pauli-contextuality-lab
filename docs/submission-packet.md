# Ready-to-Send Submission & Correspondence Dossier (`docs/submission-packet.md`)

> **Status:** Draft preparation packet awaiting human author review, line-by-line fidelity sign-off, and manual submission. Nothing in this file has been transmitted or submitted by any automated script.

## 1. Palomar Registry Draft Payload (`formalization.yaml`)

- **Repository:** `https://github.com/0thernes/pauli-contextuality-lab`
- **Lean toolchain:** `leanprover/lean4:v4.35.0` (`Mathlib v4.35.0`, rev `56a005855ea1`)
- **Challenge / Solution / Config:** `lean/Challenge.lean`, `lean/Solution.lean`, `lean/comparator.json`
- **6-kernel comparator command:** `cd lean && lake exe cache get && lake build HoggarBound ContextualityTensor Evidence Solution VerifyAll && lake env lean VerifyAll.lean && lake comparator --config comparator.json --paranoid`
- **12 cross-track targets verified across all 6 independent kernels (`lean-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`, `lean-default`):**
  - Track 1 (`HoggarBound`): spectral floor, Kramers floor, saturation integrality `(2^N - 1)|S| = □`, infinite non-closed pure-CCZ family `|Ψ_{3m}⟩`, exact four-qubit $C_3$ binary optima (`368` vs. `344`), Jonah's Conjecture E across all 9 vertex cases ($N \ge 4$), unconditional $d(W(7,2)) \ge 1455$ & $d(Q^+(9,2)) \ge 6444$.
  - Track 2 (`ContextualityTensor`): exact disjoint-copy formulas `(7^k - 5^k)/2` (squares) and `(6^k - 4^k)/2` (pentagrams).
  - Track 3 (`Evidence`): Peres–Mermin sharp setting-bias bound $1 - \beta$ and finite adaptive-tree supermartingale hitting bound.
- **Permanent Software Heritage snapshot:** `swh:1:snp:0d84f85d8dc6b9c703784c655998864acee6c98d` (`v2.9.0`; updated snapshot recorded in `0thernes-research-archive` after `v3.0.0`).

## 2. Human Line-by-Line Statement Fidelity Sign-Off Checklist (Playbook v1.3)

Before flipping `human_line_by_line_review_recorded: false` → `true` in `formalization.yaml`, the author reviews and initials each row of `docs/statement-fidelity.md`:

- [ ] Track 1 definitions (`HoggarBound/Pauli.lean`, `Bound.lean`, `Quadric.lean`, `ConjectureECore.lean`, `NormPhaseFamily.lean`) match Sections 2–9 of `papers/spectral-bounds/unified-contextuality.pdf`.
- [ ] Track 2 definitions (`ContextualityTensor/ActualModel.lean`, `PhysicalBridge.lean`) match Muller & Saniga (`arXiv:2609.19862v1` Def. 11–13 & Sec. 6) and `papers/disjoint-mermin/contextuality-tensor.pdf`.
- [ ] Track 3 definitions (`Evidence/Square.lean`, `Sequential.lean`, `Physical.lean`) match `papers/sequential-evidence/whitepaper.pdf`.
- [ ] `lean/Challenge.lean` (12 isolated targets) and `lean/HoggarBound/NonVacuity.lean` (10 existential witnesses) contain zero vacuous hypotheses or definition drift.
- [ ] `ERRATA.md`, `LIMITATIONS.md`, and `CLAIMS.md` accurately delineate Lean-proved vs. C-census vs. simulation results.

## 3. Suggested Specialist Correspondence List (Draft Outreach Notes)

- **Metod Saniga & Axel Muller / Frédéric Holweck / Alain Giorgetti / Colm Kelleher:** Share Track 1 (`unified-contextuality.pdf`, explicit $Sp(2N,2)$ witness isomorphisms matching `[M2]` and Qontextium-ready hyperbolic quasi-quadric `135/1,095/75` exports at `/exports/hyperbolic-quasi-quadric-135/`) and Track 2 (`contextuality-tensor.pdf`, exact arbitrary-$k$ disjoint-copy formulas addressing Muller & Saniga `arXiv:2609.19862v1` Sec. 6).
- **B. W. Jonah:** Share Lean 4.35.0 formalization of the spectral floor, Kramers floor, saturation theory, exact $C_3$ binary optima (`368` vs. `344`), and all-nine-case proof of Conjecture E (`N ≥ 4`) with explicit credit throughout.
- **Lean / Mathlib Community:** Candidate small hand-reviewed Mathlib PRs under `Apache-2.0` (only after human author review & handwritten prose): finite-field quadratic forms / symplectic transvections and exact integer third-moment inequalities.
