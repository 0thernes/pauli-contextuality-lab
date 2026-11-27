# Ready-to-Send Submission & Correspondence Dossier (`docs/submission-packet.md`)

> **Status:** Draft preparation packet awaiting human author review, line-by-line fidelity sign-off, and manual submission. Nothing in this file has been transmitted or submitted by any automated script.

## 1. Palomar Registry Draft Payload (`formalization.yaml`)

- **Repository:** `https://github.com/0thernes/pauli-contextuality-lab`
- **Lean toolchain:** `leanprover/lean4:v4.35.0` (`Mathlib v4.35.0`, rev `56a005855ea1`)
- **Palomar `module` header status (Playbook v1.3 Part D #3):** Partial (`5/64` `.lean` files — `Evidence/*` — currently carry `module`; `HoggarBound/*`, `ContextualityTensor/*`, `Challenge.lean`, and `Solution.lean` are tracked on `ROADMAP.md` for Lean 4.35 `module` migration prior to Palomar Registry submission).
- **Challenge / Solution / Config:** `lean/Challenge.lean`, `lean/Solution.lean`, `lean/comparator.json`
- **6-kernel comparator command:** `cd lean && lake exe cache get && lake build HoggarBound ContextualityTensor Evidence Solution VerifyAll && lake env lean VerifyAll.lean && lake comparator --config comparator.json --paranoid`
- **18 cross-track comparator targets (`lean/comparator.json`) accepted by 6 independent kernels (`lean-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`, `lean-default`); other theorems are checked by the standard Lean kernel only:**
  - Track 1 (`HoggarBound`): Jonah's spectral floor and Kramers floor (formalized prior work), saturation integrality `(2^N - 1)|S| = □`, infinite non-closed pure-CCZ family `|Ψ_{3m}⟩` attaining the floor, binary optima (`368`, `344`) for one four-qubit $C_3$ sign pair, strict-law failure for one representative of each of the 9 vertex cases of Jonah's Conjecture E ($N \ge 4$; formal vertex-case membership in `ConjectureECases.lean`; whole-case transfer via Theorem B4 outside Lean), lower bounds $d(W(7,2)) \ge 1455$ & $d(Q^+(9,2)) \ge 6444$ (Jonah earlier claimed the exact values `1575`, `6975`).
  - Track 2 (`ContextualityTensor`): exact disjoint-copy formulas `(7^k - 5^k)/2` (squares) and `(6^k - 4^k)/2` (pentagrams) in BOTH the tuple-indexed model (Targets 9–10) AND the actual vertex-subset model (Targets 13–14), plus genuine minimum-defined limit theorems `actual_*_min_epsilon_tends_to_one` (Targets 15–16).
  - Track 3 (`Evidence`): Peres–Mermin sharp setting-bias bound $1 - \beta$ and finite adaptive-tree supermartingale hitting bound (formalized elementary bounds, Targets 11–12).
  - Kernel-Proved Perturbed-Bound Refutations: `target_refute_w52_bound_64` and `target_refute_c3_signA_bound_369` (Targets 17–18).
- **Permanent Software Heritage snapshot:** `swh:1:snp:bcb2b33b31015225ace11d52fa98b2f93c5b4913` (`v3.1.0`; refreshed via Save Code Now on each release).
- **DOI fallback note (Playbook v1.3 H13):** Confirm Zenodo generative-AI depositor eligibility before depositing; if Zenodo declines, use **OSF Preprints** (moderated, DOI on acceptance). Do not deposit to HAL until a formal affiliation exists.
- **Export-control self-screen (Playbook v1.3 #37):** Pure quantum-foundations mathematics / finite symplectic geometry (`15 CFR 734.8` published fundamental research); no controlled cryptographic, defense, or dual-use implementation. Consult counsel if any doubt arises prior to commercial use.

## 2. Human Line-by-Line Statement Fidelity Sign-Off Checklist (Playbook v1.3)

Before flipping `human_line_by_line_review_recorded: false` → `true` in `formalization.yaml`, the author reviews and initials each row of `docs/statement-fidelity.md`:

- [ ] Track 1 definitions (`HoggarBound/Pauli.lean`, `Bound.lean`, `Quadric.lean`, `ConjectureECore.lean`, `NormPhaseFamily.lean`) match Sections 2–9 of `papers/spectral-bounds/unified-contextuality.pdf`.
- [ ] Track 2 definitions (`ContextualityTensor/ActualModel.lean`, `PhysicalBridge.lean`) match Muller & Saniga (`arXiv:2609.19862v1` Def. 11–13 & Sec. 6) and `papers/disjoint-mermin/contextuality-tensor.pdf`.
- [ ] Track 3 definitions (`Evidence/Square.lean`, `Sequential.lean`, `Physical.lean`) match `papers/sequential-evidence/whitepaper.pdf`.
- [ ] `lean/Challenge.lean` (18 isolated targets) and `lean/HoggarBound/NonVacuity.lean` (10 existential witnesses + 8 perturbed-bound refutations) contain zero vacuous hypotheses or definition drift.
- [ ] `ERRATA.md`, `LIMITATIONS.md`, and `CLAIMS.md` accurately delineate Lean-proved vs. C-census vs. simulation results.

## 3. Suggested Specialist Correspondence List (Draft Outreach Notes)

- **Metod Saniga & Axel Muller / Frédéric Holweck / Alain Giorgetti / Colm Kelleher:** Share Track 1 (`unified-contextuality.pdf`, explicit $Sp(2N,2)$ witness isomorphisms matching `[M2]` and Qontextium-ready hyperbolic quasi-quadric `135/1,095/75` exports at `/exports/hyperbolic-quasi-quadric-135/`) and Track 2 (`contextuality-tensor.pdf`, exact arbitrary-$k$ disjoint-copy formulas addressing Muller & Saniga `arXiv:2609.19862v1` Sec. 6).
- **B. W. Jonah:** Share Lean 4.35.0 formalization of the spectral floor, Kramers floor, saturation theory, exact $C_3$ binary optima (`368` vs. `344`), and strict-law failure for one representative of each of the nine vertex cases of Conjecture E (`N ≥ 4`; case coverage via Jonah's Theorem B4, outside Lean; cases C1 and C6 are Jonah's own results), with explicit credit throughout.
- **Lean / Mathlib Community:** Candidate small hand-reviewed Mathlib PRs under `Apache-2.0` (only after human author review & handwritten prose): finite-field quadratic forms / symplectic transvections and exact integer third-moment inequalities.
