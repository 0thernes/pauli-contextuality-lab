# Publication Status (Track 3 — Sequential Contextuality Evidence)

- **Current release:** `v2.4.0` (24 November 2026), consolidated into [`pauli-contextuality-lab`](https://github.com/0thernes/pauli-contextuality-lab) (`papers/sequential-evidence/`, `tracks/sequential-evidence/`, `lean/Evidence/`).
- **Author:** Alexander S. Donahue (Independent researcher, Spokane, WA, USA; ORCID [0009-0006-8168-9648](https://orcid.org/0009-0006-8168-9648)).
- **Licences:** Code `Apache-2.0` (`LICENSE`); manuscripts and documentation `CC-BY-4.0` (`LICENSE-DOCS`).

| Channel | Status | Link |
|---|---|---|
| Unified repository | Live (`v2.4.0`) | [pauli-contextuality-lab](https://github.com/0thernes/pauli-contextuality-lab) |
| Unified GitHub Pages (Track 3 lab) | Live | [Sequential Evidence Lab](https://0thernes.github.io/pauli-contextuality-lab/sequential-evidence/) |
| Paper PDF | Live | [whitepaper.pdf](https://0thernes.github.io/pauli-contextuality-lab/papers/sequential-evidence/whitepaper.pdf) |
| Archived standalone snapshot | Read-only archive (`v1.0.0`) | [contextuality-evidence-lab](https://github.com/0thernes/contextuality-evidence-lab) |
| Journal submission / external peer review | Not submitted / not peer reviewed | Research preprint only |

## Verification Boundaries

Publication means public distribution as a research preprint and executable artifact. It does not mean journal acceptance, arXiv submission, a DOI, independent external peer review, or established historical priority.

The Lean 4 formalization (`lean/Evidence/Square.lean`, `lean/Evidence/Sequential.lean`, audited inside `lean/VerifyAll.lean` and replayed across 6 Lean kernels via `lake comparator --paranoid`) proves a conditional finite-model setting-bias bound and constructs a concrete 36-round miscalibration counterexample. No physical quantum apparatus was used; the conditional setting floor, absence of within-trial context leakage, and physical measurement compatibility are explicit hypotheses outside the recorded classical simulations.
