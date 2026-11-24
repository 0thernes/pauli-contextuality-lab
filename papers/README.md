# Papers & Correspondence Guide

All manuscripts in this directory are **unreviewed research preprints** by **Alexander S. Donahue** (independent researcher, ORCID [`0009-0006-8168-9648`](https://orcid.org/0009-0006-8168-9648)), produced with AI assistance under human direction, and licensed under **CC-BY-4.0** (`LICENSE-DOCS`).

## Three Manuscripts in This Repository

| Folder | Paper | Direct Relation to Prior Literature | Formal Lean 4.35.0 Library |
|---|---|---|---|
| [`spectral-bounds/`](spectral-bounds/) | *Spectral bounds and their limits in Pauli contextuality: exact configurations and a proof of Jonah's Conjecture E* (`unified-contextuality.pdf`, plus archived initial REVTeX note in `revtex-v1/`) | Builds on symplectic polar spaces $W(2N-1,2)$ and quadrics $Q^\pm(2N-1,2)$ of **Muller, Saniga, Holweck, Giorgetti, and Kelleher** (`arXiv:2407.02928`), Jonah's Zenodo preprints (non-peer-reviewed), Li–Gupta–Ganesh (`arXiv:2610.26465`), Cieśliński (`arXiv:2610.07172`), and Okumura (1974). | `lean/HoggarBound/` |
| [`disjoint-mermin/`](disjoint-mermin/) | *Exact contextuality degrees for disjoint Mermin configurations* (`contextuality-tensor.pdf`, `.tex`, `.md`, `.bib`) | Directly proves exact arbitrary-$k$ formulas $d_k = (7^k - 5^k)/2$ (squares) and $(6^k - 4^k)/2$ (pentagrams) for the repeated-disjoint-copy problem in **Section 6 of Muller & Saniga (`arXiv:2609.19862v1`)**. | `lean/ContextualityTensor/` |
| [`sequential-evidence/`](sequential-evidence/) | *Contextuality Evidence Lab: Exact Sequential Certificates and a Constructive Setting-Bias Attack* (`whitepaper.pdf`, `.md`) | Methods artifact applying finite adaptive-tree supermartingale tests (Zhang–Glancy–Knill) to the Peres–Mermin square under setting bias. | `lean/Evidence/` |

## Guide for External Reviewers & Correspondents

If you are reviewing this work following correspondence regarding symplectic Pauli contextuality (e.g., **M. Saniga, A. Muller, F. Holweck, C. Kelleher, A. Giorgetti**):

1. **Five-second mechanical proof check:** See the verbatim `#print axioms` block at the top of [`README.md`](../README.md) — every theorem depends strictly on `[propext, Classical.choice, Quot.sound]`, with zero `sorry`, zero `native_decide`, and zero custom axioms.
2. **Line-by-line statement audit:** [`docs/statement-fidelity.md`](../docs/statement-fidelity.md) maps every Lean declaration to its mathematical definition in the papers so you can check for definition drift or hidden hypotheses without reading proof scripts.
3. **Interactive theorem dependency graph:** Browse the Lean Blueprint at [`/blueprint/`](https://0thernes.github.io/pauli-contextuality-lab/blueprint/).
4. **Honest scope & limitations:** See [`CLAIMS.md`](../CLAIMS.md) (every claim tagged `kernel-checked`, `certificate-checked`, `paper proof`, `numerical_approximation`, or `open`, with explicit falsifiers) and [`LIMITATIONS.md`](../LIMITATIONS.md) (explicit CRediT & AI-contribution disclosure).
5. **Corrections:** Please open an issue or email `0_0@0thernes.art`.
