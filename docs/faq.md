# Frequently Asked Questions

### 1. Why were four repositories consolidated into `pauli-contextuality-lab`?
`hoggar-bound`, `hoggar-bound-lab`, `contextuality-tensor-lab`, and `contextuality-evidence-lab` all studied multiqubit Pauli and Peres-Mermin contextuality using the identical Lean 4.35.0 + Mathlib `56a005855ea1` toolchain and identical vendored `third_party/` stack. Consolidating them eliminates duplicate multi-gigabyte Mathlib caches, resolves root clutter, aligns open licensing (`Apache-2.0` + `CC-BY-4.0`), and gives external researchers one coherent codebase. The four legacy GitHub repositories remain publicly archived (read-only) with redirect notices so no existing links break.

### 2. Why is `kochen-specker-extremal-lab` kept as a separate repository?
`kochen-specker-extremal-lab` proves exact minimum Kochen-Specker ray sets in real coordinate pools using a **zero-Mathlib** Lean 4.35.0 kernel (clean build in ~27 seconds) plus SAT/DRUP certificates. Keeping it separate preserves its tiny Mathlib-free trust base.

### 3. Are these papers peer reviewed?
**No.** Every manuscript in `papers/` is an unreviewed research preprint produced with AI assistance under human direction. The Lean 4 formal proofs are mechanically certified by the Lean kernel (and configured for 6-kernel `lake comparator --paranoid`), which certifies logical validity of the formalized Lean statements — not external peer review, historical priority, or statement-to-literature fidelity (which requires human domain review).

### 4. Does Moonlab / QGTL / quantum_rng mean experiments ran on real quantum hardware?
**No.** Moonlab is a classical state-vector simulator compiled to WebAssembly, `quantum_rng` is a seeded classical software generator, and QGTL provides classical differential-geometry C kernels. Nothing in this repository is a measurement on physical quantum hardware.

### 5. Which tracks directly address the papers of Muller, Saniga, Holweck, Giorgetti, and Kelleher?
- **Track 1 (`tracks/spectral-bounds/`, `papers/spectral-bounds/`)** builds on the symplectic polar spaces $W(2N-1,2)$ and quadrics $Q^\pm(2N-1,2)$ studied by Muller, Saniga, Holweck, Giorgetti, and Kelleher (`arXiv:2407.02928`), formalizing the spectral floor, exact $N=4,5$ ladders, saturating states, and Jonah's Conjecture E.
- **Track 2 (`tracks/disjoint-mermin/`, `papers/disjoint-mermin/`)** directly proves the exact closed-form degrees $d_k = (7^k - 5^k)/2$ (disjoint Peres-Mermin squares) and $(6^k - 4^k)/2$ (disjoint Mermin pentagrams) posed as an open question in Section 6 of Muller & Saniga (`arXiv:2609.19862v1`).
