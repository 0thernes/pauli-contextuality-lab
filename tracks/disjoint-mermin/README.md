# Track 2 · Exact Contextuality Degrees for Disjoint Mermin Configurations

Consolidates `0thernes/contextuality-tensor-lab` (`v0.1.0`), directly proving the arbitrary-copy contextuality degree question posed in **Section 6 of Muller & Saniga (`arXiv:2609.19862v1`)**.

## Headline Formal Results (`lean/ContextualityTensor/`)

For the full context family formed from $k$ disjoint copies of a local configuration (all nonempty unions choosing at most one local context per block):

- **$k$ disjoint Peres–Mermin squares (`square_minimum_closed_form`, `global_actual_square_minimum`):**
  $$d_k = \frac{7^k - 5^k}{2}, \qquad L_k = 7^k - 1, \qquad \frac{2 d_k}{L_k} \longrightarrow 1.$$
- **$k$ disjoint Mermin pentagrams (`pentagram_minimum_closed_form`, `global_actual_pentagram_minimum`):**
  $$d_k = \frac{6^k - 4^k}{2}, \qquad L_k = 6^k - 1, \qquad \frac{2 d_k}{L_k} \longrightarrow 1.$$
- **Proof mechanism:** Exact score factorization $1 + \text{score} = \prod_i (1 + \text{local score}_i)$ (`score_factorization`) paired with explicit attaining assignments and literal Pauli-matrix realization (`PhysicalBridge.lean`, `ActualModel.lean`).

## Directory Contents

- `src/`: Exact certificate generator (`certificates.py`) and Tsotchke-stack runners (`stack_moonlab.mjs`, `stack_qrng.c`, `stack_enumeration.esk`).
- `scripts/`: Exact verifier (`verify_exact.py`), stack runner (`run_stack.py`), paper builder.
- `web/`: Live 4-qubit interactive Mermin-square browser lab.
- `results/`: Exact certificate JSONs and independent check records.
- Paper: [`papers/disjoint-mermin/`](../../papers/disjoint-mermin/).
