# Track 3 · Exact Sequential Contextuality Certificates & Setting-Bias Attack

Consolidates `0thernes/contextuality-evidence-lab` (`v1.0.0`): a sharp setting-bias bound for the Peres–Mermin square, a finite adaptive-tree supermartingale wealth theorem, an exact counterexample to naive calibration, and a hash-bound four-tool Tsotchke experiment.

## Headline Formal Results (`lean/Evidence/`)

- **Sharp setting-bias bound (`sharp_minimum`, `success_upper_bound`, `defect_success_bound`):** Minimum failure probability of any classical Peres–Mermin assignment equals the minimum context selection probability $\beta$; conditional floor $\beta$ caps success at $1 - \beta$ (or $1 - (1-\delta)\beta$ with exceptional budget $\delta$).
- **Finite adaptive-tree evidence bound (`BetTree.finite_hitting_bound`):** For every finite adaptive binary tree with conditional expected wealth factor $\le 1$, $\Pr(\text{ever reach } T) \le \text{initial wealth} / T$ under arbitrary optional stopping.
- **Constructive miscalibration counterexample (`naive_attack_prefix_crosses`, `concrete_classical_false_positive`):** Under setting bias $(11/60, \dots, 11/60, 1/12)$, the all-$+1$ classical strategy triggers a naive nominal $1\%$ test **97.2443815%** of the time within 1,000 IID trials (exact rational DP; $> 4.3\%$ already at 36 trials), whereas the bias-aware test stays at **0.8907211%** ($< 1\%$).

## Directory Contents

- `src/`: Exact rational evidence engine (`evidence.py`) and Tsotchke-stack runners (`stack_moonlab.mjs`, `stack_qrng.c`, `stack_enumeration.esk`).
- `scripts/`: Exact DP & replay (`run_experiment.py`), independent integer artifact verifier (`verify_artifact.py`), stack runner (`run_stack.py`), figure generator (`make_figures.py`).
- `web/`: Interactive sequential contextuality evidence browser lab.
- `results/`: Native Moonlab/QGTL/QRNG/Eshkol execution report (`stack_report.json`), shots, and replay verification logs.
- Paper: [`papers/sequential-evidence/`](../../papers/sequential-evidence/).
