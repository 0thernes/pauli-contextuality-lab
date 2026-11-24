# Independent Verification Companion (Track 1 Explorer)

This directory contains a dependency-free browser explorer of five checked Pauli-contextuality configurations (three-, four-, and five-qubit full spaces and real four- and five-qubit hyperbolic quadrics). It runs live at https://0thernes.github.io/pauli-contextuality-lab/independent-review/.

## Local Preview

From the repository root:

```sh
python scripts/build_site.py
python -m http.server 8769 --directory build/site --bind 127.0.0.1
```

Then visit `http://127.0.0.1:8769/independent-review/`. Flip observable signs, generate a random assignment, apply strictly improving single flips, restore the stored witness, or export an assignment for the C verifier. A local search minimum is not a global proof.

## Mathematical & Implementation Evidence

- [Unified Track 1 manuscript](../../../../papers/spectral-bounds/unified-contextuality.pdf): definitions, proofs, literature context, and limitations.
- [Statement-fidelity table](../../../../docs/statement-fidelity.md): maps prose claims to Lean 4.35.0 declarations.
- [Literature audit](../../results/literature-audit.md): bounded prior-art check (does not establish historical priority).
- [Lean audit](../../results/lean-audit.md) & [unified axiom log](../../../../results/lean-axioms-all.log): exact theorem statements and strict standard-axiom receipts.
- [Independent matrix checks](../../results/independent_validation.json): 138,792 contexts across 12 geometries, eight witness recounts, and 120 sparse supports.
- [Stack audit](../../results/stack-independent-audit.md): separately replayed Moonlab simulation, QGTL differential-geometry kernels, seeded software RNG, and Eshkol arithmetic.

## Reproduce from Repository Root

```sh
python scripts/verify_all.py
python -m pytest -v tests/
node --test tests/test_web_models.mjs
cd lean && lake exe cache get && lake build HoggarBound Solution && lake env lean VerifyAll.lean
```

## Interpretation

Moonlab is a classical state-vector simulator, `quantum_rng` is a classical quantum-inspired software mixer, QGTL checks two specified differential-geometry kernels, and Eshkol provides independent arithmetic checks. This is a theoretical and computational research artifact, not a physical quantum experiment.
