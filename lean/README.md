# Formal Verification Trust Base (`lean/`)

This single unified Lean 4.35.0 + Mathlib `v4.35.0` (pinned rev `56a005855ea1`) Lake package houses all three Pauli contextuality libraries without cache duplication:

| Library | Track | Key Modules |
|---|---|---|
| `HoggarBound` | Track 1 (`tracks/spectral-bounds/`) | `Moment`, `Pauli`, `Bound`, `Counting`, `Corollaries`, `Quadric`, `Kramers`, `Witness`, `TwoQubit`, `Stability`, `SaturationTheory`, `ConjectureECore`, `ConjectureECones`, `ConjectureE`, `ConjectureEExtras`, `AuditUpgrades`, `C3ExactOptima`, `SaturatedPhaseSix`, `NormPhaseFamily`, `ExactDegreesN4N5`, `NonVacuity`, `CarrierFamily`, `Saturated*` |
| `ContextualityTensor` | Track 2 (`tracks/disjoint-mermin/`) | `ContextualityTensor`, `ActualModel`, `Asymptotics`, `Pauli`, `Support`, `PhysicalBridge`, `UnionModel` |
| `Evidence` | Track 3 (`tracks/sequential-evidence/`) | `Evidence`, `Square`, `Sequential`, `Physical`, `Bridge` |
| `Challenge` / `Solution` | All 3 tracks | 12-target isolated specification & sorry-free proof bridge verified by `lake comparator --config comparator.json --paranoid` |

## Reproduce from a Clean Clone

```bash
cd lean
lake exe cache get
lake build HoggarBound ContextualityTensor Evidence Solution
lake env lean VerifyAll.lean
lake comparator --config comparator.json --paranoid
```

## Module Audit Coverage (60 `.lean` Files)

- **Unified exhaustive audit (`VerifyAll.lean`, 44 transitive modules + `VerifyAll.lean`):** Imports all active headline libraries across `HoggarBound` (including `HoggarBound.Stability`), `ContextualityTensor`, `Evidence` (including `Evidence.{Square,Sequential,Physical,Bridge}` via Lean 4.35 `module` / `public import`), and `Solution.lean`. Audits `166` explicit `#print axioms` lines plus all `2,206` project theorems via `Lean.collectAxioms`.
- **Isolated specification (`Challenge.lean`, 1 file):** Contains the 12 intentional `sorry` target declarations checked against sorry-free `Solution.lean` by six independent Lean kernels (`lake comparator --config comparator.json --paranoid`).
- **Root umbrella & heavy finite-certificate modules (14 files):** `HoggarBound.lean` (root aggregator) plus standalone finite-certificate proof modules (`HoggarBound.{C3Certificate,C3Spectra,C3Theorem,FlatData,PhaseData,Saturated,SaturatedFive,SaturatedPhaseFive,SaturatedPhaseSeven}`) and dedicated standalone audit scripts (`C3Verification.lean`, `IndependentVerification.lean`, `SaturatedVerification.lean`, `SaturatedSevenVerification.lean`, `StabilityVerification.lean`, `VerifyNewFormalizations.lean`). All 59 non-`Challenge` `.lean` files are scanned for zero forbidden tokens (`sorry`, `admit`, `native_decide`, `unsafe`, `axiom`, `implemented_by`, `@[extern`) in CI and `tests/test_repo_integrity.py`.

## Verification Boundary

- **Zero forbidden tokens:** No `sorry`, `admit`, `native_decide`, `@[extern]`, `implemented_by`, or custom `axiom` in any proof module or `Solution.lean`. (`Challenge.lean` contains intentional `sorry` stubs as the comparator specification.)
- **Permitted axioms:** Strictly within `[propext, Classical.choice, Quot.sound]`, audited verbatim in [`results/lean-axioms-all.log`](../results/lean-axioms-all.log) and synced to [`README.md`](../README.md).
- **Outside the Lean kernel:** Statement-to-literature fidelity (mapped line-by-line in [`docs/statement-fidelity.md`](../docs/statement-fidelity.md)), the 42-orbit `W(5,2)` C census, the 540.3M-form `N=9` search, Jonah `[J3, Theorem B4]` single-orbit transitivity, and browser/Moonlab simulations.
