# Formal Verification Trust Base (`lean/`)

This single unified Lean 4.35.0 + Mathlib `v4.35.0` (pinned rev `56a005855ea1`) Lake package houses all three Pauli contextuality libraries without cache duplication:

| Library | Track | Key Modules |
|---|---|---|
| `HoggarBound` | Track 1 (`tracks/spectral-bounds/`) | `Moment`, `Pauli`, `Bound`, `Counting`, `Corollaries`, `Quadric`, `Kramers`, `Witness`, `TwoQubit`, `Stability`, `SaturationTheory`, `ConjectureECore`, `ConjectureECones`, `ConjectureE`, `ConjectureEExtras`, `ConjectureECases`, `AuditUpgrades`, `C3ExactOptima`, `SaturatedPhaseSix`, `NormPhaseFamily`, `ExactDegreesN4N5`, `NonVacuity`, `CarrierFamily`, `Saturated*`, `C3{Certificate,Theorem,Spectra}` |
| `ContextualityTensor` | Track 2 (`tracks/disjoint-mermin/`) | `ContextualityTensor`, `ActualModel`, `Asymptotics`, `Pauli`, `Support`, `PhysicalBridge`, `SeedSupport`, `UnionModel` |
| `Evidence` | Track 3 (`tracks/sequential-evidence/`) | `Evidence`, `Square`, `Sequential`, `Physical`, `Bridge` |
| `Challenge` / `Solution` | All 3 tracks | 18-target isolated specification & sorry-free proof bridge verified by `lake comparator --config comparator.json --paranoid` |

## Reproduce from a Clean Clone

```bash
cd lean
lake exe cache get
lake build HoggarBound ContextualityTensor Evidence Solution VerifyAll
lake env lean VerifyAll.lean
lake comparator --config comparator.json --paranoid
# Standalone heavy Track 1 finite-certificate audits (also run in parallel CI):
lake build VerifyStandalone && lake env lean VerifyStandalone.lean
lake build VerifyPhaseSeven && lake env lean VerifyPhaseSeven.lean
```

## Module Audit Coverage (64 `.lean` Files; 1,221 Authored Declarations / 1,203 Non-Challenge)

- **Unified exhaustive audit (`VerifyAll.lean`, 45 transitive modules + `VerifyAll.lean`):** Imports all active headline libraries across `HoggarBound` (including `HoggarBound.Stability`, `HoggarBound.ConjectureECases`, and 8 perturbed-bound refutations in `NonVacuity.lean`), `ContextualityTensor` (including `ContextualityTensor.SeedSupport` and `ActualModel` minimum-defined asymptotics), `Evidence`, and `Solution.lean`. Audits `198` explicit `#print axioms` lines plus all `2,306` kernel theorem constants via `Lean.collectAxioms` (corresponding to `1,203` non-Challenge authored `theorem`/`lemma` declarations across all 64 `.lean` files).
- **Standalone finite-certificate CI audits (`VerifyStandalone.lean`, `VerifyPhaseSeven.lean`):** Compile and axiom-audit all nine heavy finite-certificate Track 1 modules (`FlatData`, `PhaseData`, `Saturated`, `SaturatedFive`, `SaturatedPhaseFive`, `C3Certificate`, `C3Theorem`, `C3Spectra`, `SaturatedPhaseSeven`) live in parallel CI jobs (`lean-verify-standalone`, `lean-verify-phase7`).
- **Isolated specification (`Challenge.lean`, 1 file):** Contains the 18 intentional `sorry` target declarations checked against sorry-free `Solution.lean` by six independent Lean kernels (`lake comparator --config comparator.json --paranoid`).
- **All 63 non-`Challenge` `.lean` files** are scanned for zero forbidden tokens (`sorry`, `admit`, `native_decide`, `unsafe`, `axiom`, `implemented_by`, `@[extern`) in CI and `tests/test_repo_integrity.py`.

## Verification Boundary

- **Zero forbidden tokens:** No `sorry`, `admit`, `native_decide`, `@[extern]`, `implemented_by`, or custom `axiom` in any proof module or `Solution.lean`. (`Challenge.lean` contains intentional `sorry` stubs as the comparator specification.)
- **Permitted axioms:** Strictly within `[propext, Classical.choice, Quot.sound]`, audited verbatim in [`results/lean-axioms-all.log`](../results/lean-axioms-all.log) and synced to [`README.md`](../README.md).
- **Outside the Lean kernel:** Statement-to-literature fidelity (mapped line-by-line in [`docs/statement-fidelity.md`](../docs/statement-fidelity.md)), the 42-orbit `W(5,2)` C census, the 540.3M-form `N=9` search, Jonah `[J3, Theorem B4]` single-orbit transitivity, and browser/Moonlab simulations.
