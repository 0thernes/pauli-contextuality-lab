/-
Pauli Contextuality Lab — Standalone Finite-Certificate & C3 Spectral Axiom Audit.

Compiles and axiom-audits the eight finite-certificate Track 1 modules previously outside
default CI (`FlatData`, `PhaseData`, `Saturated`, `SaturatedFive`, `SaturatedPhaseFive`,
`C3Certificate`, `C3Theorem`, `C3Spectra`), restoring live CI-compiled kernel evidence for:
  - `pivot_degree` (4-qubit 135-observable pivot configuration, degree 75)
  - `cieslinski5_degree` & `phase5_degree` (5-qubit 496-observable flat/phase states, degree 480)
  - `quadric_degree` (315), `hoggar_degree` (63), `ccz_degree` (0), `lly_degree` (0)
  - `four_qubit_C3_counterexample` & `four_qubit_C3_spectral_counterexample` (exact 4-qubit C3
    cospectrality and completion cubic-moment / eigenvalue-multiset separation)

Run: `cd lean && lake build VerifyStandalone && lake env lean VerifyStandalone.lean`
Every theorem must depend strictly on `[propext, Classical.choice, Quot.sound]`.
-/
import Lean
import HoggarBound.Saturated
import HoggarBound.SaturatedPhaseFive
import HoggarBound.C3Spectra

#print axioms HoggarBound.lly_degree
#print axioms HoggarBound.ccz_degree
#print axioms HoggarBound.hoggar_degree
#print axioms HoggarBound.quadric_degree
#print axioms HoggarBound.pivot_degree
#print axioms HoggarBound.cieslinski5_degree
#print axioms HoggarBound.phase5_degree
#print axioms HoggarBound.phase5_contexts
#print axioms HoggarBound.C3.carrier_charpoly_eq
#print axioms HoggarBound.C3.pauli_carrier_charpoly_eq
#print axioms HoggarBound.C3.pauli_carrier_eigenvalues_eq
#print axioms HoggarBound.C3.pauli_completion_charpoly_ne
#print axioms HoggarBound.C3.pauli_completion_eigenvalues_ne
#print axioms HoggarBound.C3.pauli_completion_eigenvalue_multisets_ne
#print axioms HoggarBound.C3.four_qubit_C3_counterexample
#print axioms HoggarBound.C3.four_qubit_C3_spectral_counterexample

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let targets : Array Name := #[
    `HoggarBound.lly_degree, `HoggarBound.ccz_degree, `HoggarBound.hoggar_degree,
    `HoggarBound.quadric_degree, `HoggarBound.pivot_degree, `HoggarBound.cieslinski5_degree,
    `HoggarBound.phase5_degree, `HoggarBound.phase5_contexts,
    `HoggarBound.C3.carrier_charpoly_eq, `HoggarBound.C3.pauli_carrier_charpoly_eq,
    `HoggarBound.C3.pauli_carrier_eigenvalues_eq, `HoggarBound.C3.pauli_completion_charpoly_ne,
    `HoggarBound.C3.pauli_completion_eigenvalues_ne, `HoggarBound.C3.pauli_completion_eigenvalue_multisets_ne,
    `HoggarBound.C3.four_qubit_C3_counterexample, `HoggarBound.C3.four_qubit_C3_spectral_counterexample
  ]
  let mut bad : Array String := #[]
  for name in targets do
    let axioms ← Lean.collectAxioms name
    let forbidden := axioms.filter fun a => !allowed.contains a
    if !forbidden.isEmpty then
      bad := bad.push s!"{name}: {forbidden}"
  if !bad.isEmpty then
    throwError s!"Disallowed axioms in VerifyStandalone:\n{String.intercalate "\n" bad.toList}"
  logInfo m!"STANDALONE_AXIOM_AUDIT_PASS: verified {targets.size} standalone Track 1 finite-certificate & C3 spectral theorems — 0 disallowed axioms."
