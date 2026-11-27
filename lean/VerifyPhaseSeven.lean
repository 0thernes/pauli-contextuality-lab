/-
Pauli Contextuality Lab — Seven-Qubit Phase-State Certificate Axiom Audit.

Compiles and axiom-audits `HoggarBound.SaturatedPhaseSeven` (8,128 observables,
2,824,192 contexts, exact degree 729,344). Run in its own dedicated CI job because
the kernel checks 16 blocks of 1,024 packed rows sequentially (`Elab.async false`).

Run: `cd lean && lake build VerifyPhaseSeven && lake env lean VerifyPhaseSeven.lean`
-/
import Lean
import HoggarBound.SaturatedPhaseSeven

#print axioms HoggarBound.phase7_card
#print axioms HoggarBound.phase7_flags
#print axioms HoggarBound.phase7_witness
#print axioms HoggarBound.phase7_degree
#print axioms HoggarBound.phase7_contexts

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let targets : Array Name := #[
    `HoggarBound.phase7_card, `HoggarBound.phase7_flags, `HoggarBound.phase7_witness,
    `HoggarBound.phase7_degree, `HoggarBound.phase7_contexts
  ]
  let mut bad : Array String := #[]
  for name in targets do
    let axioms ← Lean.collectAxioms name
    let forbidden := axioms.filter fun a => !allowed.contains a
    if !forbidden.isEmpty then
      bad := bad.push s!"{name}: {forbidden}"
  if !bad.isEmpty then
    throwError s!"Disallowed axioms in VerifyPhaseSeven:\n{String.intercalate "\n" bad.toList}"
  logInfo m!"PHASE7_AXIOM_AUDIT_PASS: verified {targets.size} seven-qubit phase-state certificate theorems — 0 disallowed axioms."
