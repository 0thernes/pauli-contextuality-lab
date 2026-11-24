/-
Pauli Contextuality Lab — Unified Exhaustive Axiom Audit across ALL THREE Tracks:
  Track 1 (`HoggarBound`): spectral floor, Kramers floor, saturation theory, infinite CCZ family,
    exact C3 optima (368/344), Jonah's Conjecture E (all 9 cases + spectra), N=4..5 ladders,
    TwoQubit & Hoggar witnesses (`d(W(5,2))=63`, `d(Q⁻(5,2))=9`), and all 10 NonVacuity witnesses
    (116 explicit Track 1 declarations covering 100% of historical `VerifyNewFormalizations.lean` + legacy witnesses).
  Track 2 (`ContextualityTensor`): exact degrees `(7^k-5^k)/2` and `(6^k-4^k)/2`, Pauli bridge,
    actual union model, asymptotics (16 explicit declarations covering 100% of historical `Verification.lean`).
  Track 3 (`Evidence`): Peres-Mermin sharp setting-bias bound, finite adaptive-tree supermartingale
    hitting bound, concrete classical miscalibration counterexample (14 explicit declarations).
  Comparator Bridge (`Solution.lean`): all 12 cross-track `ComparatorTarget` theorems.
  PLUS an exhaustive `Lean.collectAxioms` metaprogram auditing EVERY single `theorem` in
  `HoggarBound`, `ContextualityTensor`, `Evidence`, and `PauliContextualityLab`.

Run: `cd lean && lake env lean VerifyAll.lean`
Every theorem must depend strictly on `[propext, Classical.choice, Quot.sound]` (or fewer).
-/
import Lean
import HoggarBound.Bound
import HoggarBound.Counting
import HoggarBound.Corollaries
import HoggarBound.Quadric
import HoggarBound.Kramers
import HoggarBound.Witness
import HoggarBound.TwoQubit
import HoggarBound.SaturationTheory
import HoggarBound.ConjectureECore
import HoggarBound.ConjectureECones
import HoggarBound.ConjectureE
import HoggarBound.ConjectureEExtras
import HoggarBound.AuditUpgrades
import HoggarBound.C3ExactOptima
import HoggarBound.SaturatedPhaseSix
import HoggarBound.NormPhaseFamily
import HoggarBound.ExactDegreesN4N5
import HoggarBound.NonVacuity
import ContextualityTensor
import ContextualityTensor.ActualModel
import ContextualityTensor.Asymptotics
import ContextualityTensor.Pauli
import ContextualityTensor.Support
import ContextualityTensor.PhysicalBridge
import Evidence
import Solution

-- ============================================================================
-- Track 1: Baseline, Witnesses, Kramers, Saturation, Conjecture E, C3 Optima,
--          Infinite CCZ Family, N=4..5 Ladders, and NonVacuity (116 decls)
-- ============================================================================
#print axioms HoggarBound.hoggar_bound
#print axioms HoggarBound.three_qubit_contexts
#print axioms HoggarBound.mermin_peres
#print axioms HoggarBound.doily_contexts
#print axioms HoggarBound.degree_three_qubit
#print axioms HoggarBound.degree_three_qubit_elliptic

-- Theorem 2: Quaternionic / Kramers spectral floor and elliptic quadrics
#print axioms HoggarBound.kramers_even_mult
#print axioms HoggarBound.sum_cube_le_even_mult
#print axioms HoggarBound.trace_cube_le_kramers
#print axioms HoggarBound.hoggar_bound_quaternionic
#print axioms HoggarBound.hoggar_bound_quaternionic_violated
#print axioms HoggarBound.card_ellipticPoints
#print axioms HoggarBound.card_flags_elliptic
#print axioms HoggarBound.elliptic_fraction
#print axioms HoggarBound.three_qubit_elliptic_contexts
#print axioms HoggarBound.four_qubit_elliptic_contexts
#print axioms HoggarBound.five_qubit_elliptic_contexts

-- Theorems 3 & 4: Saturation equivalences, Pauli expansion of A², and (2^N - 1)|S| = □
#print axioms HoggarBound.sum_cube_eq_iff
#print axioms HoggarBound.matrix_eq_sum_pauli
#print axioms HoggarBound.opA_sq_eq
#print axioms HoggarBound.saturation_tfae
#print axioms HoggarBound.saturation_mul_isSquare

-- Lemmas 20 & 21 and the Universal Cubic-Trace Identity
#print axioms HoggarBound.ConjectureE.lemma20_jordan_action
#print axioms HoggarBound.ConjectureE.trace_completion_pow_eq
#print axioms HoggarBound.ConjectureE.trace_completion_cube_universal
#print axioms HoggarBound.ConjectureE.lemma21_trace_cube_sylvester
#print axioms HoggarBound.ConjectureE.lemma21_trace_cube_symm

-- Closed-form outside character sums S_O(s) across all nine vertex cases
#print axioms HoggarBound.ConjectureE.charSumOut_C1
#print axioms HoggarBound.ConjectureE.charSumOut_C3_C5
#print axioms HoggarBound.ConjectureE.charSumOut_C6
#print axioms HoggarBound.ConjectureE.charSumOut_C8
#print axioms HoggarBound.ConjectureE.charSumOut_C11_C14
#print axioms HoggarBound.ConjectureE.charSumOut_C12_C15

-- Theorem 19: Jonah's Conjecture E in all nine vertex cases
#print axioms HoggarBound.ConjectureE.c1_strict_law_fails
#print axioms HoggarBound.ConjectureE.c3_strict_law_fails
#print axioms HoggarBound.ConjectureE.c5_strict_law_fails
#print axioms HoggarBound.ConjectureE.c6_strict_law_fails
#print axioms HoggarBound.ConjectureE.c8_strict_law_fails
#print axioms HoggarBound.ConjectureE.c11_strict_law_fails
#print axioms HoggarBound.ConjectureE.c12_strict_law_fails
#print axioms HoggarBound.ConjectureE.c14_strict_law_fails
#print axioms HoggarBound.ConjectureE.c15_strict_law_fails
#print axioms HoggarBound.ConjectureE.jonah_conjecture_e_all_nine_cases

-- Corollary 18: General cone lift and C11 from C3 for every N ≥ 4
#print axioms HoggarBound.ConjectureE.cone_lift_opA_reindex
#print axioms HoggarBound.ConjectureE.cone_lift_carrier_charpoly
#print axioms HoggarBound.ConjectureE.cone_lift_completion_reindex
#print axioms HoggarBound.ConjectureE.cone_lift_completion_charpoly
#print axioms HoggarBound.ConjectureE.cone_lift_completion_trace_cube
#print axioms HoggarBound.ConjectureE.cone_lift_strict_law_fails
#print axioms HoggarBound.ConjectureE.corollary18_c11_from_c3

-- Corollary 16: Four-qubit C3 binary completion minima separation
#print axioms HoggarBound.ConjectureE.c3_quadForm_eq
#print axioms HoggarBound.ConjectureE.corollary16_sigmaA_lower
#print axioms HoggarBound.ConjectureE.corollary16_sigmaB_lower
#print axioms HoggarBound.ConjectureE.corollary16_sigmaB_witness
#print axioms HoggarBound.ConjectureE.corollary16_binary_minima_differ

-- AuditUpgrades: Asymptotics, Propositions 3/8/10, Clifford transport, spectra, SDP-dual C3
#print axioms HoggarBound.AuditUpgrades.floor_deficit_tendsto_zero
#print axioms HoggarBound.AuditUpgrades.full_space_fraction_tendsto_half
#print axioms HoggarBound.AuditUpgrades.hyperbolic_fraction_tendsto_half
#print axioms HoggarBound.AuditUpgrades.full_space_violated_fraction_eventually_gt
#print axioms HoggarBound.AuditUpgrades.elliptic_violated_fraction_eventually_gt
#print axioms HoggarBound.AuditUpgrades.proposition3_commuting_qgt
#print axioms HoggarBound.AuditUpgrades.anticommuting_qgt
#print axioms HoggarBound.AuditUpgrades.proposition3_violated_iff
#print axioms HoggarBound.AuditUpgrades.proposition3_satisfied_iff
#print axioms HoggarBound.AuditUpgrades.proposition8_flat_state_qgt
#print axioms HoggarBound.AuditUpgrades.pure_state_pauli_sq_transform
#print axioms HoggarBound.AuditUpgrades.proposition10_two_character_sum
#print axioms HoggarBound.AuditUpgrades.proposition10_hyperplane_card
#print axioms HoggarBound.AuditUpgrades.clifford_preserves_symp
#print axioms HoggarBound.AuditUpgrades.clifford_transport_comm_product
#print axioms HoggarBound.AuditUpgrades.clifford_transport_opA
#print axioms HoggarBound.AuditUpgrades.clifford_transport_carrier_charpoly
#print axioms HoggarBound.AuditUpgrades.clifford_transport_completion_charpoly
#print axioms HoggarBound.AuditUpgrades.clifford_transport_strict_law_fails
#print axioms HoggarBound.AuditUpgrades.completionMat_isHermitian
#print axioms HoggarBound.AuditUpgrades.real_hermitian_charpoly_eq_iff_roots_eq
#print axioms HoggarBound.AuditUpgrades.strict_law_fails_to_spectra
#print axioms HoggarBound.AuditUpgrades.jonah_conjecture_e_all_nine_cases_spectra
#print axioms HoggarBound.AuditUpgrades.c3SdpBlock_pos_def
#print axioms HoggarBound.AuditUpgrades.c3_shift_quad_zero
#print axioms HoggarBound.AuditUpgrades.corollary16_sigmaB_sdp_lower
#print axioms HoggarBound.AuditUpgrades.corollary16_sigmaA_witness
#print axioms HoggarBound.AuditUpgrades.corollary16_binary_minima_tightened

-- C3ExactOptima: Exact global binary completion optima of four-qubit C3 (368 and 344, gap 24)
#print axioms HoggarBound.C3ExactOptima.corollary16_sigmaA_exact_lower
#print axioms HoggarBound.C3ExactOptima.corollary16_sigmaB_exact_lower
#print axioms HoggarBound.C3ExactOptima.corollary16_exact_binary_optima

-- SaturatedPhaseSix & NormPhaseFamily: Infinite non-closed pure-CCZ family |Ψ_{3m}⟩
#print axioms HoggarBound.det6_card
#print axioms HoggarBound.det6_contexts
#print axioms HoggarBound.det6_degree
#print axioms HoggarBound.NormPhaseFamily.detPhase_isFlatState
#print axioms HoggarBound.NormPhaseFamily.detSupport_card
#print axioms HoggarBound.NormPhaseFamily.detSupport_not_closed
#print axioms HoggarBound.NormPhaseFamily.detSupport_flags_card
#print axioms HoggarBound.NormPhaseFamily.infinite_nonclosed_saturated_family
#print axioms HoggarBound.NormPhaseFamily.infinite_nonclosed_family_contextual

-- ExactDegreesN4N5: Transvection invariance, CSS witnesses, ladders, unconditional bounds
#print axioms HoggarBound.ExactDegreesN4N5.transv_violatedLines_eq
#print axioms HoggarBound.ExactDegreesN4N5.q7minus_css_witness
#print axioms HoggarBound.ExactDegreesN4N5.w72_css_witness
#print axioms HoggarBound.ExactDegreesN4N5.q9plus_css_witness
#print axioms HoggarBound.ExactDegreesN4N5.d_W72_of_Q7minus
#print axioms HoggarBound.ExactDegreesN4N5.d_Q9plus_of_W72
#print axioms HoggarBound.ExactDegreesN4N5.w72_ge_1455
#print axioms HoggarBound.ExactDegreesN4N5.q9plus_ge_6444
#print axioms HoggarBound.ExactDegreesN4N5.lemma_L1_q7minus_section_le_92
#print axioms HoggarBound.ExactDegreesN4N5.lemma_L4_w52_hyperplane_le_21
#print axioms HoggarBound.ExactDegreesN4N5.exact_degrees_n4_n5_of_q7minus_315

-- NonVacuity: Explicit existential non-vacuity witnesses for every headline family
#print axioms HoggarBound.NonVacuity.spectral_floor_nonvacuous
#print axioms HoggarBound.NonVacuity.kramers_nonvacuous
#print axioms HoggarBound.NonVacuity.saturation_tfae_nonvacuous
#print axioms HoggarBound.NonVacuity.conjecture_e_nonvacuous
#print axioms HoggarBound.NonVacuity.clifford_transport_nonvacuous
#print axioms HoggarBound.NonVacuity.cone_lift_nonvacuous
#print axioms HoggarBound.NonVacuity.norm_phase_family_nonvacuous
#print axioms HoggarBound.NonVacuity.c3_exact_optima_nonvacuous
#print axioms HoggarBound.NonVacuity.exact_degrees_ladders_nonvacuous
#print axioms HoggarBound.NonVacuity.propositions_qgt_twochar_nonvacuous

-- ============================================================================
-- Track 2: Exact Contextuality Degrees for Disjoint Mermin Configurations (16 decls)
-- ============================================================================
#print axioms ContextualityTensor.score_factorization
#print axioms ContextualityTensor.score_violations
#print axioms ContextualityTensor.square_minimum_closed_form
#print axioms ContextualityTensor.pentagram_minimum_closed_form
#print axioms ContextualityTensor.unionContext_injective
#print axioms ContextualityTensor.union_response
#print axioms ContextualityTensor.square_actual_context_count
#print axioms ContextualityTensor.pentagram_actual_context_count
#print axioms ContextualityTensor.square_epsilon_is_count_ratio
#print axioms ContextualityTensor.pentagram_epsilon_is_count_ratio
#print axioms ContextualityTensor.global_actual_square_minimum
#print axioms ContextualityTensor.global_actual_pentagram_minimum
#print axioms ContextualityTensor.square_epsilon_tends_to_one
#print axioms ContextualityTensor.pentagram_epsilon_tends_to_one
#print axioms ContextualityTensor.actual_square_epsilon_tends_to_one
#print axioms ContextualityTensor.actual_pentagram_epsilon_tends_to_one

-- ============================================================================
-- Track 3: Sequential Contextuality Evidence & Setting-Bias Bounds (14 decls)
-- ============================================================================
#print axioms Evidence.square_no_all_win
#print axioms Evidence.square_singleton_witness
#print axioms Evidence.sharp_minimum
#print axioms Evidence.success_upper_bound
#print axioms Evidence.defect_success_bound
#print axioms Evidence.ideal_observables
#print axioms Evidence.ideal_context_commutation
#print axioms Evidence.ideal_context_product
#print axioms Evidence.local_factor_bound
#print axioms Evidence.BetTree.finite_hitting_bound
#print axioms Evidence.naive_attack_prefix_crosses
#print axioms Evidence.naive_attack_prefix_probability
#print axioms Evidence.concrete_classical_false_positive
#print axioms Evidence.classical_square_node_valid

-- ============================================================================
-- Unified 12-Target Comparator Solution Bridge (12 decls)
-- ============================================================================
#print axioms PauliContextualityLab.ComparatorTarget.target_spectral_floor
#print axioms PauliContextualityLab.ComparatorTarget.target_kramers_floor
#print axioms PauliContextualityLab.ComparatorTarget.target_saturation_mul_isSquare
#print axioms PauliContextualityLab.ComparatorTarget.target_infinite_nonclosed_saturated_family
#print axioms PauliContextualityLab.ComparatorTarget.target_c3_exact_binary_optima
#print axioms PauliContextualityLab.ComparatorTarget.target_jonah_conjecture_e_all_nine_cases
#print axioms PauliContextualityLab.ComparatorTarget.target_w72_ge_1455
#print axioms PauliContextualityLab.ComparatorTarget.target_q9plus_ge_6444
#print axioms PauliContextualityLab.ComparatorTarget.target_disjoint_square_degree
#print axioms PauliContextualityLab.ComparatorTarget.target_disjoint_pentagram_degree
#print axioms PauliContextualityLab.ComparatorTarget.target_peres_mermin_sharp_minimum
#print axioms PauliContextualityLab.ComparatorTarget.target_sequential_hitting_bound

-- ============================================================================
-- Exhaustive Metaprogram Audit: EVERY theorem across all four project namespaces
-- ============================================================================
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let prefixes : Array Name := #[`HoggarBound, `ContextualityTensor, `Evidence, `PauliContextualityLab]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let all := env.constants.toList.filter fun (name, info) =>
    info.isTheorem && prefixes.any (fun p => p.isPrefixOf name)
  if all.isEmpty then
    throwError "No project theorems found for exhaustive axiom audit"
  let mut bad : Array String := #[]
  for (name, _) in all do
    let axioms ← Lean.collectAxioms name
    let forbidden := axioms.filter fun a => !allowed.contains a
    if !forbidden.isEmpty then
      bad := bad.push s!"{name}: {forbidden}"
  if !bad.isEmpty then
    throwError s!"Disallowed axioms detected across project theorems:\n{String.intercalate "\n" bad.toList}"
  logInfo m!"ALL_THEOREMS_AXIOM_AUDIT_PASS: checked {all.length} theorems across HoggarBound, ContextualityTensor, Evidence, PauliContextualityLab — 0 disallowed axioms."
