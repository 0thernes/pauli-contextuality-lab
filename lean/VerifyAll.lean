/-
Pauli Contextuality Lab — Unified Exhaustive Axiom Audit across ALL THREE Tracks:
  Track 1 (`HoggarBound`): spectral floor, Kramers floor, saturation theory, infinite CCZ family,
    exact C3 optima (368/344), Jonah's Conjecture E (all 9 cases + spectra), N=4..5 ladders,
    TwoQubit & Hoggar witnesses (`d(W(5,2))=63`, `d(Q⁻(5,2))=9`), NonVacuity.
  Track 2 (`ContextualityTensor`): exact degrees `(7^k-5^k)/2` and `(6^k-4^k)/2`, Pauli bridge,
    actual union model, asymptotics.
  Track 3 (`Evidence`): Peres-Mermin sharp setting-bias bound, finite adaptive-tree supermartingale
    hitting bound, concrete classical miscalibration counterexample.

Run: `cd lean && lake env lean VerifyAll.lean`
Every theorem must depend strictly on `[propext, Classical.choice, Quot.sound]` (or fewer).
-/
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

-- Track 1: Spectral Bounds, Witnesses, Saturation, Conjecture E, C3 Optima, Ladders, NonVacuity
#print axioms HoggarBound.hoggar_bound
#print axioms HoggarBound.hoggar_bound_quaternionic
#print axioms HoggarBound.elliptic_fraction
#print axioms HoggarBound.three_qubit_contexts
#print axioms HoggarBound.three_qubit_elliptic_contexts
#print axioms HoggarBound.four_qubit_elliptic_contexts
#print axioms HoggarBound.five_qubit_elliptic_contexts
#print axioms HoggarBound.mermin_peres
#print axioms HoggarBound.doily_contexts
#print axioms HoggarBound.degree_three_qubit
#print axioms HoggarBound.degree_three_qubit_elliptic
#print axioms HoggarBound.saturation_tfae
#print axioms HoggarBound.saturation_mul_isSquare
#print axioms HoggarBound.ConjectureE.trace_completion_cube_universal
#print axioms HoggarBound.ConjectureE.jonah_conjecture_e_all_nine_cases
#print axioms HoggarBound.ConjectureE.corollary18_c11_from_c3
#print axioms HoggarBound.ConjectureE.corollary16_binary_minima_differ
#print axioms HoggarBound.AuditUpgrades.floor_deficit_tendsto_zero
#print axioms HoggarBound.AuditUpgrades.full_space_fraction_tendsto_half
#print axioms HoggarBound.AuditUpgrades.hyperbolic_fraction_tendsto_half
#print axioms HoggarBound.AuditUpgrades.proposition3_violated_iff
#print axioms HoggarBound.AuditUpgrades.proposition8_flat_state_qgt
#print axioms HoggarBound.AuditUpgrades.proposition10_two_character_sum
#print axioms HoggarBound.AuditUpgrades.clifford_transport_strict_law_fails
#print axioms HoggarBound.AuditUpgrades.jonah_conjecture_e_all_nine_cases_spectra
#print axioms HoggarBound.AuditUpgrades.corollary16_sigmaB_sdp_lower
#print axioms HoggarBound.AuditUpgrades.corollary16_binary_minima_tightened
#print axioms HoggarBound.C3ExactOptima.corollary16_sigmaA_exact_lower
#print axioms HoggarBound.C3ExactOptima.corollary16_sigmaB_exact_lower
#print axioms HoggarBound.C3ExactOptima.corollary16_exact_binary_optima
#print axioms HoggarBound.det6_degree
#print axioms HoggarBound.NormPhaseFamily.detPhase_isFlatState
#print axioms HoggarBound.NormPhaseFamily.infinite_nonclosed_saturated_family
#print axioms HoggarBound.NormPhaseFamily.infinite_nonclosed_family_contextual
#print axioms HoggarBound.ExactDegreesN4N5.transv_violatedLines_eq
#print axioms HoggarBound.ExactDegreesN4N5.q7minus_css_witness
#print axioms HoggarBound.ExactDegreesN4N5.w72_css_witness
#print axioms HoggarBound.ExactDegreesN4N5.q9plus_css_witness
#print axioms HoggarBound.ExactDegreesN4N5.w72_ge_1455
#print axioms HoggarBound.ExactDegreesN4N5.q9plus_ge_6444
#print axioms HoggarBound.ExactDegreesN4N5.exact_degrees_n4_n5_of_q7minus_315
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

-- Track 2: Exact Contextuality Degrees for Disjoint Mermin Configurations
#print axioms ContextualityTensor.score_factorization
#print axioms ContextualityTensor.score_violations
#print axioms ContextualityTensor.square_minimum_closed_form
#print axioms ContextualityTensor.pentagram_minimum_closed_form
#print axioms ContextualityTensor.global_actual_square_minimum
#print axioms ContextualityTensor.global_actual_pentagram_minimum
#print axioms ContextualityTensor.square_epsilon_tends_to_one
#print axioms ContextualityTensor.pentagram_epsilon_tends_to_one
#print axioms ContextualityTensor.actual_square_epsilon_tends_to_one
#print axioms ContextualityTensor.actual_pentagram_epsilon_tends_to_one

-- Track 3: Sequential Contextuality Evidence & Setting-Bias Bounds
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

-- Unified 12-Target Comparator Solution Bridge
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
