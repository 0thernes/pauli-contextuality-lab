/-
Pauli Contextuality Lab — Unified Sorry-Free Solution Module Matched Against `Challenge`.

Every theorem below has the definitionally identical signature to `Challenge.lean`, uses ZERO
`sorry`, `admit`, `native_decide`, or custom axioms, and is verified across all six Lean 4.35.0
kernels by `lake comparator --config comparator.json --paranoid`.
-/
import HoggarBound.Bound
import HoggarBound.Counting
import HoggarBound.IndependentContexts
import HoggarBound.Quadric
import HoggarBound.C3Geometry
import HoggarBound.Kramers
import HoggarBound.SaturationTheory
import HoggarBound.ConjectureECore
import HoggarBound.ConjectureE
import HoggarBound.ConjectureEExtras
import HoggarBound.C3ExactOptima
import HoggarBound.NormPhaseFamily
import HoggarBound.ExactDegreesN4N5
import HoggarBound.NonVacuity
import ContextualityTensor
import ContextualityTensor.ActualModel
import ContextualityTensor.GeneralTheory
import Evidence.Square
import Evidence.Sequential

open Finset Matrix Filter Topology

namespace PauliContextualityLab.ComparatorTarget

theorem target_spectral_floor {N : ℕ} (hN : 1 ≤ N) (S : Finset (HoggarBound.Pt N))
    (h0 : (0 : HoggarBound.Pt N) ∉ S) (f : HoggarBound.Pt N → ℝ)
    (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1) :
    ((2 : ℝ) ^ N - 1) * HoggarBound.beta6 S f ≤
      ((2 : ℝ) ^ N - 2) * S.card * Real.sqrt (((2 : ℝ) ^ N - 1) * S.card) :=
  HoggarBound.hoggar_bound hN S h0 f hf

theorem target_kramers_floor {N : ℕ} (hN : 2 ≤ N) (w : HoggarBound.Pt N)
    (hw : HoggarBound.qform w = 1) (S : Finset (HoggarBound.Pt N))
    (h0 : (0 : HoggarBound.Pt N) ∉ S)
    (hS : ∀ u ∈ S, HoggarBound.qform u + HoggarBound.symp w u = 0)
    (f : HoggarBound.Pt N → ℝ) (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1) :
    ((2 : ℝ) ^ (N - 1) - 1) * HoggarBound.beta6 S f ≤
      ((2 : ℝ) ^ (N - 1) - 2) * S.card * Real.sqrt (((2 : ℝ) ^ (N - 1) - 1) * S.card) :=
  HoggarBound.hoggar_bound_quaternionic hN w hw S h0 hS f hf

theorem target_saturation_mul_isSquare {N : ℕ} (hN : 2 ≤ N) (S : Finset (HoggarBound.Pt N))
    (hne : S.Nonempty) (f : HoggarBound.Pt N → ℝ) (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1)
    (hsat : ((2 : ℝ) ^ N - 1) * HoggarBound.beta6 S f =
      ((2 : ℝ) ^ N - 2) * S.card * Real.sqrt (((2 : ℝ) ^ N - 1) * S.card)) :
    ∃ k : ℕ, (2 ^ N - 1) * S.card = k ^ 2 :=
  HoggarBound.saturation_mul_isSquare hN S hne f hf hsat

theorem target_infinite_nonclosed_saturated_family (m : ℕ) (hm : 1 ≤ m) :
    let q := 2 ^ m
    ∃ S : Finset (HoggarBound.Pt (3 * m)),
      (0 : HoggarBound.Pt (3 * m)) ∉ S ∧
      S.card = (q ^ 3 - 1) * q ^ 2 ∧
      (∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ HoggarBound.symp u v = 0 ∧ u + v ∉ S) ∧
      6 * (HoggarBound.contexts S).card = (q ^ 3 - 1) * q ^ 4 * (q ^ 2 + q - 3) ∧
      (∀ f : HoggarBound.Pt (3 * m) → ℝ, (∀ u ∈ S, f u = 1 ∨ f u = -1) →
        (q ^ 3 - 1) * q ^ 3 * (q - 1) * (q - 2) ≤ 12 * (HoggarBound.violatedLines S f).card) ∧
      (∃ f : HoggarBound.Pt (3 * m) → ℝ, (∀ u, f u = 1 ∨ f u = -1) ∧
        12 * (HoggarBound.violatedLines S f).card = (q ^ 3 - 1) * q ^ 3 * (q - 1) * (q - 2)) :=
  HoggarBound.NormPhaseFamily.infinite_nonclosed_saturated_family m hm

theorem target_c3_exact_binary_optima :
    (∀ y : Fin 64 → ℝ, (∀ i, y i = 1 ∨ y i = -1) →
      368 ≤ HoggarBound.ConjectureE.c3ViolatedOutsideContexts HoggarBound.C3.signA y) ∧
    (∃ y₀ : Fin 64 → ℝ, (∀ i, y₀ i = 1 ∨ y₀ i = -1) ∧
      HoggarBound.ConjectureE.c3ViolatedOutsideContexts HoggarBound.C3.signA y₀ = 368) ∧
    (∀ y : Fin 64 → ℝ, (∀ i, y i = 1 ∨ y i = -1) →
      344 ≤ HoggarBound.ConjectureE.c3ViolatedOutsideContexts HoggarBound.C3.signB y) ∧
    (∃ y₁ : Fin 64 → ℝ, (∀ i, y₁ i = 1 ∨ y₁ i = -1) ∧
      HoggarBound.ConjectureE.c3ViolatedOutsideContexts HoggarBound.C3.signB y₁ = 344) :=
  HoggarBound.C3ExactOptima.corollary16_exact_binary_optima

theorem target_jonah_conjecture_e_all_nine_cases {N : ℕ} (hN : 4 ≤ N) :
    let fails (X : Finset (HoggarBound.Pt N)) (d : HoggarBound.Pt N) : Prop :=
      ∃ σ τ : HoggarBound.Pt N → ℝ, (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
        (HoggarBound.opA (HoggarBound.ConjectureE.sectionOf X d) σ).charpoly =
          (HoggarBound.opA (HoggarBound.ConjectureE.sectionOf X d) τ).charpoly ∧
        (HoggarBound.ConjectureE.completionMat X d σ).charpoly ≠
          (HoggarBound.ConjectureE.completionMat X d τ).charpoly
    fails (HoggarBound.allPoints N) (HoggarBound.ConjectureE.ptZ ⟨0, by omega⟩) ∧
    fails (HoggarBound.ConjectureE.quadric N 0) (HoggarBound.ConjectureE.ptZ ⟨0, by omega⟩) ∧
    fails (HoggarBound.ConjectureE.quadric N (HoggarBound.ConjectureE.ptY ⟨1, by omega⟩)) (HoggarBound.ConjectureE.ptZ ⟨0, by omega⟩) ∧
    fails (HoggarBound.ConjectureE.perpSet (HoggarBound.allPoints N) (HoggarBound.ConjectureE.ptZ ⟨0, by omega⟩)) (HoggarBound.ConjectureE.ptZ ⟨1, by omega⟩) ∧
    fails (HoggarBound.ConjectureE.perpSet (HoggarBound.ConjectureE.quadric N 0) (HoggarBound.ConjectureE.ptY ⟨0, by omega⟩)) (HoggarBound.ConjectureE.ptZ ⟨1, by omega⟩) ∧
    fails (HoggarBound.ConjectureE.perpSet (HoggarBound.ConjectureE.quadric N 0) (HoggarBound.ConjectureE.ptZ ⟨0, by omega⟩)) (HoggarBound.ConjectureE.ptZ ⟨1, by omega⟩) ∧
    fails (HoggarBound.ConjectureE.perpSet (HoggarBound.ConjectureE.quadric N 0) (HoggarBound.ConjectureE.ptZ ⟨0, by omega⟩)) (HoggarBound.ConjectureE.ptY ⟨1, by omega⟩) ∧
    fails (HoggarBound.ConjectureE.perpSet (HoggarBound.ConjectureE.quadric N (HoggarBound.ConjectureE.ptY ⟨2, by omega⟩)) (HoggarBound.ConjectureE.ptZ ⟨0, by omega⟩)) (HoggarBound.ConjectureE.ptZ ⟨1, by omega⟩) ∧
    fails (HoggarBound.ConjectureE.perpSet (HoggarBound.ConjectureE.quadric N (HoggarBound.ConjectureE.ptY ⟨2, by omega⟩)) (HoggarBound.ConjectureE.ptZ ⟨0, by omega⟩)) (HoggarBound.ConjectureE.ptY ⟨1, by omega⟩) :=
  HoggarBound.ConjectureE.jonah_conjecture_e_all_nine_cases hN

theorem target_w72_ge_1455 (f : HoggarBound.Pt 4 → ℝ)
    (hf : ∀ u ∈ HoggarBound.allPoints 4, f u = 1 ∨ f u = -1) :
    1455 ≤ (HoggarBound.violatedLines (HoggarBound.allPoints 4) f).card :=
  HoggarBound.ExactDegreesN4N5.w72_ge_1455 f hf

theorem target_q9plus_ge_6444 (f : HoggarBound.Pt 5 → ℝ)
    (hf : ∀ u ∈ HoggarBound.realPoints 5, f u = 1 ∨ f u = -1) :
    6444 ≤ (HoggarBound.violatedLines (HoggarBound.realPoints 5) f).card :=
  HoggarBound.ExactDegreesN4N5.q9plus_ge_6444 f hf

theorem target_disjoint_square_degree (k : ℕ) :
    (∃ a : Fin k → Fin 9 → Bool,
      ContextualityTensor.violations (fun i => ContextualityTensor.squareResponse (a i)) =
        (7 ^ k - 5 ^ k) / 2) ∧
    (∀ a : Fin k → Fin 9 → Bool,
      (7 ^ k - 5 ^ k) / 2 ≤
        ContextualityTensor.violations (fun i => ContextualityTensor.squareResponse (a i))) :=
  ContextualityTensor.square_minimum_closed_form k

theorem target_disjoint_pentagram_degree (k : ℕ) :
    (∃ a : Fin k → Fin 10 → Bool,
      ContextualityTensor.violations (fun i => ContextualityTensor.pentagramResponse (a i)) =
        (6 ^ k - 4 ^ k) / 2) ∧
    (∀ a : Fin k → Fin 10 → Bool,
      (6 ^ k - 4 ^ k) / 2 ≤
        ContextualityTensor.violations (fun i => ContextualityTensor.pentagramResponse (a i))) :=
  ContextualityTensor.pentagram_minimum_closed_form k

theorem target_peres_mermin_sharp_minimum (p : Fin 6 → ℝ) (c : Fin 6)
    (hp : ∀ d, 0 ≤ p d) (hc : ∀ d, p c ≤ p d) :
    (∃ a : Evidence.Assignment, Evidence.failureProbability p a = p c) ∧
    (∀ a : Evidence.Assignment, p c ≤ Evidence.failureProbability p a) :=
  Evidence.sharp_minimum p c hp hc

theorem target_sequential_hitting_bound (tree : Evidence.BetTree) (h : tree.Valid)
    (z T : ℝ) (hz : 0 ≤ z) (hT : 0 < T) :
    tree.hitProbability z T ≤ z / T :=
  Evidence.BetTree.finite_hitting_bound tree h z T hz hT

theorem target_global_actual_square_minimum (k : ℕ) :
    (∃ a : (Σ _i : Fin k, Fin 9) → Bool,
      ContextualityTensor.actualViolations ContextualityTensor.squareContext (fun c => c == 5) a =
        (7 ^ k - 5 ^ k) / 2) ∧
    (∀ a : (Σ _i : Fin k, Fin 9) → Bool,
      (7 ^ k - 5 ^ k) / 2 ≤
        ContextualityTensor.actualViolations ContextualityTensor.squareContext (fun c => c == 5) a) :=
  ContextualityTensor.global_actual_square_minimum k

theorem target_global_actual_pentagram_minimum (k : ℕ) :
    (∃ a : (Σ _i : Fin k, Fin 10) → Bool,
      ContextualityTensor.actualViolations ContextualityTensor.pentagramContext (fun c => c == 4) a =
        (6 ^ k - 4 ^ k) / 2) ∧
    (∀ a : (Σ _i : Fin k, Fin 10) → Bool,
      (6 ^ k - 4 ^ k) / 2 ≤
        ContextualityTensor.actualViolations ContextualityTensor.pentagramContext (fun c => c == 4) a) :=
  ContextualityTensor.global_actual_pentagram_minimum k

theorem target_actual_square_min_epsilon_tends_to_one :
    Tendsto ContextualityTensor.actualSquareMinEpsilon atTop (𝓝 1) :=
  ContextualityTensor.actual_square_min_epsilon_tends_to_one

theorem target_actual_pentagram_min_epsilon_tends_to_one :
    Tendsto ContextualityTensor.actualPentagramMinEpsilon atTop (𝓝 1) :=
  ContextualityTensor.actual_pentagram_min_epsilon_tends_to_one

theorem target_refute_w52_bound_64 :
    ¬ (∀ f : HoggarBound.Pt 3 → ℝ, (∀ u ∈ HoggarBound.allPoints 3, f u = 1 ∨ f u = -1) →
        64 ≤ (HoggarBound.violatedLines (HoggarBound.allPoints 3) f).card) :=
  HoggarBound.NonVacuity.refute_w52_bound_64

theorem target_refute_c3_signA_bound_369 :
    ¬ (∀ y : Fin 64 → ℝ, (∀ i, y i = 1 ∨ y i = -1) →
        369 ≤ HoggarBound.ConjectureE.c3ViolatedOutsideContexts HoggarBound.C3.signA y) :=
  HoggarBound.NonVacuity.refute_c3_signA_bound_369

theorem target_heterogeneous_endpoint_reduction {k : ℕ}
    {C : Fin k → Type*} [∀ i, Fintype (C i)] [∀ i, DecidableEq (C i)]
    {A : Fin k → Type*} (R : (i : Fin k) → A i → C i → ℤ)
    (l u : Fin k → ℤ)
    (hbounds : ∀ i a, l i ≤ 1 + ∑ c, R i a c ∧ 1 + ∑ c, R i a c ≤ u i)
    (hattain : ∀ i, (∃ a, 1 + ∑ c, R i a c = l i) ∧ (∃ a, 1 + ∑ c, R i a c = u i)) :
    (∀ a : (i : Fin k) → A i, ContextualityTensor.hetScore (fun i => R i (a i)) + 1 ≤
      ContextualityTensor.cornerMax l u) ∧
    (∃ a : (i : Fin k) → A i, ContextualityTensor.hetScore (fun i => R i (a i)) + 1 =
      ContextualityTensor.cornerMax l u) :=
  ContextualityTensor.heterogeneous_endpoint_reduction R l u hbounds hattain

theorem target_mixed_square_pentagram_minimum (s t : ℕ) :
    (ContextualityTensor.hetContexts (ContextualityTensor.mixedContextType s t)).card + 1 =
      7 ^ s * 6 ^ t ∧
    (∃ a : (i : Fin s ⊕ Fin t) → ContextualityTensor.mixedAssignType s t i,
      ContextualityTensor.hetViolations (fun i => ContextualityTensor.mixedResponse s t i (a i)) =
        (7 ^ s * 6 ^ t - 5 ^ s * 4 ^ t) / 2) ∧
    (∀ a : (i : Fin s ⊕ Fin t) → ContextualityTensor.mixedAssignType s t i,
      (7 ^ s * 6 ^ t - 5 ^ s * 4 ^ t) / 2 ≤
        ContextualityTensor.hetViolations (fun i => ContextualityTensor.mixedResponse s t i (a i))) :=
  ContextualityTensor.mixed_square_pentagram_minimum s t

theorem target_general_seed_epsilon_tends_to_one {C V : Type*} [Fintype C] [DecidableEq C]
    [Fintype V] [DecidableEq V] (seed : C → Finset V) (negative : C → Bool)
    (hi : Function.Injective seed) (hne : ∀ c, (seed c).Nonempty)
    (hctx : ∀ a : V → Bool, ∃ c : C, ContextualityTensor.response a (negative c) (seed c) = -1) :
    Tendsto (ContextualityTensor.actualMinEpsilon seed negative) atTop (𝓝 1) :=
  ContextualityTensor.general_seed_epsilon_tends_to_one seed negative hi hne hctx

theorem target_arbitrary_k_square_pauli_realization (k : ℕ) :
    (∀ x, (ContextualityTensor.kSquarePauli k x).IsHermitian ∧
      ContextualityTensor.kSquarePauli k x * ContextualityTensor.kSquarePauli k x = 1 ∧
      ContextualityTensor.kSquarePauli k x ≠ 1) ∧
    Function.Injective (ContextualityTensor.kSquarePauli k) ∧
    (∀ x y, x.1 ≠ y.1 →
      ContextualityTensor.kSquarePauli k x * ContextualityTensor.kSquarePauli k y =
      ContextualityTensor.kSquarePauli k y * ContextualityTensor.kSquarePauli k x) ∧
    (∀ q ∈ ContextualityTensor.contexts k (Fin 6),
      (ContextualityTensor.unionVertexList ContextualityTensor.squareCtxList q).toFinset =
        ContextualityTensor.unionContext ContextualityTensor.squareContext q ∧
      (∀ x ∈ ContextualityTensor.unionContext ContextualityTensor.squareContext q,
        ∀ y ∈ ContextualityTensor.unionContext ContextualityTensor.squareContext q,
        ContextualityTensor.kSquarePauli k x * ContextualityTensor.kSquarePauli k y =
        ContextualityTensor.kSquarePauli k y * ContextualityTensor.kSquarePauli k x) ∧
      ((ContextualityTensor.unionVertexList ContextualityTensor.squareCtxList q).map
          (ContextualityTensor.kSquarePauli k)).prod =
        ((ContextualityTensor.actualSign ContextualityTensor.squareContext (fun c => c == 5)
          (ContextualityTensor.unionContext ContextualityTensor.squareContext q) : ℤ) : ℂ) • 1) :=
  ContextualityTensor.arbitrary_k_square_pauli_realization k

theorem target_arbitrary_k_pentagram_pauli_realization (k : ℕ) :
    (∀ x, (ContextualityTensor.kPentagramPauli k x).IsHermitian ∧
      ContextualityTensor.kPentagramPauli k x * ContextualityTensor.kPentagramPauli k x = 1 ∧
      ContextualityTensor.kPentagramPauli k x ≠ 1) ∧
    Function.Injective (ContextualityTensor.kPentagramPauli k) ∧
    (∀ x y, x.1 ≠ y.1 →
      ContextualityTensor.kPentagramPauli k x * ContextualityTensor.kPentagramPauli k y =
      ContextualityTensor.kPentagramPauli k y * ContextualityTensor.kPentagramPauli k x) ∧
    (∀ q ∈ ContextualityTensor.contexts k (Fin 5),
      (ContextualityTensor.unionVertexList ContextualityTensor.pentagramCtxList q).toFinset =
        ContextualityTensor.unionContext ContextualityTensor.pentagramContext q ∧
      (∀ x ∈ ContextualityTensor.unionContext ContextualityTensor.pentagramContext q,
        ∀ y ∈ ContextualityTensor.unionContext ContextualityTensor.pentagramContext q,
        ContextualityTensor.kPentagramPauli k x * ContextualityTensor.kPentagramPauli k y =
        ContextualityTensor.kPentagramPauli k y * ContextualityTensor.kPentagramPauli k x) ∧
      ((ContextualityTensor.unionVertexList ContextualityTensor.pentagramCtxList q).map
          (ContextualityTensor.kPentagramPauli k)).prod =
        ((ContextualityTensor.actualSign ContextualityTensor.pentagramContext (fun c => c == 4)
          (ContextualityTensor.unionContext ContextualityTensor.pentagramContext q) : ℤ) : ℂ) • 1) :=
  ContextualityTensor.arbitrary_k_pentagram_pauli_realization k

theorem target_noise_thresholds_k_independent (k : ℕ) (hk : 1 ≤ k) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    ((5 : ℝ) ^ k - 1 < ContextualityTensor.noisyScore 6 3 k p ↔ (2 : ℝ) / 3 < (1 - 2 * p) ^ 3) ∧
    ((4 : ℝ) ^ k - 1 < ContextualityTensor.noisyScore 5 4 k p ↔ (3 : ℝ) / 5 < (1 - 2 * p) ^ 4) :=
  ⟨ContextualityTensor.square_noise_threshold_iff k hk p hp0 hp1,
   ContextualityTensor.pentagram_noise_threshold_iff k hk p hp0 hp1⟩

end PauliContextualityLab.ComparatorTarget
