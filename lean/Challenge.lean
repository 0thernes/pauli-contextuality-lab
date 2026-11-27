/-
Pauli Contextuality Lab — Unified Isolated Challenge Specification (`lake comparator`).

Contains ONLY the target statements of 12 headline theorems spanning ALL THREE research tracks:
  - Track 1 (`HoggarBound`): spectral floor, Kramers floor, saturation squareness, infinite
    pure-CCZ family `|Psi_{3m}>`, exact C3 binary optima (368 vs 344), Jonah's Conjecture E
    (all 9 vertex cases, all N ≥ 4), and unconditional N=4..5 bounds (1455, 6444).
  - Track 2 (`ContextualityTensor`): exact degrees `(7^k - 5^k)/2` and `(6^k - 4^k)/2`
    for k disjoint Peres-Mermin squares and Mermin pentagrams (Muller & Saniga Sec. 6).
  - Track 3 (`Evidence`): sharp setting-bias bound on the Peres-Mermin square and finite
    adaptive-tree wealth supermartingale hitting bound.

NOTE: Every `sorry` here is intentional — `Challenge.lean` is the specification stub checked
against sorry-free `Solution.lean` by `lake comparator --config comparator.json --paranoid`.
-/
import HoggarBound.Bound
import HoggarBound.Counting
import HoggarBound.IndependentContexts
import HoggarBound.Quadric
import HoggarBound.C3Geometry
import HoggarBound.ConjectureECore
import HoggarBound.ConjectureEExtras
import ContextualityTensor
import ContextualityTensor.ActualModel
import ContextualityTensor.GeneralTheory
import Evidence.Square
import Evidence.Sequential

open Finset Matrix Filter Topology

namespace PauliContextualityLab.ComparatorTarget

/-! ### Track 1: Spectral Bounds, Saturating States & Jonah's Conjecture E -/

/-- Target 1 (Track 1, Thm 1): Universal spectral floor for arbitrary N-qubit Pauli subsets. -/
theorem target_spectral_floor {N : ℕ} (hN : 1 ≤ N) (S : Finset (HoggarBound.Pt N))
    (h0 : (0 : HoggarBound.Pt N) ∉ S) (f : HoggarBound.Pt N → ℝ)
    (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1) :
    ((2 : ℝ) ^ N - 1) * HoggarBound.beta6 S f ≤
      ((2 : ℝ) ^ N - 2) * S.card * Real.sqrt (((2 : ℝ) ^ N - 1) * S.card) := by
  sorry

/-- Target 2 (Track 1, Thm 2): Quaternionic / Kramers spectral floor for N ≥ 2. -/
theorem target_kramers_floor {N : ℕ} (hN : 2 ≤ N) (w : HoggarBound.Pt N)
    (hw : HoggarBound.qform w = 1) (S : Finset (HoggarBound.Pt N))
    (h0 : (0 : HoggarBound.Pt N) ∉ S)
    (hS : ∀ u ∈ S, HoggarBound.qform u + HoggarBound.symp w u = 0)
    (f : HoggarBound.Pt N → ℝ) (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1) :
    ((2 : ℝ) ^ (N - 1) - 1) * HoggarBound.beta6 S f ≤
      ((2 : ℝ) ^ (N - 1) - 2) * S.card * Real.sqrt (((2 : ℝ) ^ (N - 1) - 1) * S.card) := by
  sorry

/-- Target 3 (Track 1, Thm 4): Saturation forces `(2^N - 1) * |S|` to be a perfect square. -/
theorem target_saturation_mul_isSquare {N : ℕ} (hN : 2 ≤ N) (S : Finset (HoggarBound.Pt N))
    (hne : S.Nonempty) (f : HoggarBound.Pt N → ℝ) (hf : ∀ u ∈ S, f u = 1 ∨ f u = -1)
    (hsat : ((2 : ℝ) ^ N - 1) * HoggarBound.beta6 S f =
      ((2 : ℝ) ^ N - 2) * S.card * Real.sqrt (((2 : ℝ) ^ N - 1) * S.card)) :
    ∃ k : ℕ, (2 ^ N - 1) * S.card = k ^ 2 := by
  sorry

/-- Target 4 (Track 1, Thm 13b): Infinite non-closed contextual floor-saturating family `|Psi_{3m}>`. -/
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
        12 * (HoggarBound.violatedLines S f).card = (q ^ 3 - 1) * q ^ 3 * (q - 1) * (q - 2)) := by
  sorry

/-- Target 5 (Track 1, Thm 16''): Exact four-qubit C3 global binary completion optima (368 vs 344). -/
theorem target_c3_exact_binary_optima :
    (∀ y : Fin 64 → ℝ, (∀ i, y i = 1 ∨ y i = -1) →
      368 ≤ HoggarBound.ConjectureE.c3ViolatedOutsideContexts HoggarBound.C3.signA y) ∧
    (∃ y₀ : Fin 64 → ℝ, (∀ i, y₀ i = 1 ∨ y₀ i = -1) ∧
      HoggarBound.ConjectureE.c3ViolatedOutsideContexts HoggarBound.C3.signA y₀ = 368) ∧
    (∀ y : Fin 64 → ℝ, (∀ i, y i = 1 ∨ y i = -1) →
      344 ≤ HoggarBound.ConjectureE.c3ViolatedOutsideContexts HoggarBound.C3.signB y) ∧
    (∃ y₁ : Fin 64 → ℝ, (∀ i, y₁ i = 1 ∨ y₁ i = -1) ∧
      HoggarBound.ConjectureE.c3ViolatedOutsideContexts HoggarBound.C3.signB y₁ = 344) := by
  sorry

/-- Target 6 (Track 1, Thm 19): Jonah's Conjecture E across all nine vertex cases for all `N ≥ 4`. -/
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
    fails (HoggarBound.ConjectureE.perpSet (HoggarBound.ConjectureE.quadric N (HoggarBound.ConjectureE.ptY ⟨2, by omega⟩)) (HoggarBound.ConjectureE.ptZ ⟨0, by omega⟩)) (HoggarBound.ConjectureE.ptY ⟨1, by omega⟩) := by
  sorry

/-- Target 7 (Track 1): Unconditional Kramers-lifted lower bound `d(W(7,2)) ≥ 1455`. -/
theorem target_w72_ge_1455 (f : HoggarBound.Pt 4 → ℝ)
    (hf : ∀ u ∈ HoggarBound.allPoints 4, f u = 1 ∨ f u = -1) :
    1455 ≤ (HoggarBound.violatedLines (HoggarBound.allPoints 4) f).card := by
  sorry

/-- Target 8 (Track 1): Unconditional Kramers-lifted lower bound `d(Q⁺(9,2)) ≥ 6444`. -/
theorem target_q9plus_ge_6444 (f : HoggarBound.Pt 5 → ℝ)
    (hf : ∀ u ∈ HoggarBound.realPoints 5, f u = 1 ∨ f u = -1) :
    6444 ≤ (HoggarBound.violatedLines (HoggarBound.realPoints 5) f).card := by
  sorry

/-! ### Track 2: Exact Contextuality Degrees for Disjoint Mermin Configurations -/

/-- Target 9 (Track 2): Exact contextuality degree `(7^k - 5^k)/2` for `k` disjoint Peres-Mermin squares. -/
theorem target_disjoint_square_degree (k : ℕ) :
    (∃ a : Fin k → Fin 9 → Bool,
      ContextualityTensor.violations (fun i => ContextualityTensor.squareResponse (a i)) =
        (7 ^ k - 5 ^ k) / 2) ∧
    (∀ a : Fin k → Fin 9 → Bool,
      (7 ^ k - 5 ^ k) / 2 ≤
        ContextualityTensor.violations (fun i => ContextualityTensor.squareResponse (a i))) := by
  sorry

/-- Target 10 (Track 2): Exact contextuality degree `(6^k - 4^k)/2` for `k` disjoint Mermin pentagrams. -/
theorem target_disjoint_pentagram_degree (k : ℕ) :
    (∃ a : Fin k → Fin 10 → Bool,
      ContextualityTensor.violations (fun i => ContextualityTensor.pentagramResponse (a i)) =
        (6 ^ k - 4 ^ k) / 2) ∧
    (∀ a : Fin k → Fin 10 → Bool,
      (6 ^ k - 4 ^ k) / 2 ≤
        ContextualityTensor.violations (fun i => ContextualityTensor.pentagramResponse (a i))) := by
  sorry

/-! ### Track 3: Sequential Contextuality Evidence & Setting-Bias Bounds -/

/-- Target 11 (Track 3): Sharp minimum failure probability on the Peres-Mermin square equals `min_c p(c)`. -/
theorem target_peres_mermin_sharp_minimum (p : Fin 6 → ℝ) (c : Fin 6)
    (hp : ∀ d, 0 ≤ p d) (hc : ∀ d, p c ≤ p d) :
    (∃ a : Evidence.Assignment, Evidence.failureProbability p a = p c) ∧
    (∀ a : Evidence.Assignment, p c ≤ Evidence.failureProbability p a) := by
  sorry

/-- Target 12 (Track 3): Finite adaptive-tree supermartingale hitting-probability bound `≤ z / T`. -/
theorem target_sequential_hitting_bound (tree : Evidence.BetTree) (h : tree.Valid)
    (z T : ℝ) (hz : 0 ≤ z) (hT : 0 < T) :
    tree.hitProbability z T ≤ z / T := by
  sorry

/-! ### Track 2 Actual-Context Model & Minimum-Defined Asymptotics (Closing `ERRATA.md` #4) -/

/-- Target 13 (Track 2): Exact contextuality degree `(7^k - 5^k)/2` on the actual vertex-subset model. -/
theorem target_global_actual_square_minimum (k : ℕ) :
    (∃ a : (Σ _i : Fin k, Fin 9) → Bool,
      ContextualityTensor.actualViolations ContextualityTensor.squareContext (fun c => c == 5) a =
        (7 ^ k - 5 ^ k) / 2) ∧
    (∀ a : (Σ _i : Fin k, Fin 9) → Bool,
      (7 ^ k - 5 ^ k) / 2 ≤
        ContextualityTensor.actualViolations ContextualityTensor.squareContext (fun c => c == 5) a) := by
  sorry

/-- Target 14 (Track 2): Exact contextuality degree `(6^k - 4^k)/2` on the actual vertex-subset model. -/
theorem target_global_actual_pentagram_minimum (k : ℕ) :
    (∃ a : (Σ _i : Fin k, Fin 10) → Bool,
      ContextualityTensor.actualViolations ContextualityTensor.pentagramContext (fun c => c == 4) a =
        (6 ^ k - 4 ^ k) / 2) ∧
    (∀ a : (Σ _i : Fin k, Fin 10) → Bool,
      (6 ^ k - 4 ^ k) / 2 ≤
        ContextualityTensor.actualViolations ContextualityTensor.pentagramContext (fun c => c == 4) a) := by
  sorry

/-- Target 15 (Track 2): Minimum-defined contextuality fraction for `k` disjoint squares tends to `1`. -/
theorem target_actual_square_min_epsilon_tends_to_one :
    Tendsto ContextualityTensor.actualSquareMinEpsilon atTop (𝓝 1) := by
  sorry

/-- Target 16 (Track 2): Minimum-defined contextuality fraction for `k` disjoint pentagrams tends to `1`. -/
theorem target_actual_pentagram_min_epsilon_tends_to_one :
    Tendsto ContextualityTensor.actualPentagramMinEpsilon atTop (𝓝 1) := by
  sorry

/-! ### Kernel-Proved Refutations of Perturbed Headline Bounds (Closing `ERRATA.md` CI #2) -/

/-- Target 17 (Refutation): The tightened bound `d(W(5,2)) ≥ 64` is false. -/
theorem target_refute_w52_bound_64 :
    ¬ (∀ f : HoggarBound.Pt 3 → ℝ, (∀ u ∈ HoggarBound.allPoints 3, f u = 1 ∨ f u = -1) →
        64 ≤ (HoggarBound.violatedLines (HoggarBound.allPoints 3) f).card) := by
  sorry

/-- Target 18 (Refutation): The tightened C3 binary bound `≥ 369` on `signA` is false. -/
theorem target_refute_c3_signA_bound_369 :
    ¬ (∀ y : Fin 64 → ℝ, (∀ i, y i = 1 ∨ y i = -1) →
        369 ≤ HoggarBound.ConjectureE.c3ViolatedOutsideContexts HoggarBound.C3.signA y) := by
  sorry

/-! ### Complete Track 2 General Theory (Theorems 2 & 5, Eqs. 5, 12, 14–16) -/

/-- Target 19 (Track 2, Theorem 2, Eq. 7): Heterogeneous multilinear endpoint reduction. -/
theorem target_heterogeneous_endpoint_reduction {k : ℕ}
    {C : Fin k → Type*} [∀ i, Fintype (C i)] [∀ i, DecidableEq (C i)]
    {A : Fin k → Type*} (R : (i : Fin k) → A i → C i → ℤ)
    (l u : Fin k → ℤ)
    (hbounds : ∀ i a, l i ≤ 1 + ∑ c, R i a c ∧ 1 + ∑ c, R i a c ≤ u i)
    (hattain : ∀ i, (∃ a, 1 + ∑ c, R i a c = l i) ∧ (∃ a, 1 + ∑ c, R i a c = u i)) :
    (∀ a : (i : Fin k) → A i, ContextualityTensor.hetScore (fun i => R i (a i)) + 1 ≤
      ContextualityTensor.cornerMax l u) ∧
    (∃ a : (i : Fin k) → A i, ContextualityTensor.hetScore (fun i => R i (a i)) + 1 =
      ContextualityTensor.cornerMax l u) := by
  sorry

/-- Target 20 (Track 2, Eq. 12): Exact contextuality degree `(7^s 6^t - 5^s 4^t) / 2` for
`s` disjoint Peres–Mermin squares and `t` disjoint Mermin pentagrams. -/
theorem target_mixed_square_pentagram_minimum (s t : ℕ) :
    (ContextualityTensor.hetContexts (ContextualityTensor.mixedContextType s t)).card + 1 =
      7 ^ s * 6 ^ t ∧
    (∃ a : (i : Fin s ⊕ Fin t) → ContextualityTensor.mixedAssignType s t i,
      ContextualityTensor.hetViolations (fun i => ContextualityTensor.mixedResponse s t i (a i)) =
        (7 ^ s * 6 ^ t - 5 ^ s * 4 ^ t) / 2) ∧
    (∀ a : (i : Fin s ⊕ Fin t) → ContextualityTensor.mixedAssignType s t i,
      (7 ^ s * 6 ^ t - 5 ^ s * 4 ^ t) / 2 ≤
        ContextualityTensor.hetViolations (fun i => ContextualityTensor.mixedResponse s t i (a i))) := by
  sorry

/-- Target 21 (Track 2, Theorem 5, Eq. 13): For EVERY finite contextual signed seed with distinct
nonempty contexts, the genuine minimum-defined contextuality fraction `ε_k → 1`. -/
theorem target_general_seed_epsilon_tends_to_one {C V : Type*} [Fintype C] [DecidableEq C]
    [Fintype V] [DecidableEq V] (seed : C → Finset V) (negative : C → Bool)
    (hi : Function.Injective seed) (hne : ∀ c, (seed c).Nonempty)
    (hctx : ∀ a : V → Bool, ∃ c : C, ContextualityTensor.response a (negative c) (seed c) = -1) :
    Tendsto (ContextualityTensor.actualMinEpsilon seed negative) atTop (𝓝 1) := by
  sorry

/-- Target 22 (Track 2, Eq. 5): Arbitrary-`k` `2k`-qubit Pauli operator realization for `k` squares. -/
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
          (ContextualityTensor.unionContext ContextualityTensor.squareContext q) : ℤ) : ℂ) • 1) := by
  sorry

/-- Target 23 (Track 2, Eq. 5): Arbitrary-`k` `3k`-qubit Pauli operator realization for `k` pentagrams. -/
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
          (ContextualityTensor.unionContext ContextualityTensor.pentagramContext q) : ℤ) : ℂ) • 1) := by
  sorry

/-- Target 24 (Track 2, Eqs. 15–16): `k`-independent readout-noise violation thresholds for
disjoint Peres–Mermin squares and Mermin pentagrams. -/
theorem target_noise_thresholds_k_independent (k : ℕ) (hk : 1 ≤ k) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    ((5 : ℝ) ^ k - 1 < ContextualityTensor.noisyScore 6 3 k p ↔ (2 : ℝ) / 3 < (1 - 2 * p) ^ 3) ∧
    ((4 : ℝ) ^ k - 1 < ContextualityTensor.noisyScore 5 4 k p ↔ (3 : ℝ) / 5 < (1 - 2 * p) ^ 4) := by
  sorry

end PauliContextualityLab.ComparatorTarget
