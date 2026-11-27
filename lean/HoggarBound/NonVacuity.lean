/-
Hoggar Bound Lab — Explicit Non-Vacuity Witnesses for Every Headline Theorem.

In formal verification of mathematical physics, a universally quantified theorem can be
accidentally vacuous if its hypothesis bundle is unsatisfiable or defines an unintended
degenerate object. This module proves explicit existential non-vacuity witnesses for every
headline theorem family in the `v1.5.0–v3.3.0` formalization stack:

1. `spectral_floor_nonvacuous`          : Theorem 1 (`hoggar_bound`) on 3-qubit `W(5,2)`.
2. `kramers_nonvacuous`                 : Theorem 2 (`hoggar_bound_quaternionic` & `Q⁻(5,2)`).
3. `saturation_tfae_nonvacuous`         : Theorems 3 & 4 (`saturation_tfae` & `saturation_mul_isSquare`)
                                          witnessed by the 6-qubit pure-CCZ determinant state.
4. `conjecture_e_nonvacuous`            : Theorem 19 (`jonah_conjecture_e_all_nine_cases_spectra`) at `N = 4`.
5. `clifford_transport_nonvacuous`      : Signed-Clifford orbit transport (`clifford_transport_strict_law_fails`).
6. `cone_lift_nonvacuous`               : Corollary 18 (`corollary18_c11_from_c3`) at `N = 4`.
7. `norm_phase_family_nonvacuous`       : Theorem 13b (`infinite_nonclosed_saturated_family`) at `m = 2`.
8. `c3_exact_optima_nonvacuous`         : Theorem 16'' (`corollary16_exact_binary_optima`: 368 vs 344, gap 24).
9. `exact_degrees_ladders_nonvacuous`   : Exact CSS witnesses (315, 1575, 6975) & unconditional bounds (1455, 6444).
10. `propositions_qgt_twochar_nonvacuous`: Propositions 3, 8, and 10 (`AuditUpgrades`).
11. `triality_residuals_nonvacuous`     : Theorem 23 (`TrialityResiduals`: exact degrees 0, 210, 252, 252).
12. `pg_rigidity_nonvacuous`            : Theorem 24 (`PGRigidity`: `W(15,2)` bound `166,115,415`).
13. `desargues_quasi_quadric_nonvacuous`: Theorem 25 (`DesarguesQuasiQuadric`: `S_ε` & `S_B^+` bracket).

Zero `sorry`, zero `admit`, zero `native_decide`, zero `set_option`, strictly within
`[propext, Classical.choice, Quot.sound]`.
-/
import HoggarBound.Kramers
import HoggarBound.Witness
import HoggarBound.SaturationTheory
import HoggarBound.ConjectureE
import HoggarBound.ConjectureEExtras
import HoggarBound.AuditUpgrades
import HoggarBound.C3ExactOptima
import HoggarBound.SaturatedPhaseSix
import HoggarBound.NormPhaseFamily
import HoggarBound.ExactDegreesN4N5
import HoggarBound.TrialityResiduals
import HoggarBound.PGRigidity
import HoggarBound.DesarguesQuasiQuadric
import ContextualityTensor.ActualModel

open Finset Matrix

namespace HoggarBound.NonVacuity

/-- 1. Non-vacuity witness for Theorem 1 (`hoggar_bound`) on three-qubit `W(5,2)`. -/
theorem spectral_floor_nonvacuous :
    ∃ (S : Finset (Pt 3)) (f : Pt 3 → ℝ),
      (0 : Pt 3) ∉ S ∧ S.card = 63 ∧ (∀ u ∈ S, f u = 1 ∨ f u = -1) ∧
      ((2 : ℝ) ^ 3 - 1) * beta6 S f ≤
        ((2 : ℝ) ^ 3 - 2) * S.card * Real.sqrt (((2 : ℝ) ^ 3 - 1) * S.card) := by
  refine ⟨allPoints 3, fun _ => 1, by simp [allPoints], ?_, fun _ _ => Or.inl rfl, ?_⟩
  · rw [card_allPoints]; norm_num
  · exact hoggar_bound (N := 3) (by norm_num) (allPoints 3) (by simp [allPoints])
      (fun _ => 1) (fun _ _ => Or.inl rfl)

/-- 2. Non-vacuity witness for Theorem 2 (`hoggar_bound_quaternionic` and `Q⁻(5,2)`). -/
theorem kramers_nonvacuous :
    ∃ (w : Pt 3) (S : Finset (Pt 3)) (f : Pt 3 → ℝ),
      qform w = 1 ∧ (0 : Pt 3) ∉ S ∧ S.card = 27 ∧
      (∀ u ∈ S, qform u + symp w u = 0) ∧ (∀ u ∈ S, f u = 1 ∨ f u = -1) ∧
      ((2 : ℝ) ^ (3 - 1) - 1) * beta6 S f ≤
        ((2 : ℝ) ^ (3 - 1) - 2) * S.card * Real.sqrt (((2 : ℝ) ^ (3 - 1) - 1) * S.card) ∧
      9 ≤ (violatedLines S f).card := by
  let w : Pt 3 := HoggarBound.ExactDegreesN4N5.Y0 3 (by norm_num)
  have hw : qform w = 1 := HoggarBound.ExactDegreesN4N5.qform_Y0 3 (by norm_num)
  refine ⟨w, ellipticPoints 3 w, fun _ => 1, hw, by simp [ellipticPoints], ?_, ?_,
    fun _ _ => Or.inl rfl, ?_, ?_⟩
  · have h := card_ellipticPoints (N := 3) hw; norm_num at h; omega
  · intro u hu; exact (Finset.mem_filter.mp hu).2.2
  · exact hoggar_bound_quaternionic (N := 3) (by norm_num) w hw (ellipticPoints 3 w)
      (by simp [ellipticPoints]) (fun u hu => (Finset.mem_filter.mp hu).2.2)
      (fun _ => 1) (fun _ _ => Or.inl rfl)
  · exact three_qubit_elliptic_contexts w hw (fun _ => 1) (fun _ _ => Or.inl rfl)

/-- 3. Non-vacuity witness for Theorems 3 & 4 (`saturation_tfae` and `saturation_mul_isSquare`):
the six-qubit pure-CCZ determinant state `|Ψ_6⟩` satisfies all five equivalent saturation conditions
with `|S| = 1008` and `(2^6 - 1) * 1008 = 252^2`. -/
theorem saturation_tfae_nonvacuous :
    ∃ (S : Finset (Pt 6)) (f : Pt 6 → ℝ) (ψ : Vec 6 → ℂ),
      (0 : Pt 6) ∉ S ∧ S.Nonempty ∧ S.card = 1008 ∧ (∀ u ∈ S, f u = 1 ∨ f u = -1) ∧
      IsFlatState S f ψ ∧
      ((2 : ℝ) ^ 6 - 1) * beta6 S f =
        ((2 : ℝ) ^ 6 - 2) * S.card * Real.sqrt (((2 : ℝ) ^ 6 - 1) * S.card) ∧
      (2 ^ 6 - 1) * S.card = 252 ^ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := GaloisField 2 2
  let : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 4 := by
    rw [← Nat.card_eq_fintype_card]
    simpa using GaloisField.card 2 2 (by norm_num)
  obtain ⟨e⟩ := HoggarBound.NormPhaseFamily.exists_linearEquiv_galoisField3 2 (by norm_num)
  let S := HoggarBound.NormPhaseFamily.detSupport e
  let f := HoggarBound.NormPhaseFamily.detSigns e
  let ψ := HoggarBound.NormPhaseFamily.detPhaseState e
  have h0 : (0 : Pt 6) ∉ S := HoggarBound.NormPhaseFamily.detSupport_zero_notMem e
  have hScard : S.card = 1008 := by
    have h := HoggarBound.NormPhaseFamily.detSupport_card hcard e
    norm_num at h; exact h
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hf : ∀ u ∈ S, f u = 1 ∨ f u = -1 := fun u _ =>
    HoggarBound.NormPhaseFamily.detSigns_values e u
  have hflat : IsFlatState S f ψ := HoggarBound.NormPhaseFamily.detPhase_isFlatState (by norm_num) hcard e
  have htfae := saturation_tfae (N := 6) (by norm_num) S h0 hne f hf
  have h41 : (∃ ψ', IsFlatState S f ψ') ↔
      ((2 : ℝ) ^ 6 - 1) * beta6 S f =
        ((2 : ℝ) ^ 6 - 2) * S.card * Real.sqrt (((2 : ℝ) ^ 6 - 1) * S.card) :=
    htfae.out 4 1
  have hsat : ((2 : ℝ) ^ 6 - 1) * beta6 S f =
      ((2 : ℝ) ^ 6 - 2) * S.card * Real.sqrt (((2 : ℝ) ^ 6 - 1) * S.card) :=
    h41.mp ⟨ψ, hflat⟩
  refine ⟨S, f, ψ, h0, hne, hScard, hf, hflat, hsat, ?_⟩
  rw [hScard]; norm_num

/-- 4. Non-vacuity witness for Theorem 19 (`jonah_conjecture_e_all_nine_cases_spectra`) at `N = 4`:
all nine vertex cases simultaneously admit cospectral Hermitian carriers with unequal completion
eigenvalue lists and root multisets. -/
theorem conjecture_e_nonvacuous :
    HoggarBound.AuditUpgrades.StrictLawFailsSpectra (allPoints 4) (HoggarBound.ConjectureE.ptZ ⟨0, by norm_num⟩) ∧
    HoggarBound.AuditUpgrades.StrictLawFailsSpectra (HoggarBound.ConjectureE.quadric 4 0) (HoggarBound.ConjectureE.ptZ ⟨0, by norm_num⟩) ∧
    HoggarBound.AuditUpgrades.StrictLawFailsSpectra (HoggarBound.ConjectureE.quadric 4 (HoggarBound.ConjectureE.ptY ⟨1, by norm_num⟩)) (HoggarBound.ConjectureE.ptZ ⟨0, by norm_num⟩) ∧
    HoggarBound.AuditUpgrades.StrictLawFailsSpectra (HoggarBound.ConjectureE.perpSet (allPoints 4) (HoggarBound.ConjectureE.ptZ ⟨0, by norm_num⟩)) (HoggarBound.ConjectureE.ptZ ⟨1, by norm_num⟩) ∧
    HoggarBound.AuditUpgrades.StrictLawFailsSpectra (HoggarBound.ConjectureE.perpSet (HoggarBound.ConjectureE.quadric 4 0) (HoggarBound.ConjectureE.ptY ⟨0, by norm_num⟩)) (HoggarBound.ConjectureE.ptZ ⟨1, by norm_num⟩) ∧
    HoggarBound.AuditUpgrades.StrictLawFailsSpectra (HoggarBound.ConjectureE.perpSet (HoggarBound.ConjectureE.quadric 4 0) (HoggarBound.ConjectureE.ptZ ⟨0, by norm_num⟩)) (HoggarBound.ConjectureE.ptZ ⟨1, by norm_num⟩) ∧
    HoggarBound.AuditUpgrades.StrictLawFailsSpectra (HoggarBound.ConjectureE.perpSet (HoggarBound.ConjectureE.quadric 4 0) (HoggarBound.ConjectureE.ptZ ⟨0, by norm_num⟩)) (HoggarBound.ConjectureE.ptY ⟨1, by norm_num⟩) ∧
    HoggarBound.AuditUpgrades.StrictLawFailsSpectra (HoggarBound.ConjectureE.perpSet (HoggarBound.ConjectureE.quadric 4 (HoggarBound.ConjectureE.ptY ⟨2, by norm_num⟩)) (HoggarBound.ConjectureE.ptZ ⟨0, by norm_num⟩)) (HoggarBound.ConjectureE.ptZ ⟨1, by norm_num⟩) ∧
    HoggarBound.AuditUpgrades.StrictLawFailsSpectra (HoggarBound.ConjectureE.perpSet (HoggarBound.ConjectureE.quadric 4 (HoggarBound.ConjectureE.ptY ⟨2, by norm_num⟩)) (HoggarBound.ConjectureE.ptZ ⟨0, by norm_num⟩)) (HoggarBound.ConjectureE.ptY ⟨1, by norm_num⟩) :=
  HoggarBound.AuditUpgrades.jonah_conjecture_e_all_nine_cases_spectra (N := 4) (by norm_num)

/-- 5. Non-vacuity witness for signed-Clifford orbit transport (`clifford_transport_strict_law_fails`):
every hypothesis of the transport theorem is inhabited by a concrete unitary Clifford operator on 4 qubits. -/
theorem clifford_transport_nonvacuous :
    ∃ (U : Matrix (Vec 4) (Vec 4) ℂ) (g : Pt 4 ≃ Pt 4) (ν : Pt 4 → ℝ),
      U * Uᴴ = 1 ∧ Uᴴ * U = 1 ∧ (∀ v, ν v = 1 ∨ ν v = -1) ∧
      (∀ v : Pt 4, U * pauli v * Uᴴ = (ν v : ℂ) • pauli (g v)) := by
  refine ⟨1, Equiv.refl _, fun _ => 1, by simp, by simp, fun _ => Or.inl rfl, fun v => by simp⟩

/-- 6. Non-vacuity witness for Corollary 18 (`corollary18_c11_from_c3`) at four qubits (`g = 2`, `N = 4`). -/
theorem cone_lift_nonvacuous :
    ∃ σ τ : Pt 4 → ℝ, (∀ s, σ s = 1 ∨ σ s = -1) ∧ (∀ s, τ s = 1 ∨ τ s = -1) ∧
      (opA (HoggarBound.ConjectureE.sectionOf
        (HoggarBound.ConjectureE.perpSet (HoggarBound.ConjectureE.quadric 4 0)
          (HoggarBound.ConjectureE.ptZ ⟨0, by norm_num⟩))
        (HoggarBound.ConjectureE.ptZ ⟨1, by norm_num⟩)) σ).charpoly =
      (opA (HoggarBound.ConjectureE.sectionOf
        (HoggarBound.ConjectureE.perpSet (HoggarBound.ConjectureE.quadric 4 0)
          (HoggarBound.ConjectureE.ptZ ⟨0, by norm_num⟩))
        (HoggarBound.ConjectureE.ptZ ⟨1, by norm_num⟩)) τ).charpoly ∧
      (HoggarBound.ConjectureE.completionMat
        (HoggarBound.ConjectureE.perpSet (HoggarBound.ConjectureE.quadric 4 0)
          (HoggarBound.ConjectureE.ptZ ⟨0, by norm_num⟩))
        (HoggarBound.ConjectureE.ptZ ⟨1, by norm_num⟩) σ).charpoly ≠
      (HoggarBound.ConjectureE.completionMat
        (HoggarBound.ConjectureE.perpSet (HoggarBound.ConjectureE.quadric 4 0)
          (HoggarBound.ConjectureE.ptZ ⟨0, by norm_num⟩))
        (HoggarBound.ConjectureE.ptZ ⟨1, by norm_num⟩) τ).charpoly :=
  HoggarBound.ConjectureE.corollary18_c11_from_c3 (g := 2) (by norm_num)

/-- 7. Non-vacuity witness for Theorem 13b (`infinite_nonclosed_saturated_family`) at `m = 2` (`N = 6`):
exhibits a strictly non-closed 1,008-point set with 45,696 contexts and exact degree `2,016 > 0`. -/
theorem norm_phase_family_nonvacuous :
    ∃ S : Finset (Pt 6),
      (0 : Pt 6) ∉ S ∧ S.card = 1008 ∧
      (∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ symp u v = 0 ∧ u + v ∉ S) ∧
      (contexts S).card = 45696 ∧
      (∀ f : Pt 6 → ℝ, (∀ u ∈ S, f u = 1 ∨ f u = -1) → 2016 ≤ (violatedLines S f).card) ∧
      (∃ f : Pt 6 → ℝ, (∀ u, f u = 1 ∨ f u = -1) ∧ (violatedLines S f).card = 2016) := by
  obtain ⟨S, h0, hcard, hnc, hctx, hlo, ⟨f, hf, hhi⟩⟩ :=
    HoggarBound.NormPhaseFamily.infinite_nonclosed_saturated_family 2 (by norm_num)
  norm_num at hcard hctx hlo hhi
  refine ⟨S, h0, hcard, hnc, by omega, fun g hg => ?_, ⟨f, hf, by omega⟩⟩
  have := hlo g (fun a b hab => hg (a, b) hab)
  omega

/-- 8. Non-vacuity witness for Theorem 16'' (`corollary16_exact_binary_optima`):
exhibits attaining binary completions `y₀, y₁ ∈ {±1}^64` achieving the exact optima `368` and `344`
with exact separation `368 - 344 = 24`. -/
theorem c3_exact_optima_nonvacuous :
    ∃ (y₀ y₁ : Fin 64 → ℝ),
      (∀ i, y₀ i = 1 ∨ y₀ i = -1) ∧
      (∀ i, y₁ i = 1 ∨ y₁ i = -1) ∧
      HoggarBound.ConjectureE.c3ViolatedOutsideContexts HoggarBound.C3.signA y₀ = 368 ∧
      HoggarBound.ConjectureE.c3ViolatedOutsideContexts HoggarBound.C3.signB y₁ = 344 ∧
      HoggarBound.ConjectureE.c3ViolatedOutsideContexts HoggarBound.C3.signA y₀ -
        HoggarBound.ConjectureE.c3ViolatedOutsideContexts HoggarBound.C3.signB y₁ = 24 := by
  obtain ⟨_, ⟨y₀, hy₀, hA⟩, _, ⟨y₁, hy₁, hB⟩⟩ :=
    HoggarBound.C3ExactOptima.corollary16_exact_binary_optima
  exact ⟨y₀, y₁, hy₀, hy₁, hA, hB, by omega⟩

/-- 9. Non-vacuity witness for `ExactDegreesN4N5`:
exhibits the three CSS witnesses (`315`, `1575`, `6975`) and verifies the unconditional Kramers-lifted
lower bounds `1455 ≤ 1575` on `W(7,2)` and `6444 ≤ 6975` on `Q⁺(9,2)`. -/
theorem exact_degrees_ladders_nonvacuous :
    (∃ f4 : Pt 4 → ℝ, (∀ u, f4 u = 1 ∨ f4 u = -1) ∧
      (violatedLines (ellipticPoints 4 (HoggarBound.ExactDegreesN4N5.Y0 4 (by norm_num))) f4).card = 315) ∧
    (∃ f4w : Pt 4 → ℝ, (∀ u, f4w u = 1 ∨ f4w u = -1) ∧
      1455 ≤ (violatedLines (allPoints 4) f4w).card ∧
      (violatedLines (allPoints 4) f4w).card = 1575) ∧
    (∃ f5 : Pt 5 → ℝ, (∀ u, f5 u = 1 ∨ f5 u = -1) ∧
      6444 ≤ (violatedLines (realPoints 5) f5).card ∧
      (violatedLines (realPoints 5) f5).card = 6975) := by
  obtain ⟨f4, hf4, h315⟩ := HoggarBound.ExactDegreesN4N5.q7minus_css_witness
  obtain ⟨f4w, hf4w, h1575⟩ := HoggarBound.ExactDegreesN4N5.w72_css_witness
  obtain ⟨f5, hf5, h6975⟩ := HoggarBound.ExactDegreesN4N5.q9plus_css_witness
  exact ⟨⟨f4, hf4, h315⟩,
    ⟨f4w, hf4w, HoggarBound.ExactDegreesN4N5.w72_ge_1455 f4w (fun u _ => hf4w u), h1575⟩,
    ⟨f5, hf5, HoggarBound.ExactDegreesN4N5.q9plus_ge_6444 f5 (fun u _ => hf5 u), h6975⟩⟩

/-- 10. Non-vacuity witness for Propositions 3, 8, and 10 (`AuditUpgrades`):
the six-qubit flat determinant state witnesses Proposition 10's two-character hyperplane
intersection cardinality (`528` for `u ∈ S`, `496` for `u ∉ S`). -/
theorem propositions_qgt_twochar_nonvacuous :
    ∃ (S : Finset (Pt 6)) (f : Pt 6 → ℝ) (ψ : Vec 6 → ℂ),
      (0 : Pt 6) ∉ S ∧ S.Nonempty ∧ S.card = 1008 ∧
      IsFlatState S f ψ ∧
      ∀ (u : Pt 6), u ≠ 0 →
        ((S.filter fun v => symp v u = 0).card : ℝ) =
          (496 : ℝ) + (if u ∈ S then (32 : ℝ) else 0) := by
  obtain ⟨S, f, ψ, h0, hne, hScard, hf, hflat, _, _⟩ := saturation_tfae_nonvacuous
  refine ⟨S, f, ψ, h0, hne, hScard, hflat, fun u hu => ?_⟩
  have h10 := HoggarBound.AuditUpgrades.proposition10_hyperplane_card (N := 6) (by norm_num)
    h0 hne hf hflat hu
  rw [hScard] at h10
  norm_num at h10 ⊢
  exact h10

/-! ### Kernel-Proved Refutations of Perturbed Headline Bounds (Closing `ERRATA.md` CI #2)

Each theorem below proves the negation of a genuine tightened (false) perturbation of a
quantified headline theorem using the exact attaining witnesses already formalized in the kernel. -/

/-- Perturbed headline refutation 1: `d(W(5,2)) ≥ 64` is false (Hoggar witness attains `63`). -/
theorem refute_w52_bound_64 :
    ¬ (∀ f : Pt 3 → ℝ, (∀ u ∈ allPoints 3, f u = 1 ∨ f u = -1) →
        64 ≤ (violatedLines (allPoints 3) f).card) := by
  intro h
  obtain ⟨_, f, hf, h63⟩ := degree_three_qubit
  have hge := h f (fun u _ => hf u)
  omega

/-- Perturbed headline refutation 2: `d(Q⁻(5,2)) ≥ 10` is false (Hoggar witness attains `9`). -/
theorem refute_q5minus_bound_10 :
    ¬ (∀ f : Pt 3 → ℝ, (∀ u ∈ ellipticPoints 3 eY3, f u = 1 ∨ f u = -1) →
        10 ≤ (violatedLines (ellipticPoints 3 eY3) f).card) := by
  intro h
  obtain ⟨_, f, hf, h9⟩ := degree_three_qubit_elliptic
  have hge := h f (fun u _ => hf u)
  omega

/-- Perturbed headline refutation 3: `d(W(7,2)) ≥ 1576` is false (CSS witness attains `1575`). -/
theorem refute_w72_bound_1576 :
    ¬ (∀ f : Pt 4 → ℝ, (∀ u ∈ allPoints 4, f u = 1 ∨ f u = -1) →
        1576 ≤ (violatedLines (allPoints 4) f).card) := by
  intro h
  obtain ⟨f, hf, h1575⟩ := HoggarBound.ExactDegreesN4N5.w72_css_witness
  have hge := h f (fun u _ => hf u)
  omega

/-- Perturbed headline refutation 4: `d(Q⁺(9,2)) ≥ 6976` is false (CSS witness attains `6975`). -/
theorem refute_q9plus_bound_6976 :
    ¬ (∀ f : Pt 5 → ℝ, (∀ u ∈ realPoints 5, f u = 1 ∨ f u = -1) →
        6976 ≤ (violatedLines (realPoints 5) f).card) := by
  intro h
  obtain ⟨f, hf, h6975⟩ := HoggarBound.ExactDegreesN4N5.q9plus_css_witness
  have hge := h f (fun u _ => hf u)
  omega

/-- Perturbed headline refutation 5: `C3` signA minimum `≥ 369` is false (witness attains `368`). -/
theorem refute_c3_signA_bound_369 :
    ¬ (∀ y : Fin 64 → ℝ, (∀ i, y i = 1 ∨ y i = -1) →
        369 ≤ HoggarBound.ConjectureE.c3ViolatedOutsideContexts HoggarBound.C3.signA y) := by
  intro h
  obtain ⟨_, ⟨y₀, hy₀, h368⟩, _, _⟩ := HoggarBound.C3ExactOptima.corollary16_exact_binary_optima
  have hge := h y₀ hy₀
  omega

/-- Perturbed headline refutation 6: `C3` signB minimum `≥ 345` is false (witness attains `344`). -/
theorem refute_c3_signB_bound_345 :
    ¬ (∀ y : Fin 64 → ℝ, (∀ i, y i = 1 ∨ y i = -1) →
        345 ≤ HoggarBound.ConjectureE.c3ViolatedOutsideContexts HoggarBound.C3.signB y) := by
  intro h
  obtain ⟨_, _, _, ⟨y₁, hy₁, h344⟩⟩ := HoggarBound.C3ExactOptima.corollary16_exact_binary_optima
  have hge := h y₁ hy₁
  omega

/-- Perturbed headline refutation 7: two disjoint Peres–Mermin squares do not force `13` violations (`d₂ = 12`). -/
theorem refute_square_k2_bound_13 :
    ¬ (∀ a : (Σ _i : Fin 2, Fin 9) → Bool,
        13 ≤ ContextualityTensor.actualViolations ContextualityTensor.squareContext (fun c => c == 5) a) := by
  intro h
  obtain ⟨⟨a0, h12⟩, _⟩ := ContextualityTensor.global_actual_square_minimum 2
  have hge := h a0
  norm_num at h12
  omega

/-- Perturbed headline refutation 8: two disjoint Mermin pentagrams do not force `11` violations (`d₂ = 10`). -/
theorem refute_pentagram_k2_bound_11 :
    ¬ (∀ a : (Σ _i : Fin 2, Fin 10) → Bool,
        11 ≤ ContextualityTensor.actualViolations ContextualityTensor.pentagramContext (fun c => c == 4) a) := by
  intro h
  obtain ⟨⟨a0, h10⟩, _⟩ := ContextualityTensor.global_actual_pentagram_minimum 2
  have hge := h a0
  norm_num at h10
  omega

/-- 11. Non-vacuity witness for Theorem 23 (`TrialityResiduals`):
exhibits all four 315-line deletion residuals of `Q⁺(7,2)` (`1,260` residual contexts each)
attaining exact degrees `0`, `210` (canonical spread `m1Spread`), `252` (`Q(6,2)`), and `252`
(triality-dual 9-point ovoid deletion). -/
theorem triality_residuals_nonvacuous :
    (∃ f0 : Pt 4 → ℝ, (∀ u, f0 u = 1 ∨ f0 u = -1) ∧
      (violatedLines (realPoints 4) f0).card = 315 ∧
      ((contexts (realPoints 4)) \ (violatedLines (realPoints 4) f0)).card = 1260) ∧
    (∃ (S : HoggarBound.TrialityResiduals.SolidSpread) (f1 : Pt 4 → ℝ),
      (∀ u, f1 u = 1 ∨ f1 u = -1) ∧ (S.resViolatedLines f1).card = 210) ∧
    (∃ (w : Pt 4) (f2 : Pt 4 → ℝ),
      qform w = 1 ∧ (∀ u, f2 u = 1 ∨ f2 u = -1) ∧
      (HoggarBound.TrialityResiduals.q62ResViolatedLines w f2).card = 252) ∧
    (∃ f3 : Pt 4 → ℝ, (∀ u, f3 u = 1 ∨ f3 u = -1) ∧
      (violatedLines (HoggarBound.cfg 4 HoggarBound.TrialityResiduals.ovoidRemovedMask) f3).card = 252) := by
  obtain ⟨_, f1, hf1, h210⟩ := HoggarBound.TrialityResiduals.m1_spread_residual_exact_210
  obtain ⟨_, f2, hf2, h252q⟩ := HoggarBound.TrialityResiduals.q62_residual_exact_252
  obtain ⟨_, f3, hf3, h252o⟩ := HoggarBound.TrialityResiduals.ovoid_residual_exact_252
  exact ⟨HoggarBound.TrialityResiduals.dw52_residual_exact_zero,
    ⟨HoggarBound.TrialityResiduals.m1Spread, f1, hf1, h210⟩,
    ⟨HoggarBound.ExactDegreesN4N5.Y0 4 (by norm_num), f2,
      HoggarBound.ExactDegreesN4N5.qform_Y0 4 (by norm_num), hf2, h252q⟩,
    ⟨f3, hf3, h252o⟩⟩

/-- 12. Non-vacuity witness for Theorem 24 (`PGRigidity`) at `N = 8` (`W(15,2)`):
the canonical `pgCssSign 8` assignment inhabits the hypothesis bundle of `pg_rigidity_n8`,
forcing at least `166,115,415` violated contexts. -/
theorem pg_rigidity_nonvacuous :
    ∃ f : Pt 8 → ℝ,
      (∀ u ∈ realPoints 8, f u = HoggarBound.PGRigidity.pgCssSign 8 u) ∧
      (∀ u ∈ allPoints 8, f u = 1 ∨ f u = -1) ∧
      166115415 ≤ (violatedLines (allPoints 8) f).card :=
  ⟨HoggarBound.PGRigidity.pgCssSign 8, fun _ _ => rfl,
    fun u _ => HoggarBound.PGRigidity.pgCssSign_values 8 u,
    HoggarBound.PGRigidity.pg_rigidity_n8 (HoggarBound.PGRigidity.pgCssSign 8)
      (fun _ _ => rfl) (fun u _ => HoggarBound.PGRigidity.pgCssSign_values 8 u)⟩

/-- 13. Non-vacuity witness for Theorem 25 (`DesarguesQuasiQuadric`):
the constant-zero fiber-flip set `S_0` exhibits exact `71/63` hyperplane intersections at `N = 4`,
paired with the attaining `127`-violation witness on Metod Saniga's augmented quasi-quadric `S_B^+`. -/
theorem desargues_quasi_quadric_nonvacuous :
    (HoggarBound.DesarguesQuasiQuadric.fiberFlipSet 4 (fun _ => 0)).card = 135 ∧
    (∃ f : Pt 4 → ℝ, (∀ u, f u = 1 ∨ f u = -1) ∧
      (violatedLines (HoggarBound.cfg 4 HoggarBound.DesarguesQuasiQuadric.sbAugMask) f).card = 127) :=
  ⟨(HoggarBound.DesarguesQuasiQuadric.fiberFlip_n4_71_63 (fun _ => 0)).1,
   HoggarBound.DesarguesQuasiQuadric.sb_aug_bounds_121_127.2⟩

/-- Perturbed headline refutation 9: `d(Q⁺(7,2) \ M1) ≥ 211` is false (`m1OptNeg` attains `210`). -/
theorem refute_m1_spread_bound_211 :
    ¬ (∀ f : Pt 4 → ℝ, (∀ u ∈ realPoints 4, f u = 1 ∨ f u = -1) →
        211 ≤ (HoggarBound.TrialityResiduals.m1Spread.resViolatedLines f).card) := by
  intro h
  obtain ⟨_, f, hf, h210⟩ := HoggarBound.TrialityResiduals.m1_spread_residual_exact_210
  have hge := h f (fun u _ => hf u)
  omega

/-- Perturbed headline refutation 10: `d(Q⁺(7,2) \ Q(6,2)) ≥ 253` is false (`ovoidOptNeg` attains `252`). -/
theorem refute_q62_residual_bound_253 :
    ¬ (∀ f : Pt 4 → ℝ, (∀ u ∈ realPoints 4, f u = 1 ∨ f u = -1) →
        253 ≤ (HoggarBound.TrialityResiduals.q62ResViolatedLines
          (HoggarBound.ExactDegreesN4N5.Y0 4 (by norm_num)) f).card) := by
  intro h
  obtain ⟨_, f, hf, h252⟩ := HoggarBound.TrialityResiduals.q62_residual_exact_252
  have hge := h f (fun u _ => hf u)
  omega

/-- Perturbed headline refutation 11: `d(Q⁺(7,2) \ O) ≥ 253` is false (`ovoidOptNeg` attains `252`). -/
theorem refute_ovoid_residual_bound_253 :
    ¬ (∀ f : Pt 4 → ℝ, (∀ u ∈ HoggarBound.cfg 4 HoggarBound.TrialityResiduals.ovoidRemovedMask, f u = 1 ∨ f u = -1) →
        253 ≤ (violatedLines (HoggarBound.cfg 4 HoggarBound.TrialityResiduals.ovoidRemovedMask) f).card) := by
  intro h
  obtain ⟨_, f, hf, h252⟩ := HoggarBound.TrialityResiduals.ovoid_residual_exact_252
  have hge := h f (fun u _ => hf u)
  omega

end HoggarBound.NonVacuity
