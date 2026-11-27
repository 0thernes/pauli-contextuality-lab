import ContextualityTensor.ActualModel
import HoggarBound.Pauli
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# General Track 2 Theory: Heterogeneous Endpoint Reduction, Mixed Families, General Contextual Seeds, Arbitrary-k Pauli Realizations, and Independent-Readout Noise Thresholds

Closes 100% of the remaining formalization boundary of `papers/disjoint-mermin/contextuality-tensor.tex`:
1. **Theorem 2 (`heterogeneous_endpoint_reduction`, Eq. 7):** Exact multilinear corner optimization
   for arbitrary heterogeneous signed configurations with attainable local augmented-score endpoints
   `l i ≤ 1 + β_i ≤ u i`.
2. **Mixed-family exact formula (`mixed_square_pentagram_minimum`, Eq. 12):** For `s` disjoint
   Peres–Mermin squares and `t` disjoint Mermin pentagrams, exact context count `7^s 6^t - 1`,
   sharp classical bound `5^s 4^t - 1`, and exact contextuality degree `(7^s 6^t - 5^s 4^t) / 2`.
3. **Theorem 5 (`general_seed_epsilon_tends_to_one`, Eq. 13):** For EVERY finite contextual signed
   seed `(V, C, seed, negative)` with distinct nonempty contexts, proves average local score `0`,
   `Fintype.card C ≥ 2`, `|1 + β(a)| ≤ m - 1`, and convergence `actualMinEpsilon seed negative k → 1`.
4. **Arbitrary-`k` quantum Pauli tensor-product realization (Eq. 5):** Using `HoggarBound.Pauli`,
   embeds `k` disjoint copies of the 2-qubit Peres–Mermin square into `2k` qubits and `k` disjoint
   copies of the 3-qubit Mermin pentagram into `3k` qubits, proving distinctness, non-identity,
   Hermiticity, involutivity, cross-register & within-context commutation, and exact union-context
   operator product `actualSign · I` for EVERY `k : ℕ`.
5. **Independent-readout noise model (Eqs. 14–16):** Exact predicted score
   `Q_k(p) = (1 + m (1 - 2p)^r)^k - 1`, `k`-independent square and pentagram violation thresholds,
   and vanishing normalized score `(Q_k(p)) / ((m + 1)^k - 1) → 0` for every fixed `p ∈ (0, 1/2]`.
-/

open Finset Filter Topology Matrix

namespace ContextualityTensor

/-! ### Part 1. Heterogeneous Full Union Construction & Theorem 2 (Endpoint Reduction, Eq. 7) -/

/-- All-empty context tuple for a heterogeneous family indexed by `I`. -/
def hetEmptyChoice {I : Type*} {C : I → Type*} : (i : I) → Option (C i) := fun _ => none

/-- Full nonempty-union context family over heterogeneous blocks `C i`. -/
def hetContexts {I : Type*} [Fintype I] [DecidableEq I]
    (C : I → Type*) [∀ i, Fintype (C i)] [∀ i, DecidableEq (C i)] :
    Finset ((i : I) → Option (C i)) :=
  univ.erase hetEmptyChoice

/-- Product context response for a heterogeneous tuple of local responses. -/
def hetContextValue {I : Type*} [Fintype I] {C : I → Type*}
    (f : (i : I) → C i → ℤ) (q : (i : I) → Option (C i)) : ℤ :=
  ∏ i, extend (f i) (q i)

/-- Classical correlation score summed over all nonempty heterogeneous union contexts. -/
def hetScore {I : Type*} [Fintype I] [DecidableEq I] {C : I → Type*}
    [∀ i, Fintype (C i)] [∀ i, DecidableEq (C i)]
    (f : (i : I) → C i → ℤ) : ℤ :=
  ∑ q ∈ hetContexts C, hetContextValue f q

/-- Count of violated contexts (`hetContextValue = -1`) in the heterogeneous union family. -/
def hetViolations {I : Type*} [Fintype I] [DecidableEq I] {C : I → Type*}
    [∀ i, Fintype (C i)] [∀ i, DecidableEq (C i)]
    (f : (i : I) → C i → ℤ) : ℕ :=
  ((hetContexts C).filter fun q => hetContextValue f q = -1).card

@[simp] theorem hetContextValue_empty {I : Type*} [Fintype I] {C : I → Type*}
    (f : (i : I) → C i → ℤ) :
    hetContextValue f hetEmptyChoice = 1 := by
  simp [hetContextValue, hetEmptyChoice, extend]

/-- Heterogeneous context-count product identity `L_* + 1 = ∏_i (|C_i| + 1)` (Eq. 3). -/
theorem hetContext_count {I : Type*} [Fintype I] [DecidableEq I]
    (C : I → Type*) [∀ i, Fintype (C i)] [∀ i, DecidableEq (C i)] :
    (hetContexts C).card + 1 = ∏ i, (Fintype.card (C i) + 1) := by
  have h := Finset.card_erase_add_one (s := (univ : Finset ((i : I) → Option (C i))))
    (mem_univ hetEmptyChoice)
  simpa [hetContexts, Fintype.card_pi, Fintype.card_option] using h

/-- Heterogeneous augmented-score factorization `1 + β_* = ∏_i (1 + β_i)` (Theorem 1, Eq. 6). -/
theorem hetScore_factorization {I : Type*} [Fintype I] [DecidableEq I] {C : I → Type*}
    [∀ i, Fintype (C i)] [∀ i, DecidableEq (C i)]
    (f : (i : I) → C i → ℤ) :
    hetScore f + 1 = ∏ i, (1 + ∑ c : C i, f i c) := by
  have he := Finset.sum_erase_add (s := (univ : Finset ((i : I) → Option (C i))))
    (f := hetContextValue f) (mem_univ hetEmptyChoice)
  have hp := Fintype.prod_sum (fun i q => extend (f i) q)
  simpa [hetScore, hetContexts, hetContextValue, hetEmptyChoice, extend, Fintype.sum_option,
    add_comm] using he.trans hp.symm

theorem abs_hetContextValue {I : Type*} [Fintype I] {C : I → Type*}
    (f : (i : I) → C i → ℤ) (hf : ∀ i c, |f i c| = 1) (q : (i : I) → Option (C i)) :
    |hetContextValue f q| = 1 := by
  rw [hetContextValue, abs_prod]
  apply Finset.prod_eq_one
  intro i _
  cases q i with
  | none => simp [extend]
  | some c => exact hf i c

/-- Heterogeneous score-violation relation `β_* = L_* - 2 v_*` (Eq. 1). -/
theorem hetScore_violations {I : Type*} [Fintype I] [DecidableEq I] {C : I → Type*}
    [∀ i, Fintype (C i)] [∀ i, DecidableEq (C i)]
    (f : (i : I) → C i → ℤ) (hf : ∀ i c, |f i c| = 1) :
    hetScore f = (hetContexts C).card - 2 * (hetViolations f : ℤ) := by
  have hv (q : (i : I) → Option (C i)) :
      hetContextValue f q = 1 - 2 * (if hetContextValue f q = -1 then (1 : ℤ) else 0) := by
    have h := abs_hetContextValue f hf q
    rcases (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp h with h | h <;> simp [h]
  unfold hetScore
  rw [Finset.sum_congr rfl (fun q _ => hv q)]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_boole, hetViolations]

/-- Multilinear products over a closed integer box `∏_i [l_i, u_i]` attain both their minimum
and maximum at corners `z_i ∈ {l_i, u_i}`. -/
theorem multilinear_box_extrema : ∀ (k : ℕ) (l u x : Fin k → ℤ),
    (∀ i, l i ≤ x i ∧ x i ≤ u i) →
    (∃ ε : Fin k → Bool, ∏ i, (if ε i then u i else l i) ≤ ∏ i, x i) ∧
    (∃ ε : Fin k → Bool, ∏ i, x i ≤ ∏ i, (if ε i then u i else l i))
  | 0, _, _, _, _ => ⟨⟨Fin.elim0, by simp⟩, ⟨Fin.elim0, by simp⟩⟩
  | k + 1, l, u, x, hx => by
    obtain ⟨⟨εmin, hmin⟩, ⟨εmax, hmax⟩⟩ :=
      multilinear_box_extrema k (l ∘ Fin.succ) (u ∘ Fin.succ) (x ∘ Fin.succ) (fun i => hx i.succ)
    have h0l : l 0 ≤ x 0 := (hx 0).1
    have h0u : x 0 ≤ u 0 := (hx 0).2
    set P : ℤ := ∏ i : Fin k, x i.succ
    set Pmin : ℤ := ∏ i : Fin k, if εmin i then u i.succ else l i.succ
    set Pmax : ℤ := ∏ i : Fin k, if εmax i then u i.succ else l i.succ
    constructor
    · by_cases hP : 0 ≤ P
      · by_cases hl0 : 0 ≤ l 0
        · refine ⟨Fin.cons false εmin, ?_⟩
          rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ, Bool.false_eq_true, ↓reduceIte]
          calc l 0 * Pmin ≤ l 0 * P := mul_le_mul_of_nonneg_left hmin hl0
            _ ≤ x 0 * P := mul_le_mul_of_nonneg_right h0l hP
        · refine ⟨Fin.cons false εmax, ?_⟩
          rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ, Bool.false_eq_true, ↓reduceIte]
          calc l 0 * Pmax ≤ l 0 * P := mul_le_mul_of_nonpos_left hmax (by omega)
            _ ≤ x 0 * P := mul_le_mul_of_nonneg_right h0l hP
      · by_cases hu0 : 0 ≤ u 0
        · refine ⟨Fin.cons true εmin, ?_⟩
          rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ, ↓reduceIte]
          calc u 0 * Pmin ≤ u 0 * P := mul_le_mul_of_nonneg_left hmin hu0
            _ ≤ x 0 * P := mul_le_mul_of_nonpos_right h0u (by omega)
        · refine ⟨Fin.cons true εmax, ?_⟩
          rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ, ↓reduceIte]
          calc u 0 * Pmax ≤ u 0 * P := mul_le_mul_of_nonpos_left hmax (by omega)
            _ ≤ x 0 * P := mul_le_mul_of_nonpos_right h0u (by omega)
    · by_cases hP : 0 ≤ P
      · by_cases hu0 : 0 ≤ u 0
        · refine ⟨Fin.cons true εmax, ?_⟩
          rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ, ↓reduceIte]
          calc x 0 * P ≤ u 0 * P := mul_le_mul_of_nonneg_right h0u hP
            _ ≤ u 0 * Pmax := mul_le_mul_of_nonneg_left hmax hu0
        · refine ⟨Fin.cons true εmin, ?_⟩
          rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ, ↓reduceIte]
          calc x 0 * P ≤ u 0 * P := mul_le_mul_of_nonneg_right h0u hP
            _ ≤ u 0 * Pmin := mul_le_mul_of_nonpos_left hmin (by omega)
      · by_cases hl0 : 0 ≤ l 0
        · refine ⟨Fin.cons false εmax, ?_⟩
          rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ, Bool.false_eq_true, ↓reduceIte]
          calc x 0 * P ≤ l 0 * P := mul_le_mul_of_nonpos_right h0l (by omega)
            _ ≤ l 0 * Pmax := mul_le_mul_of_nonneg_left hmax hl0
        · refine ⟨Fin.cons false εmin, ?_⟩
          rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ, Bool.false_eq_true, ↓reduceIte]
          calc x 0 * P ≤ l 0 * P := mul_le_mul_of_nonpos_right h0l (by omega)
            _ ≤ l 0 * Pmin := mul_le_mul_of_nonpos_left hmin (by omega)

/-- Maximum corner product `max_{ε : Fin k → Bool} ∏_i (if ε i then u i else l i)` (Eq. 7). -/
def cornerMax {k : ℕ} (l u : Fin k → ℤ) : ℤ :=
  ((univ : Finset (Fin k → Bool)).image fun ε => ∏ i, if ε i then u i else l i).max'
    (Finset.image_nonempty.mpr ⟨fun _ => true, mem_univ _⟩)

/-- **Theorem 2 (Endpoint reduction, Eq. 7):** For any `k` heterogeneous signed configurations
with attainable local augmented-score minimum `l i` and maximum `u i`, the global maximum
augmented score `B_* + 1` equals `cornerMax l u` and is attained by an independent tuple of
local assignments. -/
theorem heterogeneous_endpoint_reduction {k : ℕ}
    {C : Fin k → Type*} [∀ i, Fintype (C i)] [∀ i, DecidableEq (C i)]
    {A : Fin k → Type*} (R : (i : Fin k) → A i → C i → ℤ)
    (l u : Fin k → ℤ)
    (hbounds : ∀ i a, l i ≤ 1 + ∑ c, R i a c ∧ 1 + ∑ c, R i a c ≤ u i)
    (hattain : ∀ i, (∃ a, 1 + ∑ c, R i a c = l i) ∧ (∃ a, 1 + ∑ c, R i a c = u i)) :
    (∀ a : (i : Fin k) → A i, hetScore (fun i => R i (a i)) + 1 ≤ cornerMax l u) ∧
    (∃ a : (i : Fin k) → A i, hetScore (fun i => R i (a i)) + 1 = cornerMax l u) := by
  constructor
  · intro a
    rw [hetScore_factorization]
    obtain ⟨_, ε, hε⟩ := multilinear_box_extrema k l u (fun i => 1 + ∑ c, R i (a i) c)
      (fun i => hbounds i (a i))
    unfold cornerMax
    exact hε.trans (Finset.le_max' _ _ (Finset.mem_image_of_mem
      (fun ε : Fin k → Bool => ∏ i, if ε i then u i else l i) (mem_univ ε)))
  · have hmem := Finset.max'_mem
      ((univ : Finset (Fin k → Bool)).image fun ε => ∏ i, if ε i then u i else l i)
      (Finset.image_nonempty.mpr ⟨fun _ => true, mem_univ _⟩)
    obtain ⟨ε, _, hε⟩ := Finset.mem_image.mp hmem
    have hchoice : ∀ i : Fin k, ∃ a : A i, 1 + ∑ c, R i a c = if ε i then u i else l i := by
      intro i
      cases hεi : ε i with
      | false => simpa using (hattain i).1
      | true => simpa using (hattain i).2
    choose a ha using hchoice
    refine ⟨a, ?_⟩
    rw [hetScore_factorization]
    calc ∏ i, (1 + ∑ c, R i (a i) c)
        = ∏ i, (if ε i then u i else l i) := Finset.prod_congr rfl fun i _ => ha i
      _ = cornerMax l u := hε

/-! ### Part 2. Mixed-Family Exact Formula: `s` Squares and `t` Pentagrams (Eq. 12) -/

/-- Context index type for `s` Peres–Mermin squares (`inl`) and `t` Mermin pentagrams (`inr`). -/
def mixedContextType (s t : ℕ) : Fin s ⊕ Fin t → Type
  | Sum.inl _ => Fin 6
  | Sum.inr _ => Fin 5

instance (s t : ℕ) (i : Fin s ⊕ Fin t) : Fintype (mixedContextType s t i) := by
  cases i <;> dsimp [mixedContextType] <;> infer_instance

instance (s t : ℕ) (i : Fin s ⊕ Fin t) : DecidableEq (mixedContextType s t i) := by
  cases i <;> dsimp [mixedContextType] <;> infer_instance

/-- Local deterministic assignment type for `s` squares (`Fin 9 → Bool`) and `t` pentagrams (`Fin 10 → Bool`). -/
def mixedAssignType (s t : ℕ) : Fin s ⊕ Fin t → Type
  | Sum.inl _ => Fin 9 → Bool
  | Sum.inr _ => Fin 10 → Bool

/-- Local signed response function on each component of the mixed `(s, t)` family. -/
def mixedResponse (s t : ℕ) : (i : Fin s ⊕ Fin t) → mixedAssignType s t i → mixedContextType s t i → ℤ
  | Sum.inl _, a, c => squareResponse a c
  | Sum.inr _, a, c => pentagramResponse a c

theorem mixed_context_count (s t : ℕ) :
    (hetContexts (mixedContextType s t)).card + 1 = 7 ^ s * 6 ^ t := by
  rw [hetContext_count, Fintype.prod_sum_type]
  simp [mixedContextType]

theorem mixed_abs_response (s t : ℕ) (a : (i : Fin s ⊕ Fin t) → mixedAssignType s t i)
    (i : Fin s ⊕ Fin t) (c : mixedContextType s t i) :
    |mixedResponse s t i (a i) c| = 1 := by
  cases i with
  | inl _ => exact abs_response _ _ _
  | inr _ => exact abs_response _ _ _

theorem mixed_score_bound (s t : ℕ) (a : (i : Fin s ⊕ Fin t) → mixedAssignType s t i) :
    hetScore (fun i => mixedResponse s t i (a i)) ≤ 5 ^ s * 4 ^ t - 1 := by
  have hfac := hetScore_factorization (fun i => mixedResponse s t i (a i))
  have habs : |hetScore (fun i => mixedResponse s t i (a i)) + 1| ≤ 5 ^ s * 4 ^ t := by
    rw [hfac, abs_prod, Fintype.prod_sum_type]
    have h1 : (∏ i : Fin s, |1 + ∑ c : Fin 6, squareResponse (a (Sum.inl i)) c|) ≤ 5 ^ s := by
      calc _ ≤ ∏ _i : Fin s, (5 : ℤ) :=
            Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => square_local_bound _)
        _ = 5 ^ s := by simp
    have h2 : (∏ j : Fin t, |1 + ∑ c : Fin 5, pentagramResponse (a (Sum.inr j)) c|) ≤ 4 ^ t := by
      calc _ ≤ ∏ _j : Fin t, (4 : ℤ) :=
            Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun j _ => pentagram_local_bound _)
        _ = 4 ^ t := by simp
    have hnn1 : 0 ≤ ∏ i : Fin s, |1 + ∑ c : Fin 6, squareResponse (a (Sum.inl i)) c| :=
      Finset.prod_nonneg fun _ _ => abs_nonneg _
    have hnn2 : (0 : ℤ) ≤ 4 ^ t := by positivity
    simpa [mixedContextType, mixedResponse] using mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by positivity)
  have := le_abs_self (hetScore (fun i => mixedResponse s t i (a i)) + 1)
  linarith

/-- The all-`false` (`+1`) assignment across `s` squares and `t` pentagrams. -/
def mixedAllFalse (s t : ℕ) : (i : Fin s ⊕ Fin t) → mixedAssignType s t i
  | Sum.inl _ => fun _ => false
  | Sum.inr _ => fun _ => false

theorem mixed_score_witness (s t : ℕ) :
    hetScore (fun i => mixedResponse s t i (mixedAllFalse s t i)) = 5 ^ s * 4 ^ t - 1 := by
  have hfac := hetScore_factorization (fun i => mixedResponse s t i (mixedAllFalse s t i))
  have hrhs : (∏ i : Fin s ⊕ Fin t,
      (1 + ∑ c : mixedContextType s t i, mixedResponse s t i (mixedAllFalse s t i) c)) =
      5 ^ s * 4 ^ t := by
    rw [Fintype.prod_sum_type]
    simp only [mixedContextType, mixedResponse, mixedAllFalse, square_local_witness,
      pentagram_local_witness]
    norm_num
  linarith

/-- **Mixed-family exact formula (Eq. 12):** For `s` disjoint Peres–Mermin squares and `t`
disjoint Mermin pentagrams, the context count is `7^s 6^t - 1`, the sharp classical bound is
`5^s 4^t - 1`, and the exact contextuality degree is `(7^s 6^t - 5^s 4^t) / 2`. -/
theorem mixed_square_pentagram_minimum (s t : ℕ) :
    (hetContexts (mixedContextType s t)).card + 1 = 7 ^ s * 6 ^ t ∧
    (∃ a : (i : Fin s ⊕ Fin t) → mixedAssignType s t i,
      hetViolations (fun i => mixedResponse s t i (a i)) = (7 ^ s * 6 ^ t - 5 ^ s * 4 ^ t) / 2) ∧
    (∀ a : (i : Fin s ⊕ Fin t) → mixedAssignType s t i,
      (7 ^ s * 6 ^ t - 5 ^ s * 4 ^ t) / 2 ≤
        hetViolations (fun i => mixedResponse s t i (a i))) := by
  have hcard : ((hetContexts (mixedContextType s t)).card : ℤ) + 1 = 7 ^ s * 6 ^ t := by
    exact_mod_cast mixed_context_count s t
  have hw_sv := hetScore_violations (fun i => mixedResponse s t i (mixedAllFalse s t i))
    (mixed_abs_response s t (mixedAllFalse s t))
  have hw_sc := mixed_score_witness s t
  have hw_two : 2 * (hetViolations (fun i => mixedResponse s t i (mixedAllFalse s t i)) : ℤ) =
      (7 : ℤ) ^ s * 6 ^ t - 5 ^ s * 4 ^ t := by linarith
  have hw_nat : hetViolations (fun i => mixedResponse s t i (mixedAllFalse s t i)) =
      (7 ^ s * 6 ^ t - 5 ^ s * 4 ^ t) / 2 := by
    have hi : (2 : ℤ) * hetViolations (fun i => mixedResponse s t i (mixedAllFalse s t i)) +
        5 ^ s * 4 ^ t = 7 ^ s * 6 ^ t := by linarith
    have hn : 2 * hetViolations (fun i => mixedResponse s t i (mixedAllFalse s t i)) +
        5 ^ s * 4 ^ t = 7 ^ s * 6 ^ t := by exact_mod_cast hi
    omega
  refine ⟨mixed_context_count s t, ⟨mixedAllFalse s t, hw_nat⟩, ?_⟩
  intro a
  have ha_sv := hetScore_violations (fun i => mixedResponse s t i (a i)) (mixed_abs_response s t a)
  have ha_bd := mixed_score_bound s t a
  have ha_two : (7 : ℤ) ^ s * 6 ^ t - 5 ^ s * 4 ^ t ≤
      2 * (hetViolations (fun i => mixedResponse s t i (a i)) : ℤ) := by linarith
  omega

/-! ### Part 3. Theorem 5 — General Finite Contextual Seed Asymptotic Limit (Eq. 13) -/

/-- Flip a single vertex `v₀` in a deterministic Boolean assignment. -/
def flipAt {V : Type*} [DecidableEq V] (v₀ : V) (a : V → Bool) : V → Bool :=
  fun v => if v = v₀ then !a v else a v

theorem flipAt_involutive {V : Type*} [DecidableEq V] (v₀ : V) :
    Function.Involutive (flipAt v₀) := by
  intro a
  funext v
  by_cases hv : v = v₀ <;> simp [flipAt, hv]

theorem sign_not (b : Bool) : sign (!b) = -sign b := by cases b <;> rfl

theorem response_flipAt {V : Type*} [DecidableEq V] {h : Finset V} {v₀ : V}
    (hv₀ : v₀ ∈ h) (neg : Bool) (a : V → Bool) :
    response (flipAt v₀ a) neg h = -response a neg h := by
  unfold response
  rw [← Finset.mul_prod_erase h _ hv₀, ← Finset.mul_prod_erase h _ hv₀]
  have herase : ∏ v ∈ h.erase v₀, sign (flipAt v₀ a v) = ∏ v ∈ h.erase v₀, sign (a v) := by
    refine Finset.prod_congr rfl fun v hv => ?_
    have hne : v ≠ v₀ := (Finset.mem_erase.mp hv).1
    simp [flipAt, hne]
  rw [herase]
  simp only [flipAt, ↓reduceIte, sign_not]
  ring

/-- Over all deterministic assignments `V → Bool`, every nonempty context has zero mean response. -/
theorem sum_response_eq_zero {V : Type*} [Fintype V] [DecidableEq V]
    {h : Finset V} (hne : h.Nonempty) (neg : Bool) :
    ∑ a : V → Bool, response a neg h = 0 := by
  obtain ⟨v₀, hv₀⟩ := hne
  have hbij : ∑ a : V → Bool, response (flipAt v₀ a) neg h = ∑ a : V → Bool, response a neg h := by
    refine Fintype.sum_equiv (Equiv.ofBijective (flipAt v₀) (flipAt_involutive v₀).bijective) _ _ ?_
    intro a; rfl
  have hneg : ∑ a : V → Bool, response (flipAt v₀ a) neg h = -∑ a : V → Bool, response a neg h := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => response_flipAt hv₀ neg a
  linarith

/-- Over all deterministic assignments, the total local score across nonempty contexts sums to zero. -/
theorem sum_local_score_eq_zero {C V : Type*} [Fintype C] [Fintype V] [DecidableEq V]
    (seed : C → Finset V) (negative : C → Bool) (hne : ∀ c, (seed c).Nonempty) :
    ∑ a : V → Bool, ∑ c : C, response a (negative c) (seed c) = 0 := by
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun c _ => sum_response_eq_zero (hne c) (negative c)

/-- Every finite seed with nonempty contexts admits a deterministic assignment with nonnegative score. -/
theorem exists_nonneg_local_score {C V : Type*} [Fintype C] [Fintype V] [DecidableEq V]
    (seed : C → Finset V) (negative : C → Bool) (hne : ∀ c, (seed c).Nonempty) :
    ∃ a : V → Bool, 0 ≤ ∑ c : C, response a (negative c) (seed c) := by
  by_contra h
  push Not at h
  have hneg : ∑ a : V → Bool, ∑ c : C, response a (negative c) (seed c) < 0 :=
    Finset.sum_neg (fun a _ => h a) ⟨fun _ => false, mem_univ _⟩
  have hzero := sum_local_score_eq_zero seed negative hne
  linarith

theorem response_le_one {V : Type*} [DecidableEq V] (a : V → Bool) (neg : Bool) (h : Finset V) :
    response a neg h ≤ 1 := by
  have := abs_response a neg h
  exact (abs_le.mp this.le).2

theorem neg_one_le_response {V : Type*} [DecidableEq V] (a : V → Bool) (neg : Bool) (h : Finset V) :
    -1 ≤ response a neg h := by
  have := abs_response a neg h
  exact (abs_le.mp this.le).1

/-- Contextuality (`∀ a, ∃ c, response = -1`) forces `β(a) ≤ |C| - 2` for every assignment. -/
theorem contextual_local_score_le {C V : Type*} [Fintype C] [DecidableEq C] [DecidableEq V]
    (seed : C → Finset V) (negative : C → Bool)
    (hctx : ∀ a : V → Bool, ∃ c : C, response a (negative c) (seed c) = -1)
    (a : V → Bool) :
    ∑ c : C, response a (negative c) (seed c) ≤ (Fintype.card C : ℤ) - 2 := by
  obtain ⟨c₀, hc₀⟩ := hctx a
  rw [← Finset.add_sum_erase _ _ (mem_univ c₀), hc₀]
  have hrest : ∑ c ∈ univ.erase c₀, response a (negative c) (seed c) ≤
      ∑ _c ∈ univ.erase c₀, (1 : ℤ) :=
    Finset.sum_le_sum fun c _ => response_le_one a (negative c) (seed c)
  have hcard : ((univ.erase c₀ : Finset C).card : ℤ) = (Fintype.card C : ℤ) - 1 := by
    have h1 := Finset.card_erase_add_one (s := (univ : Finset C)) (mem_univ c₀)
    have h2 : ((univ.erase c₀ : Finset C).card : ℤ) + 1 = Fintype.card C := by
      simpa using (show ((univ.erase c₀ : Finset C).card + 1 : ℤ) = Fintype.card C by exact_mod_cast h1)
    linarith
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hrest
  linarith

/-- Every finite contextual seed with nonempty contexts has at least `2` contexts (`m ≥ 2`). -/
theorem contextual_card_ge_two {C V : Type*} [Fintype C] [DecidableEq C]
    [Fintype V] [DecidableEq V] (seed : C → Finset V) (negative : C → Bool)
    (hne : ∀ c, (seed c).Nonempty)
    (hctx : ∀ a : V → Bool, ∃ c : C, response a (negative c) (seed c) = -1) :
    2 ≤ Fintype.card C := by
  obtain ⟨a₀, ha₀⟩ := exists_nonneg_local_score seed negative hne
  have hle := contextual_local_score_le seed negative hctx a₀
  omega

/-- Every finite contextual seed satisfies `|1 + β(a)| ≤ m - 1` for every assignment `a`. -/
theorem contextual_local_abs_bound {C V : Type*} [Fintype C] [DecidableEq C] [DecidableEq V]
    (seed : C → Finset V) (negative : C → Bool)
    (hctx : ∀ a : V → Bool, ∃ c : C, response a (negative c) (seed c) = -1)
    (a : V → Bool) :
    |1 + ∑ c : C, response a (negative c) (seed c)| ≤ (Fintype.card C : ℤ) - 1 := by
  have hub := contextual_local_score_le seed negative hctx a
  have hlb : -(Fintype.card C : ℤ) ≤ ∑ c : C, response a (negative c) (seed c) := by
    calc -(Fintype.card C : ℤ) = ∑ _c : C, (-1 : ℤ) := by simp
      _ ≤ ∑ c : C, response a (negative c) (seed c) :=
        Finset.sum_le_sum fun c _ => neg_one_le_response a (negative c) (seed c)
  rw [abs_le]
  constructor <;> linarith

/-- Genuine minimum-defined normalized ideal gap `ε_k = 2 d_k / |C_k|` for an arbitrary seed. -/
noncomputable def actualMinEpsilon {C V : Type*} [Fintype C] [DecidableEq C]
    [Fintype V] [DecidableEq V] (seed : C → Finset V) (negative : C → Bool) (k : ℕ) : ℝ :=
  2 * (actualMinViolations (k := k) seed negative : ℝ) / (actualContexts (k := k) seed).card

/-- **Theorem 5 (General finite contextual seed, Eq. 13):** For EVERY finite contextual signed
seed `(V, C, seed, negative)` with distinct nonempty contexts, the genuine minimum-defined
contextuality fraction `ε_k = 2 d_k / ((m + 1)^k - 1)` tends to `1` as `k → ∞`. -/
theorem general_seed_epsilon_tends_to_one {C V : Type*} [Fintype C] [DecidableEq C]
    [Fintype V] [DecidableEq V] (seed : C → Finset V) (negative : C → Bool)
    (hi : Function.Injective seed) (hne : ∀ c, (seed c).Nonempty)
    (hctx : ∀ a : V → Bool, ∃ c : C, response a (negative c) (seed c) = -1) :
    Tendsto (actualMinEpsilon seed negative) atTop (𝓝 1) := by
  set m : ℕ := Fintype.card C
  have hm2 : 2 ≤ m := contextual_card_ge_two seed negative hne hctx
  obtain ⟨a₀, ha₀⟩ := exists_nonneg_local_score seed negative hne
  have hlim_lo : Tendsto (fun k : ℕ => (((m : ℝ) + 1) ^ k - ((m : ℝ) - 1) ^ k) /
      (((m : ℝ) + 1) ^ k - 1)) atTop (𝓝 1) := by
    apply amplification_limit ((m : ℝ) + 1) ((m : ℝ) - 1)
    · have : (2 : ℝ) ≤ m := by exact_mod_cast hm2
      linarith
    · have : (2 : ℝ) ≤ m := by exact_mod_cast hm2
      linarith
    · linarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim_lo tendsto_const_nhds ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hcard_nat : (actualContexts (k := k) seed).card + 1 = (m + 1) ^ k :=
      actual_context_count seed hi hne
    have hcard_pos : (0 : ℝ) < (actualContexts (k := k) seed).card := by
      have hpow : 1 < (m + 1) ^ k := by
        calc 1 < m + 1 := by omega
          _ = (m + 1) ^ 1 := (pow_one _).symm
          _ ≤ (m + 1) ^ k := Nat.pow_le_pow_right (by omega) hk
      have hpos_nat : 0 < (actualContexts (k := k) seed).card := by omega
      exact_mod_cast hpos_nat
    have hcard_real : ((actualContexts (k := k) seed).card : ℝ) = ((m : ℝ) + 1) ^ k - 1 := by
      have h1 : ((actualContexts (k := k) seed).card : ℝ) + 1 = ((m : ℝ) + 1) ^ k := by
        exact_mod_cast hcard_nat
      linarith
    obtain ⟨amin, hamin⟩ := exists_actualMinViolations (k := k) seed negative
    have hsc_bd : actualScore seed negative amin ≤ ((m : ℤ) - 1) ^ k - 1 := by
      rw [actualScore_eq_score seed negative hi hne amin]
      exact score_upper_bound _ ((m : ℤ) - 1) (by omega)
        (fun i => contextual_local_abs_bound seed negative hctx (fun v => amin ⟨i, v⟩))
    have hsv : actualScore seed negative amin =
        (actualContexts (k := k) seed).card - 2 * (actualViolations seed negative amin : ℤ) := by
      rw [actualScore_eq_score seed negative hi hne amin,
          actualViolations_eq_violations seed negative hi hne amin,
          score_violations _ (fun i c => abs_response _ _ _)]
      congr 1
      unfold actualContexts
      rw [Finset.card_image_of_injective _ (unionContext_injective seed hi hne)]
    have hcard_int : ((actualContexts (k := k) seed).card : ℤ) + 1 = ((m : ℤ) + 1) ^ k := by
      exact_mod_cast hcard_nat
    have hviol_int : ((m : ℤ) + 1) ^ k - ((m : ℤ) - 1) ^ k ≤
        2 * (actualMinViolations (k := k) seed negative : ℤ) := by
      rw [← hamin]
      linarith
    have hviol_real : ((m : ℝ) + 1) ^ k - ((m : ℝ) - 1) ^ k ≤
        2 * (actualMinViolations (k := k) seed negative : ℝ) := by
      exact_mod_cast hviol_int
    unfold actualMinEpsilon
    rw [hcard_real] at hcard_pos ⊢
    exact div_le_div_of_nonneg_right hviol_real hcard_pos.le
  · filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hcard_nat : (actualContexts (k := k) seed).card + 1 = (m + 1) ^ k :=
      actual_context_count seed hi hne
    have hcard_pos : (0 : ℝ) < (actualContexts (k := k) seed).card := by
      have hpow : 1 < (m + 1) ^ k := by
        calc 1 < m + 1 := by omega
          _ = (m + 1) ^ 1 := (pow_one _).symm
          _ ≤ (m + 1) ^ k := Nat.pow_le_pow_right (by omega) hk
      have hpos_nat : 0 < (actualContexts (k := k) seed).card := by omega
      exact_mod_cast hpos_nat
    let aglob : (Σ _i : Fin k, V) → Bool := fun x => a₀ x.2
    have hsc_ge : 0 ≤ actualScore seed negative aglob := by
      rw [actualScore_eq_score seed negative hi hne aglob]
      have hfac := score_factorization (k := k) (fun (_ : Fin k) c => response a₀ (negative c) (seed c))
      have h1 : (1 : ℤ) ≤ ∏ _i : Fin k, (1 + ∑ c : C, response a₀ (negative c) (seed c)) := by
        calc (1 : ℤ) = ∏ _i : Fin k, (1 : ℤ) := by simp
          _ ≤ ∏ _i : Fin k, (1 + ∑ c : C, response a₀ (negative c) (seed c)) :=
            Finset.prod_le_prod₀ (fun _ _ => by norm_num) (fun _ _ => by linarith)
      linarith
    have hsv : actualScore seed negative aglob =
        (actualContexts (k := k) seed).card - 2 * (actualViolations seed negative aglob : ℤ) := by
      rw [actualScore_eq_score seed negative hi hne aglob,
          actualViolations_eq_violations seed negative hi hne aglob,
          score_violations _ (fun i c => abs_response _ _ _)]
      congr 1
      unfold actualContexts
      rw [Finset.card_image_of_injective _ (unionContext_injective seed hi hne)]
    have hmin_le : actualMinViolations (k := k) seed negative ≤
        actualViolations seed negative aglob := actualMinViolations_le seed negative aglob
    have hviol_ub_int : 2 * (actualMinViolations (k := k) seed negative : ℤ) ≤
        (actualContexts (k := k) seed).card := by
      have hmin_le_int : (actualMinViolations (k := k) seed negative : ℤ) ≤
          actualViolations seed negative aglob := by exact_mod_cast hmin_le
      linarith
    have hviol_ub_real : 2 * (actualMinViolations (k := k) seed negative : ℝ) ≤
        (actualContexts (k := k) seed).card := by
      exact_mod_cast hviol_ub_int
    unfold actualMinEpsilon
    exact (div_le_one hcard_pos).mpr hviol_ub_real

/-! ### Part 4. Arbitrary-`k` Pauli Tensor-Product Operator Realization (Eq. 5) -/

/-- Embed an `r`-qubit bit vector into register `i` of `k` disjoint `r`-qubit registers (`k * r` qubits). -/
def embedVec {k r : ℕ} (i : Fin k) (v : HoggarBound.Vec r) : HoggarBound.Vec (k * r) :=
  fun idx =>
    let p := finProdFinEquiv.symm idx
    if p.1 = i then v p.2 else 0

/-- Embed an `r`-qubit Pauli phase-space point `(a, c)` into register `i` of `k * r` qubits. -/
def embedPt {k r : ℕ} (i : Fin k) (u : HoggarBound.Pt r) : HoggarBound.Pt (k * r) :=
  (embedVec i u.1, embedVec i u.2)

theorem embedVec_zero {k r : ℕ} (i : Fin k) : embedVec i (0 : HoggarBound.Vec r) = 0 := by
  funext idx; simp [embedVec]

theorem embedVec_add {k r : ℕ} (i : Fin k) (a b : HoggarBound.Vec r) :
    embedVec i (a + b) = embedVec i a + embedVec i b := by
  funext idx
  simp only [embedVec, Pi.add_apply]
  split_ifs <;> simp

theorem embedPt_zero {k r : ℕ} (i : Fin k) : embedPt i (0 : HoggarBound.Pt r) = 0 :=
  Prod.ext (embedVec_zero i) (embedVec_zero i)

theorem embedPt_add {k r : ℕ} (i : Fin k) (u v : HoggarBound.Pt r) :
    embedPt i (u + v) = embedPt i u + embedPt i v :=
  Prod.ext (embedVec_add i u.1 v.1) (embedVec_add i u.2 v.2)

theorem embedVec_apply_equiv {k r : ℕ} (i j : Fin k) (v : HoggarBound.Vec r) (t : Fin r) :
    embedVec i v (finProdFinEquiv (j, t)) = if j = i then v t else 0 := by
  simp [embedVec]

theorem embedVec_injective {k r : ℕ} (i : Fin k) : Function.Injective (embedVec (k := k) (r := r) i) := by
  intro a b h
  funext t
  have := congrFun h (finProdFinEquiv (i, t))
  simpa [embedVec_apply_equiv] using this

theorem embedPt_injective {k r : ℕ} (i : Fin k) : Function.Injective (embedPt (k := k) (r := r) i) := by
  intro u v h
  exact Prod.ext (embedVec_injective i (congrArg Prod.fst h))
    (embedVec_injective i (congrArg Prod.snd h))

theorem embedPt_ne_zero {k r : ℕ} (i : Fin k) {u : HoggarBound.Pt r} (hu : u ≠ 0) :
    embedPt i u ≠ 0 := by
  intro h
  rw [← embedPt_zero i] at h
  exact hu (embedPt_injective i h)

theorem embedPt_ne_of_ne_block {k r : ℕ} {i j : Fin k} (hij : i ≠ j)
    {u v : HoggarBound.Pt r} (hu : u ≠ 0) : embedPt i u ≠ embedPt j v := by
  intro h
  have h1 : embedVec i u.1 = embedVec j v.1 := congrArg Prod.fst h
  have h2 : embedVec i u.2 = embedVec j v.2 := congrArg Prod.snd h
  apply hu
  apply Prod.ext
  · funext t
    have := congrFun h1 (finProdFinEquiv (i, t))
    simpa [embedVec_apply_equiv, hij] using this
  · funext t
    have := congrFun h2 (finProdFinEquiv (i, t))
    simpa [embedVec_apply_equiv, hij] using this

theorem dot_embedVec_same {k r : ℕ} (i : Fin k) (a b : HoggarBound.Vec r) :
    embedVec i a ⬝ᵥ embedVec i b = a ⬝ᵥ b := by
  simp only [dotProduct, embedVec]
  rw [Fintype.sum_equiv finProdFinEquiv.symm _
    (fun p : Fin k × Fin r => (if p.1 = i then a p.2 else 0) * (if p.1 = i then b p.2 else 0))
    (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji; simp [hji]
  · intro h; exact (h (mem_univ i)).elim

theorem dot_embedVec_ne {k r : ℕ} {i j : Fin k} (hij : i ≠ j) (a b : HoggarBound.Vec r) :
    embedVec i a ⬝ᵥ embedVec j b = 0 := by
  simp only [dotProduct, embedVec]
  rw [Fintype.sum_equiv finProdFinEquiv.symm _
    (fun p : Fin k × Fin r => (if p.1 = i then a p.2 else 0) * (if p.1 = j then b p.2 else 0))
    (fun _ => rfl)]
  refine Finset.sum_eq_zero fun p _ => ?_
  by_cases h1 : p.1 = i
  · subst h1; simp [hij]
  · simp [h1]

theorem symp_embedPt_same {k r : ℕ} (i : Fin k) (u v : HoggarBound.Pt r) :
    HoggarBound.symp (embedPt i u) (embedPt i v) = HoggarBound.symp u v := by
  simp [HoggarBound.symp, embedPt, dot_embedVec_same]

theorem symp_embedPt_ne {k r : ℕ} {i j : Fin k} (hij : i ≠ j) (u v : HoggarBound.Pt r) :
    HoggarBound.symp (embedPt i u) (embedPt j v) = 0 := by
  simp [HoggarBound.symp, embedPt, dot_embedVec_ne hij, dot_embedVec_ne hij.symm]

theorem ycount_embedPt {k r : ℕ} (i : Fin k) (u : HoggarBound.Pt r) :
    HoggarBound.ycount (embedPt i u) = HoggarBound.ycount u := by
  rw [HoggarBound.ycount, HoggarBound.ycount, Finset.card_filter, Finset.card_filter]
  rw [Fintype.sum_equiv finProdFinEquiv.symm _
    (fun p : Fin k × Fin r => if (if p.1 = i then u.1 p.2 else 0) = 1 ∧
      (if p.1 = i then u.2 p.2 else 0) = 1 then 1 else 0)]
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      have h01 : (0 : ZMod 2) ≠ 1 := by decide
      simp [hji, h01]
    · intro h; exact (h (mem_univ i)).elim
  · intro idx
    exact if_congr (by simp [embedPt, embedVec]) rfl rfl

theorem tau_embedPt {k r : ℕ} (i : Fin k) (u v : HoggarBound.Pt r) :
    HoggarBound.tau (embedPt i u) (embedPt i v) = HoggarBound.tau u v := by
  rw [HoggarBound.tau, HoggarBound.tau, ← embedPt_add, ycount_embedPt, ycount_embedPt,
    ycount_embedPt, HoggarBound.chi, HoggarBound.chi, embedPt, embedPt, dot_embedVec_same]

/-- Distinct phase-space points produce distinct complex Pauli matrices. -/
theorem pauli_injective {N : ℕ} : Function.Injective (HoggarBound.pauli (N := N)) := by
  intro u v h
  have htr : (HoggarBound.pauli u * HoggarBound.pauli v).trace = (2 : ℂ) ^ N := by
    rw [h, HoggarBound.pauli_mul_self, Matrix.trace_one, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    norm_cast
  rw [HoggarBound.trace_pauli_mul] at htr
  by_contra hne
  rw [ite_eq_right hne] at htr
  have hpow : (2 : ℂ) ^ N ≠ 0 := pow_ne_zero N (by norm_num)
  exact hpow htr.symm

theorem pauli_ne_one_of_ne_zero {N : ℕ} {u : HoggarBound.Pt N} (hu : u ≠ 0) :
    HoggarBound.pauli u ≠ 1 := by
  intro h
  rw [← HoggarBound.pauli_zero] at h
  exact hu (pauli_injective h)

/-- Sum of a list of Pauli phase-space points in `𝔽₂^{2N}`. -/
def pauliListSum {N : ℕ} : List (HoggarBound.Pt N) → HoggarBound.Pt N
  | [] => 0
  | u :: L => u + pauliListSum L

/-- Accumulated scalar phase of multiplying a list of Hermitian Pauli matrices. -/
def pauliListPhase {N : ℕ} : List (HoggarBound.Pt N) → ℂ
  | [] => 1
  | u :: L => HoggarBound.tau u (pauliListSum L) * pauliListPhase L

theorem pauliList_prod {N : ℕ} : ∀ L : List (HoggarBound.Pt N),
    (L.map HoggarBound.pauli).prod = pauliListPhase L • HoggarBound.pauli (pauliListSum L)
  | [] => by simp [pauliListPhase, pauliListSum, HoggarBound.pauli_zero]
  | u :: L => by
    simp only [List.map_cons, List.prod_cons, pauliList_prod L, Matrix.mul_smul,
      HoggarBound.pauli_mul, smul_smul, pauliListPhase, pauliListSum]
    ring_nf

theorem pauliListSum_embed {k r : ℕ} (i : Fin k) : ∀ L : List (HoggarBound.Pt r),
    pauliListSum (L.map (embedPt i)) = embedPt i (pauliListSum L)
  | [] => (embedPt_zero i).symm
  | u :: L => by
    simp only [List.map_cons, pauliListSum, pauliListSum_embed i L, embedPt_add]

theorem pauliListPhase_embed {k r : ℕ} (i : Fin k) : ∀ L : List (HoggarBound.Pt r),
    pauliListPhase (L.map (embedPt i)) = pauliListPhase L
  | [] => rfl
  | u :: L => by
    simp only [List.map_cons, pauliListPhase, pauliListSum_embed i L, tau_embedPt,
      pauliListPhase_embed i L]

/-- Integer mod-4 exponent for `tau u v = I ^ (tauExp u v % 4)` (enables kernel `decide`). -/
def tauExp {N : ℕ} (u v : HoggarBound.Pt N) : ℕ :=
  HoggarBound.ycount u + HoggarBound.ycount v + 3 * HoggarBound.ycount (u + v) +
    2 * (u.2 ⬝ᵥ v.1).val

theorem complex_I_pow_mod_four (n : ℕ) : Complex.I ^ n = Complex.I ^ (n % 4) := by
  conv_lhs => rw [← Nat.div_add_mod n 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]

theorem tau_eq_I_pow_tauExp {N : ℕ} (u v : HoggarBound.Pt N) :
    HoggarBound.tau u v = Complex.I ^ (tauExp u v % 4) := by
  rw [← complex_I_pow_mod_four]
  simp only [HoggarBound.tau, tauExp, pow_add, HoggarBound.chi]
  congr 1
  have hval : ((u.2 ⬝ᵥ v.1).val : ZMod 2) = u.2 ⬝ᵥ v.1 := ZMod.natCast_zmod_val _
  conv_lhs => rw [← hval]
  rw [HoggarBound.eps_natCast, pow_mul, Complex.I_sq]

/-- Mod-4 accumulated phase exponent for a list of Pauli points. -/
def pauliListExp {N : ℕ} : List (HoggarBound.Pt N) → ℕ
  | [] => 0
  | u :: L => (tauExp u (pauliListSum L) + pauliListExp L) % 4

theorem pauliListPhase_eq_I_pow {N : ℕ} : ∀ L : List (HoggarBound.Pt N),
    pauliListPhase L = Complex.I ^ (pauliListExp L)
  | [] => by simp [pauliListPhase, pauliListExp]
  | u :: L => by
    simp only [pauliListPhase, pauliListExp, tau_eq_I_pow_tauExp, pauliListPhase_eq_I_pow L]
    rw [← pow_add, complex_I_pow_mod_four, Nat.mod_add_mod]

/-- The 9 two-qubit Peres–Mermin square observables (`XI, IX, XX, IZ, ZI, ZZ, XZ, ZX, YY`)
as points in `HoggarBound.Pt 2`. -/
def squarePt : Fin 9 → HoggarBound.Pt 2 := ![
  (![1, 0], ![0, 0]),
  (![0, 1], ![0, 0]),
  (![1, 1], ![0, 0]),
  (![0, 0], ![0, 1]),
  (![0, 0], ![1, 0]),
  (![0, 0], ![1, 1]),
  (![1, 0], ![0, 1]),
  (![0, 1], ![1, 0]),
  (![1, 1], ![1, 1])]

/-- The 10 three-qubit Mermin pentagram observables (`XII, IXI, IIX, YII, IYI, IIY, XXX, XYY, YXY, YYX`)
from Section 4.2 of the manuscript, as points in `HoggarBound.Pt 3`. -/
def pentagramPt : Fin 10 → HoggarBound.Pt 3 := ![
  (![1, 0, 0], ![0, 0, 0]),
  (![0, 1, 0], ![0, 0, 0]),
  (![0, 0, 1], ![0, 0, 0]),
  (![1, 0, 0], ![1, 0, 0]),
  (![0, 1, 0], ![0, 1, 0]),
  (![0, 0, 1], ![0, 0, 1]),
  (![1, 1, 1], ![0, 0, 0]),
  (![1, 1, 1], ![0, 1, 1]),
  (![1, 1, 1], ![1, 0, 1]),
  (![1, 1, 1], ![1, 1, 0])]

/-- Ordered vertex lists for the 6 Peres–Mermin square contexts. -/
def squareCtxList : Fin 6 → List (Fin 9) :=
  ![[0, 1, 2], [3, 4, 5], [6, 7, 8], [0, 3, 6], [1, 4, 7], [2, 5, 8]]

/-- Ordered vertex lists for the 5 Mermin pentagram contexts. -/
def pentagramCtxList : Fin 5 → List (Fin 10) :=
  ![[0, 1, 2, 6], [0, 4, 5, 7], [3, 1, 5, 8], [3, 4, 2, 9], [6, 7, 8, 9]]

theorem squarePt_injective : Function.Injective squarePt := by decide +kernel
theorem squarePt_ne_zero : ∀ v : Fin 9, squarePt v ≠ 0 := by decide +kernel
theorem squarePt_context_commute : ∀ (c : Fin 6) (u v : Fin 9),
    u ∈ squareContext c → v ∈ squareContext c →
    HoggarBound.symp (squarePt u) (squarePt v) = 0 := by decide +kernel
theorem squarePt_context_sum : ∀ c : Fin 6,
    pauliListSum ((squareCtxList c).map squarePt) = 0 := by decide +kernel
theorem squarePt_context_exp : ∀ c : Fin 6,
    pauliListExp ((squareCtxList c).map squarePt) = if c == 5 then 2 else 0 := by decide +kernel

theorem pentagramPt_injective : Function.Injective pentagramPt := by decide +kernel
theorem pentagramPt_ne_zero : ∀ v : Fin 10, pentagramPt v ≠ 0 := by decide +kernel
theorem pentagramPt_context_commute : ∀ (c : Fin 5) (u v : Fin 10),
    u ∈ pentagramContext c → v ∈ pentagramContext c →
    HoggarBound.symp (pentagramPt u) (pentagramPt v) = 0 := by decide +kernel
theorem pentagramPt_context_sum : ∀ c : Fin 5,
    pauliListSum ((pentagramCtxList c).map pentagramPt) = 0 := by decide +kernel
theorem pentagramPt_context_exp : ∀ c : Fin 5,
    pauliListExp ((pentagramCtxList c).map pentagramPt) = if c == 4 then 2 else 0 := by decide +kernel

/-- The `9k` Hermitian Pauli operators on `2k` qubits realizing `k` disjoint Peres–Mermin squares. -/
def kSquarePauli (k : ℕ) (x : Σ _i : Fin k, Fin 9) :
    Matrix (HoggarBound.Vec (k * 2)) (HoggarBound.Vec (k * 2)) ℂ :=
  HoggarBound.pauli (embedPt x.1 (squarePt x.2))

/-- The `10k` Hermitian Pauli operators on `3k` qubits realizing `k` disjoint Mermin pentagrams. -/
def kPentagramPauli (k : ℕ) (x : Σ _i : Fin k, Fin 10) :
    Matrix (HoggarBound.Vec (k * 3)) (HoggarBound.Vec (k * 3)) ℂ :=
  HoggarBound.pauli (embedPt x.1 (pentagramPt x.2))

/-- Ordered list of tagged vertices for a union context `q : Fin k → Option C`. -/
def unionVertexList {k : ℕ} {C V : Type*} (ctxList : C → List V) (q : Fin k → Option C) :
    List (Σ _i : Fin k, V) :=
  (List.finRange k).flatMap fun i =>
    match q i with
    | none => []
    | some c => (ctxList c).map fun v => Sigma.mk i v

theorem list_prod_smul_one {α : Type*} [Fintype α] [DecidableEq α] :
    ∀ (L : List ℂ), (L.map (fun s => s • (1 : Matrix α α ℂ))).prod = L.prod • (1 : Matrix α α ℂ)
  | [] => by simp
  | s :: L => by
    simp only [List.map_cons, List.prod_cons, list_prod_smul_one L, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, smul_smul]
    rw [mul_comm]

theorem list_prod_flatMap {α β : Type*} [Monoid β] (L : List α) (f : α → List β) :
    (L.flatMap f).prod = (L.map (fun x => (f x).prod)).prod := by
  induction L with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, List.prod_append, ih]

theorem list_prod_finRange {k : ℕ} (f : Fin k → ℂ) :
    ((List.finRange k).map f).prod = ∏ i : Fin k, f i := by
  rw [← Multiset.prod_coe]
  have h : ((List.finRange k : List (Fin k)) : Multiset (Fin k)) = (Finset.univ : Finset (Fin k)).val := by
    rfl
  rw [← Multiset.map_coe, h]
  rfl

/-- Generic arbitrary-`k` Pauli operator-identity bridge (Eq. 5). -/
theorem arbitrary_k_pauli_realization {k r : ℕ} {C V : Type*} [Fintype C] [DecidableEq C]
    [DecidableEq V]
    (seed : C → Finset V) (ctxList : C → List V) (negative : C → Bool)
    (seedPt : V → HoggarBound.Pt r)
    (hi : Function.Injective seed) (hne : ∀ c, (seed c).Nonempty)
    (hlist : ∀ c, (ctxList c).toFinset = seed c)
    (hinj : Function.Injective seedPt) (hzero : ∀ v, seedPt v ≠ 0)
    (hcomm : ∀ c u v, u ∈ seed c → v ∈ seed c → HoggarBound.symp (seedPt u) (seedPt v) = 0)
    (hsum : ∀ c, pauliListSum ((ctxList c).map seedPt) = 0)
    (hexp : ∀ c, pauliListExp ((ctxList c).map seedPt) = if negative c then 2 else 0) :
    let op : (Σ _i : Fin k, V) → Matrix (HoggarBound.Vec (k * r)) (HoggarBound.Vec (k * r)) ℂ :=
      fun x => HoggarBound.pauli (embedPt x.1 (seedPt x.2))
    (∀ x, (op x).IsHermitian ∧ op x * op x = 1 ∧ op x ≠ 1) ∧
    Function.Injective op ∧
    (∀ x y, x.1 ≠ y.1 → op x * op y = op y * op x) ∧
    (∀ q ∈ contexts k C,
      (unionVertexList ctxList q).toFinset = unionContext seed q ∧
      (∀ x ∈ unionContext seed q, ∀ y ∈ unionContext seed q, op x * op y = op y * op x) ∧
      ((unionVertexList ctxList q).map op).prod =
        ((actualSign seed negative (unionContext seed q) : ℤ) : ℂ) • 1) := by
  intro op
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    exact ⟨HoggarBound.pauli_isHermitian _, HoggarBound.pauli_mul_self _,
      pauli_ne_one_of_ne_zero (embedPt_ne_zero x.1 (hzero x.2))⟩
  · intro x y h
    have hp := pauli_injective h
    by_cases h1 : x.1 = y.1
    · rcases x with ⟨i, u⟩
      rcases y with ⟨j, v⟩
      dsimp at h1
      subst h1
      have huv := hinj (embedPt_injective i hp)
      subst huv; rfl
    · exact (embedPt_ne_of_ne_block h1 (hzero x.2) hp).elim
  · intro x y hne_blk
    have hs : HoggarBound.symp (embedPt x.1 (seedPt x.2)) (embedPt y.1 (seedPt y.2)) = 0 :=
      symp_embedPt_ne hne_blk _ _
    have hc := HoggarBound.pauli_comm (embedPt x.1 (seedPt x.2)) (embedPt y.1 (seedPt y.2))
    rw [hs, HoggarBound.eps_zero, one_smul] at hc
    exact hc.symm
  · intro q hq
    refine ⟨?_, ?_, ?_⟩
    · ext ⟨i, v⟩
      simp only [unionVertexList, List.mem_toFinset, List.mem_flatMap, List.mem_finRange, true_and,
        unionContext, Finset.mem_sigma, Finset.mem_univ]
      constructor
      · rintro ⟨j, hj⟩
        cases hqj : q j with
        | none => simp [hqj] at hj
        | some c =>
          simp only [hqj, List.mem_map] at hj
          rcases hj with ⟨w, hw, heq⟩
          cases heq
          simp only [selectedContext, hqj, ← hlist c]
          exact List.mem_toFinset.mpr hw
      · intro hv
        refine ⟨i, ?_⟩
        cases hqi : q i with
        | none => simp [selectedContext, hqi] at hv
        | some c =>
          simp only [selectedContext, hqi, ← hlist c, List.mem_toFinset] at hv
          simp only [List.mem_map]
          exact ⟨v, hv, rfl⟩
    · intro x hx y hy
      by_cases hxy : x.1 = y.1
      · rcases x with ⟨i, u⟩
        rcases y with ⟨j, v⟩
        dsimp at hxy
        subst hxy
        simp only [unionContext, Finset.mem_sigma, Finset.mem_univ, true_and] at hx hy
        cases hqi : q i with
        | none => simp [selectedContext, hqi] at hx
        | some c =>
          simp only [selectedContext, hqi] at hx hy
          have hs : HoggarBound.symp (embedPt i (seedPt u)) (embedPt i (seedPt v)) = 0 := by
            rw [symp_embedPt_same]
            exact hcomm c u v hx hy
          have hc := HoggarBound.pauli_comm (embedPt i (seedPt u)) (embedPt i (seedPt v))
          rw [hs, HoggarBound.eps_zero, one_smul] at hc
          exact hc.symm
      · have hs : HoggarBound.symp (embedPt x.1 (seedPt x.2)) (embedPt y.1 (seedPt y.2)) = 0 :=
          symp_embedPt_ne hxy _ _
        have hc := HoggarBound.pauli_comm (embedPt x.1 (seedPt x.2)) (embedPt y.1 (seedPt y.2))
        rw [hs, HoggarBound.eps_zero, one_smul] at hc
        exact hc.symm
    · rw [actualSign_union seed negative hi hne q hq]
      unfold unionVertexList
      rw [List.map_flatMap, list_prod_flatMap]
      have hblock : ∀ i : Fin k,
          ((match q i with
            | none => []
            | some c => (ctxList c).map fun v => Sigma.mk i v).map op).prod =
          ((extend (fun c => sign (negative c)) (q i) : ℤ) : ℂ) •
            (1 : Matrix (HoggarBound.Vec (k * r)) (HoggarBound.Vec (k * r)) ℂ) := by
        intro i
        cases hqi : q i with
        | none => simp [extend]
        | some c =>
          have hmap : ((ctxList c).map (fun v => Sigma.mk i v)).map op =
              (((ctxList c).map seedPt).map (embedPt i)).map HoggarBound.pauli := by
            simp [op, List.map_map, Function.comp_def]
          rw [hmap, pauliList_prod, pauliListSum_embed, pauliListPhase_embed, hsum c,
            embedPt_zero, HoggarBound.pauli_zero, pauliListPhase_eq_I_pow, hexp c]
          congr 1
          cases hneg : negative c <;> simp [extend, sign, hneg, Complex.I_sq]
      have hmap_eq : (List.finRange k).map (fun i =>
            ((match q i with
              | none => []
              | some c => (ctxList c).map fun v => Sigma.mk i v).map op).prod) =
          ((List.finRange k).map fun i => ((extend (fun c => sign (negative c)) (q i) : ℤ) : ℂ)).map
            (fun s => s • (1 : Matrix (HoggarBound.Vec (k * r)) (HoggarBound.Vec (k * r)) ℂ)) := by
        rw [List.map_map]
        exact List.map_congr_left fun i _ => hblock i
      rw [hmap_eq, list_prod_smul_one, list_prod_finRange]
      push_cast
      rfl

/-- **Arbitrary-`k` Peres–Mermin Square Pauli Realization (Eq. 5):** For EVERY `k : ℕ`,
the `9k` Hermitian Pauli operators `kSquarePauli k` on `2k` qubits are pairwise distinct,
non-identity, involutive, commute across registers and within every union context, and satisfy
the exact operator product identity `actualSign · I` on all `7^k - 1` nonempty union contexts. -/
theorem arbitrary_k_square_pauli_realization (k : ℕ) :
    (∀ x, (kSquarePauli k x).IsHermitian ∧ kSquarePauli k x * kSquarePauli k x = 1 ∧
      kSquarePauli k x ≠ 1) ∧
    Function.Injective (kSquarePauli k) ∧
    (∀ x y, x.1 ≠ y.1 → kSquarePauli k x * kSquarePauli k y = kSquarePauli k y * kSquarePauli k x) ∧
    (∀ q ∈ contexts k (Fin 6),
      (unionVertexList squareCtxList q).toFinset = unionContext squareContext q ∧
      (∀ x ∈ unionContext squareContext q, ∀ y ∈ unionContext squareContext q,
        kSquarePauli k x * kSquarePauli k y = kSquarePauli k y * kSquarePauli k x) ∧
      ((unionVertexList squareCtxList q).map (kSquarePauli k)).prod =
        ((actualSign squareContext (fun c => c == 5) (unionContext squareContext q) : ℤ) : ℂ) • 1) :=
  arbitrary_k_pauli_realization squareContext squareCtxList (fun c => c == 5) squarePt
    square_context_injective square_context_nonempty
    (by intro c; revert c; decide +kernel)
    squarePt_injective squarePt_ne_zero squarePt_context_commute
    squarePt_context_sum squarePt_context_exp

/-- **Arbitrary-`k` Mermin Pentagram Pauli Realization (Eq. 5):** For EVERY `k : ℕ`,
the `10k` Hermitian Pauli operators `kPentagramPauli k` on `3k` qubits are pairwise distinct,
non-identity, involutive, commute across registers and within every union context, and satisfy
the exact operator product identity `actualSign · I` on all `6^k - 1` nonempty union contexts. -/
theorem arbitrary_k_pentagram_pauli_realization (k : ℕ) :
    (∀ x, (kPentagramPauli k x).IsHermitian ∧ kPentagramPauli k x * kPentagramPauli k x = 1 ∧
      kPentagramPauli k x ≠ 1) ∧
    Function.Injective (kPentagramPauli k) ∧
    (∀ x y, x.1 ≠ y.1 → kPentagramPauli k x * kPentagramPauli k y =
      kPentagramPauli k y * kPentagramPauli k x) ∧
    (∀ q ∈ contexts k (Fin 5),
      (unionVertexList pentagramCtxList q).toFinset = unionContext pentagramContext q ∧
      (∀ x ∈ unionContext pentagramContext q, ∀ y ∈ unionContext pentagramContext q,
        kPentagramPauli k x * kPentagramPauli k y = kPentagramPauli k y * kPentagramPauli k x) ∧
      ((unionVertexList pentagramCtxList q).map (kPentagramPauli k)).prod =
        ((actualSign pentagramContext (fun c => c == 4) (unionContext pentagramContext q) : ℤ) : ℂ) • 1) :=
  arbitrary_k_pauli_realization pentagramContext pentagramCtxList (fun c => c == 4) pentagramPt
    pentagram_context_injective pentagram_context_nonempty
    (by intro c; revert c; decide +kernel)
    pentagramPt_injective pentagramPt_ne_zero pentagramPt_context_commute
    pentagramPt_context_sum pentagramPt_context_exp

/-! ### Part 5. Independent-Readout Noise Model & `k`-Independent Thresholds (Eqs. 14–16) -/

/-- Exact expected union score `Q_k(p)` under independent elementary outcome flip probability `p`
for `k` copies of an `m`-context, `r`-observable-per-context seed. -/
noncomputable def noisyScore (m r k : ℕ) (p : ℝ) : ℝ :=
  ∑ q ∈ contexts k (Fin m), ∏ i : Fin k,
    match q i with
    | none => (1 : ℝ)
    | some _ => (1 - 2 * p) ^ r

/-- **Eq. (14):** Closed form `Q_k(p) = (1 + m (1 - 2p)^r)^k - 1`. -/
theorem noisyScore_closed_form (m r k : ℕ) (p : ℝ) :
    noisyScore m r k p = (1 + (m : ℝ) * (1 - 2 * p) ^ r) ^ k - 1 := by
  let g : Option (Fin m) → ℝ := fun o => match o with | none => 1 | some _ => (1 - 2 * p) ^ r
  have he := Finset.sum_erase_add (s := (univ : Finset (Fin k → Option (Fin m))))
    (f := fun q => ∏ i : Fin k, g (q i)) (mem_univ emptyChoice)
  have hempty : (∏ i : Fin k, g (emptyChoice i)) = 1 := by simp [emptyChoice, g]
  have hp := Fintype.prod_sum (fun (_i : Fin k) (o : Option (Fin m)) => g o)
  have hsum : (∑ o : Option (Fin m), g o) = 1 + (m : ℝ) * (1 - 2 * p) ^ r := by
    rw [Fintype.sum_option]
    simp [g]
  have hprod : (∏ _i : Fin k, ∑ o : Option (Fin m), g o) = (1 + (m : ℝ) * (1 - 2 * p) ^ r) ^ k := by
    rw [hsum]; simp
  have htot : noisyScore m r k p + 1 = (1 + (m : ℝ) * (1 - 2 * p) ^ r) ^ k := by
    unfold noisyScore
    calc (∑ q ∈ contexts k (Fin m), ∏ i : Fin k, g (q i)) + 1
        = (∑ q ∈ contexts k (Fin m), ∏ i : Fin k, g (q i)) + ∏ i : Fin k, g (emptyChoice i) := by
          rw [hempty]
      _ = ∑ q : Fin k → Option (Fin m), ∏ i : Fin k, g (q i) := he
      _ = ∏ _i : Fin k, ∑ o : Option (Fin m), g o := hp.symm
      _ = (1 + (m : ℝ) * (1 - 2 * p) ^ r) ^ k := hprod
  linarith

/-- **Eq. (15):** For EVERY `k ≥ 1` and `p ∈ [0, 1/2]`, the `k`-square inequality is violated
under independent readout noise iff `(1 - 2p)^3 > 2/3` (independent of `k`). -/
theorem square_noise_threshold_iff (k : ℕ) (hk : 1 ≤ k) (p : ℝ) (_hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    (5 : ℝ) ^ k - 1 < noisyScore 6 3 k p ↔ (2 : ℝ) / 3 < (1 - 2 * p) ^ 3 := by
  rw [noisyScore_closed_form]
  push_cast
  have hη : 0 ≤ 1 - 2 * p := by linarith
  have hbase : 0 ≤ 1 + (6 : ℝ) * (1 - 2 * p) ^ 3 := by positivity
  have hk_ne : k ≠ 0 := by omega
  constructor
  · intro h
    have hpow : (5 : ℝ) ^ k < (1 + (6 : ℝ) * (1 - 2 * p) ^ 3) ^ k := by linarith
    have hlt : (5 : ℝ) < 1 + (6 : ℝ) * (1 - 2 * p) ^ 3 := by
      by_contra hle
      push Not at hle
      have := pow_le_pow_left₀ hbase hle k
      linarith
    linarith
  · intro h
    have hlt : (5 : ℝ) < 1 + (6 : ℝ) * (1 - 2 * p) ^ 3 := by linarith
    have hpow : (5 : ℝ) ^ k < (1 + (6 : ℝ) * (1 - 2 * p) ^ 3) ^ k :=
      pow_lt_pow_left₀ hlt (by norm_num) hk_ne
    linarith

/-- **Eq. (16):** For EVERY `k ≥ 1` and `p ∈ [0, 1/2]`, the `k`-pentagram inequality is violated
under independent readout noise iff `(1 - 2p)^4 > 3/5` (independent of `k`). -/
theorem pentagram_noise_threshold_iff (k : ℕ) (hk : 1 ≤ k) (p : ℝ) (_hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    (4 : ℝ) ^ k - 1 < noisyScore 5 4 k p ↔ (3 : ℝ) / 5 < (1 - 2 * p) ^ 4 := by
  rw [noisyScore_closed_form]
  push_cast
  have hη : 0 ≤ 1 - 2 * p := by linarith
  have hbase : 0 ≤ 1 + (5 : ℝ) * (1 - 2 * p) ^ 4 := by positivity
  have hk_ne : k ≠ 0 := by omega
  constructor
  · intro h
    have hpow : (4 : ℝ) ^ k < (1 + (5 : ℝ) * (1 - 2 * p) ^ 4) ^ k := by linarith
    have hlt : (4 : ℝ) < 1 + (5 : ℝ) * (1 - 2 * p) ^ 4 := by
      by_contra hle
      push Not at hle
      have := pow_le_pow_left₀ hbase hle k
      linarith
    linarith
  · intro h
    have hlt : (4 : ℝ) < 1 + (5 : ℝ) * (1 - 2 * p) ^ 4 := by linarith
    have hpow : (4 : ℝ) ^ k < (1 + (5 : ℝ) * (1 - 2 * p) ^ 4) ^ k :=
      pow_lt_pow_left₀ hlt (by norm_num) hk_ne
    linarith

/-- For any fixed readout flip rate `p ∈ (0, 1/2]`, `m ≥ 1`, `r ≥ 1`, the normalized noisy
quantum score `Q_k(p) / ((m + 1)^k - 1)` tends to `0` as `k → ∞`. -/
theorem noisy_normalized_score_tends_to_zero (m r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1 / 2) :
    Tendsto (fun k : ℕ => noisyScore m r k p / (((m : ℝ) + 1) ^ k - 1)) atTop (𝓝 0) := by
  set a : ℝ := (m : ℝ) + 1
  set b : ℝ := 1 + (m : ℝ) * (1 - 2 * p) ^ r
  have ha1 : 1 < a := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have ha0 : 0 < a := lt_trans zero_lt_one ha1
  have hη0 : 0 ≤ 1 - 2 * p := by linarith
  have hη1 : 1 - 2 * p < 1 := by linarith
  have hηpow : (1 - 2 * p) ^ r < 1 := pow_lt_one₀ hη0 hη1 (by omega)
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
  have hb0 : 0 ≤ b := by positivity
  have hba : b < a := by nlinarith
  have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hb0 ha0.le) ((div_lt_one ha0).mpr hba)
  have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) ha0.le)
    ((div_lt_one ha0).mpr ha1)
  have hlim := (h1.sub h2).div ((tendsto_const_nhds (x := (1 : ℝ))).sub h2) (by norm_num : (1 : ℝ) - 0 ≠ 0)
  have heq : (fun k : ℕ => noisyScore m r k p / (a ^ k - 1)) =
      (fun k : ℕ => ((b / a) ^ k - (1 / a) ^ k) / (1 - (1 / a) ^ k)) := by
    funext k
    rw [noisyScore_closed_form]
    have hak : a ^ k ≠ 0 := pow_ne_zero k ha0.ne'
    rw [div_pow, div_pow, one_pow]
    field_simp
    simp [b]
  rw [heq]
  convert hlim using 1
  simp

end ContextualityTensor
