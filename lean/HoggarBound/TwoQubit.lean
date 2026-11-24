/-
Hoggar Bound Lab — two qubits, and sanity checks of the sign convention.

* `sign_XX_ZZ` : the context `{XX, ZZ, YY}` has operator product `−I` (`XX · ZZ = −YY`).
* `mermin_peres` : the 9 real two-qubit observables (the Mermin–Peres square, `Q⁺(3,2)`) admit
  no noncontextual assignment; the third-moment bound gives `≥ 1` violated context, and the
  all-`+1` assignment shows `d(Q⁺(3,2)) = 1`.
* `doily_contexts` : the bound gives `≥ 2` for the doily `W(3,2)` (15 points, 15 lines); the
  all-`+1` assignment violates exactly 3 (the true degree is 3; our bound is not tight here).
-/
import HoggarBound.Witness

open Finset Matrix

namespace HoggarBound

variable {N : ℕ}

/-- `XX`, as a point. -/
def pXX : Pt 2 := (fun _ => 1, fun _ => 0)
/-- `ZZ`, as a point. -/
def pZZ : Pt 2 := (fun _ => 0, fun _ => 1)

/-- `XX · ZZ · YY = −I`: the context sign is `−1`. -/
theorem sign_XX_ZZ : symp pXX pZZ = 0 ∧ lineSign pXX pZZ = -1 := by
  have h : symp pXX pZZ = 0 := by decide
  refine ⟨h, ?_⟩
  rw [lineSign_eq_lsign h]
  have : lsign pXX pZZ = -1 := by decide
  rw [this]; norm_num

/-- `pauli (XX + ZZ)` really is `Y ⊗ Y` in the sense that `XX · ZZ = − P_{XX+ZZ}`. -/
theorem pauli_XX_mul_ZZ : pauli pXX * pauli pZZ = - pauli (pXX + pZZ) := by
  rw [pauli_mul, tau_eq_lineSign sign_XX_ZZ.1, sign_XX_ZZ.2]
  simp

/-- Integer `±1` assignments: violated flags in computable form. -/
lemma violated_intCast (S : Finset (Pt N)) (g : Pt N → ℤ) :
    violated S (fun u => ((g u : ℤ) : ℝ)) = (flags S).filter
      (fun p => g p.1 * g p.2 * g (p.1 + p.2) ≠ lsign p.1 p.2) := by
  ext p
  simp only [violated, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hne⟩
    refine ⟨hp, fun h => hne ?_⟩
    rw [lineSign_eq_lsign (mem_flags.1 hp).2.2.2, ← h]
    push_cast; ring
  · rintro ⟨hp, hne⟩
    refine ⟨hp, fun h => hne ?_⟩
    rw [lineSign_eq_lsign (mem_flags.1 hp).2.2.2] at h
    have : ((g p.1 * g p.2 * g (p.1 + p.2) : ℤ) : ℝ) = ((lsign p.1 p.2 : ℤ) : ℝ) := by
      push_cast; exact h
    exact_mod_cast this

lemma realPoints_eq_filter : realPoints N = univ.filter (fun u : Pt N => u ≠ 0 ∧ qform u = 0) :=
  rfl

/-- **Mermin–Peres.**  Every `±1` assignment of the nine real two-qubit observables violates at
least one of the six contexts, and one context is the best possible. -/
theorem mermin_peres :
    (∀ f : Pt 2 → ℝ, (∀ u ∈ realPoints 2, f u = 1 ∨ f u = -1) →
        1 ≤ (violatedLines (realPoints 2) f).card) ∧
      (violatedLines (realPoints 2) (fun _ => 1)).card = 1 := by
  constructor
  · intro f hf
    have h0 : (0 : Pt 2) ∉ realPoints 2 := by simp [realPoints]
    have hb := hoggar_bound_violated (N := 2) (by norm_num) (realPoints 2) h0 f hf
    have hS : (realPoints 2).card = 9 := by decide
    have hF : (flags (realPoints 2)).card = 36 := by
      have := card_flags_real (N := 2)
      simp only [hS] at this
      generalize (flags _).card = F at this ⊢; omega
    simp only [hF, hS] at hb
    have e3 : ((2 : ℝ) ^ 2 - 2) * ((9 : ℕ) : ℝ) = 18 := by norm_num
    have e2 : ((2 : ℝ) ^ 2 - 1) = 3 := by norm_num
    have hF' : ((36 : ℕ) : ℝ) = 36 := by norm_num
    have e1' : (3 : ℝ) * ((9 : ℕ) : ℝ) = 27 := by norm_num
    simp only [e3, e2, hF'] at hb
    simp only [e1'] at hb
    have hsqrt : Real.sqrt 27 < 5.1962 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have hV' : 3 ≤ (violated (realPoints 2) f).card := by
      by_contra hlt
      have hV : ((violated (realPoints 2) f).card : ℝ) ≤ 2 := by
        have : (violated (realPoints 2) f).card ≤ 2 := by omega
        exact_mod_cast this
      have := mul_lt_mul_of_pos_left hsqrt (by norm_num : (0 : ℝ) < 18)
      linarith
    have h2 := card_violated_le (realPoints 2) h0 f
    omega
  · have : (fun _ : Pt 2 => (1 : ℝ)) = fun u => (((fun _ => (1 : ℤ)) u : ℤ) : ℝ) := by
      funext u; simp
    rw [this, violatedLines, violated_intCast, realPoints_eq_filter, flags_filter]
    decide +kernel

/-- **The doily `W(3,2)`.**  The bound gives at least 2 violated contexts out of 15; the all-`+1`
assignment violates exactly 3. -/
theorem doily_contexts :
    (∀ f : Pt 2 → ℝ, (∀ u ∈ allPoints 2, f u = 1 ∨ f u = -1) →
        2 ≤ (violatedLines (allPoints 2) f).card) ∧
      (violatedLines (allPoints 2) (fun _ => 1)).card = 3 := by
  constructor
  · intro f hf
    have h0 : (0 : Pt 2) ∉ allPoints 2 := by simp [allPoints]
    have hb := hoggar_bound_violated (N := 2) (by norm_num) (allPoints 2) h0 f hf
    have hS : (allPoints 2).card = 15 := by rw [card_allPoints]; rfl
    have hF : (flags (allPoints 2)).card = 90 := by
      have := card_flags_all (N := 2)
      generalize (flags _).card = F at this ⊢; omega
    simp only [hF, hS] at hb
    have e3 : ((2 : ℝ) ^ 2 - 2) * ((15 : ℕ) : ℝ) = 30 := by norm_num
    have e2 : ((2 : ℝ) ^ 2 - 1) = 3 := by norm_num
    have hF' : ((90 : ℕ) : ℝ) = 90 := by norm_num
    have e1' : (3 : ℝ) * ((15 : ℕ) : ℝ) = 45 := by norm_num
    simp only [e3, e2, hF'] at hb
    simp only [e1'] at hb
    have hsqrt : Real.sqrt 45 < 6.7083 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have hV' : 12 ≤ (violated (allPoints 2) f).card := by
      by_contra hlt
      have hV : ((violated (allPoints 2) f).card : ℝ) ≤ 11 := by
        have : (violated (allPoints 2) f).card ≤ 11 := by omega
        exact_mod_cast this
      have := mul_lt_mul_of_pos_left hsqrt (by norm_num : (0 : ℝ) < 30)
      linarith
    have h2 := card_violated_le (allPoints 2) h0 f
    omega
  · have : (fun _ : Pt 2 => (1 : ℝ)) = fun u => (((fun _ => (1 : ℤ)) u : ℤ) : ℝ) := by
      funext u; simp
    rw [this, violatedLines, violated_intCast, allPoints_eq_filter, flags_filter]
    decide +kernel

end HoggarBound
