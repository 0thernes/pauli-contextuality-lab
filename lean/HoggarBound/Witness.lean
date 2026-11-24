/-
Pauli Contextuality Lab — exact three-qubit values certified by explicit witnesses
(kernel `decide +kernel`, zero `native_decide`), ported from the legacy `hoggar-bound`
prototype onto `HoggarBound.Kramers`.

The sign pattern of the Hoggar SIC fiducial `ψ = (−1+2i, 1, …, 1)/√12` (all 63 three-qubit
Pauli expectations are `±1/3`) is stored as a 64-bit mask. The kernel checks that it violates
exactly 63 contexts of `W(5,2)` and exactly 9 contexts of the elliptic quadric `Q⁻(5,2)`.
Combined with the lower bounds this gives the exact contextuality degrees:

    d(W(5,2)) = 63        (`degree_three_qubit`)
    d(Q⁻(5,2)) = 9        (`degree_three_qubit_elliptic`)
-/
import HoggarBound.Kramers
import HoggarBound.Corollaries

open Finset Matrix

namespace HoggarBound

variable {N : ℕ}

/-! ### A computable line sign -/

/-- Exponent of `i` in the phase `tau u v`. -/
def tauExp (u v : Pt N) : ℕ := ycount u + ycount v + 3 * ycount (u + v)

/-- Integer-valued sign of the context `{u, v, u+v}` (agrees with `lineSign` on commuting pairs). -/
def lsign (u v : Pt N) : ℤ :=
  (if tauExp u v / 2 % 2 = 0 then 1 else -1) * (if u.2 ⬝ᵥ v.1 = 0 then 1 else -1)

lemma two_dvd_tauExp {u v : Pt N} (h : symp u v = 0) : 2 ∣ tauExp u v := by
  rw [← ZMod.natCast_eq_zero_iff]
  simp only [tauExp]
  push_cast
  rw [ycount_add_cast, h]
  have h1 := zmod2_add_self (ycount u : ZMod 2)
  have h2 := zmod2_add_self (ycount v : ZMod 2)
  have h3 : (3 : ZMod 2) = 1 := by decide
  rw [h3]
  linear_combination h1 + h2

lemma lineSign_eq_lsign {u v : Pt N} (h : symp u v = 0) :
    lineSign u v = ((lsign u v : ℤ) : ℝ) := by
  obtain ⟨k, hk⟩ := two_dvd_tauExp h
  have hI : Complex.I ^ tauExp u v = (-1) ^ k := by
    rw [hk, pow_mul, Complex.I_sq]
  have hk2 : tauExp u v / 2 = k := by omega
  have hchi : chi u.2 v.1 = if u.2 ⬝ᵥ v.1 = 0 then 1 else -1 := by
    simp only [chi, eps]
  have htau : tau u v = Complex.I ^ tauExp u v * chi u.2 v.1 := rfl
  have hl : lsign u v = (if k % 2 = 0 then 1 else -1) * (if u.2 ⬝ᵥ v.1 = 0 then 1 else -1) := by
    unfold lsign; rw [hk2]
  rw [hl]
  unfold lineSign
  rw [htau, hI, hchi]
  rcases Nat.even_or_odd k with hke | hko
  · have h0 : k % 2 = 0 := Nat.even_iff.1 hke
    simp only [hke.neg_one_pow, h0, ite_true]
    split_ifs <;> simp
  · have h1 : k % 2 = 1 := Nat.odd_iff.1 hko
    have h0 : ¬ k % 2 = 0 := by omega
    simp only [hko.neg_one_pow, h0, ite_false]
    split_ifs <;> simp

/-! ### The Hoggar sign pattern -/

/-- Encoding of a point as a natural number: `∑ aᵢ 2^i + ∑ cᵢ 2^(N+i)`. -/
def enc (u : Pt N) : ℕ := ∑ i : Fin N, ((u.1 i).val * 2 ^ i.val + (u.2 i).val * 2 ^ (N + i.val))

/-- Bit `enc u` is set iff `⟨ψ|P_u|ψ⟩ < 0` for the Hoggar fiducial. -/
def hoggarNegMask : ℕ := 0x163e5efe76fefe00

/-- The Hoggar sign pattern as an integer assignment. -/
def hogZ (u : Pt 3) : ℤ := if Nat.testBit hoggarNegMask (enc u) then -1 else 1

/-- The Hoggar sign pattern as a real assignment. -/
def hog (u : Pt 3) : ℝ := ((hogZ u : ℤ) : ℝ)

lemma hog_pm (u : Pt 3) : hog u = 1 ∨ hog u = -1 := by
  unfold hog hogZ; split_ifs <;> simp

/-- Computable description of the violated flags. -/
lemma violated_hog (S : Finset (Pt 3)) :
    violated S hog = (flags S).filter
      (fun p => hogZ p.1 * hogZ p.2 * hogZ (p.1 + p.2) ≠ lsign p.1 p.2) := by
  ext p
  simp only [violated, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hne⟩
    refine ⟨hp, fun h => hne ?_⟩
    rw [lineSign_eq_lsign (mem_flags.1 hp).2.2.2, ← h]
    simp [hog]
  · rintro ⟨hp, hne⟩
    refine ⟨hp, fun h => hne ?_⟩
    rw [lineSign_eq_lsign (mem_flags.1 hp).2.2.2] at h
    have : ((hogZ p.1 * hogZ p.2 * hogZ (p.1 + p.2) : ℤ) : ℝ) = ((lsign p.1 p.2 : ℤ) : ℝ) := by
      push_cast; simpa [hog] using h
    exact_mod_cast this

/-- Flags of a set given by a predicate, as a filter on all pairs (cheap to evaluate). -/
lemma flags_filter (P : Pt N → Prop) [DecidablePred P] :
    flags (univ.filter P) = (univ ×ˢ univ).filter
      (fun p : Pt N × Pt N => P p.1 ∧ P p.2 ∧ P (p.1 + p.2) ∧ symp p.1 p.2 = 0) := by
  ext p
  simp [flags, Finset.mem_filter, and_assoc]

lemma allPoints_eq_filter : allPoints N = univ.filter (fun u : Pt N => u ≠ 0) := by
  ext u; simp [allPoints]

/-- Canonical anisotropic point `Y ⊗ I ⊗ I` defining `Q⁻(5,2)`. -/
def eY3 : Pt 3 := (fun i => if i = 0 then 1 else 0, fun i => if i = 0 then 1 else 0)

lemma qform_eY3 : qform eY3 = 1 := by decide

/-- Kernel computation: the Hoggar pattern violates exactly 63 contexts of `W(5,2)`. -/
theorem hog_lines_all :
    ((((univ ×ˢ univ).filter (fun p : Pt 3 × Pt 3 =>
        p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 + p.2 ≠ 0 ∧ symp p.1 p.2 = 0)).filter
      (fun p => hogZ p.1 * hogZ p.2 * hogZ (p.1 + p.2) ≠ lsign p.1 p.2)).image lineOf).card = 63 := by
  decide +kernel

/-- Kernel computation: the Hoggar pattern violates exactly 9 contexts of `Q⁻(5,2)`. -/
theorem hog_lines_ell :
    ((((univ ×ˢ univ).filter (fun p : Pt 3 × Pt 3 =>
        (p.1 ≠ 0 ∧ qformShift eY3 p.1 = 0) ∧ (p.2 ≠ 0 ∧ qformShift eY3 p.2 = 0)
        ∧ (p.1 + p.2 ≠ 0 ∧ qformShift eY3 (p.1 + p.2) = 0) ∧ symp p.1 p.2 = 0)).filter
      (fun p => hogZ p.1 * hogZ p.2 * hogZ (p.1 + p.2) ≠ lsign p.1 p.2)).image lineOf).card = 9 := by
  decide +kernel

/-! ### Exact contextuality degrees -/

/-- **`d(W(5,2)) = 63`.** Every `±1` assignment of the 63 three-qubit observables violates at
least 63 of the 315 contexts, and the Hoggar sign pattern violates exactly 63. -/
theorem degree_three_qubit :
    (∀ f : Pt 3 → ℝ, (∀ u ∈ allPoints 3, f u = 1 ∨ f u = -1) →
        63 ≤ (violatedLines (allPoints 3) f).card) ∧
      ∃ f : Pt 3 → ℝ, (∀ u, f u = 1 ∨ f u = -1) ∧ (violatedLines (allPoints 3) f).card = 63 :=
  ⟨three_qubit_contexts, hog, hog_pm, by
    rw [violatedLines, violated_hog, allPoints_eq_filter, flags_filter]; exact hog_lines_all⟩

/-- **`d(Q⁻(5,2)) = 9`.** -/
theorem degree_three_qubit_elliptic :
    (∀ f : Pt 3 → ℝ, (∀ u ∈ ellipticPoints 3 eY3, f u = 1 ∨ f u = -1) →
        9 ≤ (violatedLines (ellipticPoints 3 eY3) f).card) ∧
      ∃ f : Pt 3 → ℝ, (∀ u, f u = 1 ∨ f u = -1) ∧
        (violatedLines (ellipticPoints 3 eY3) f).card = 9 :=
  ⟨three_qubit_elliptic_contexts eY3 qform_eY3, hog, hog_pm, by
    rw [violatedLines, violated_hog, ellipticPoints, flags_filter]; exact hog_lines_ell⟩

end HoggarBound
