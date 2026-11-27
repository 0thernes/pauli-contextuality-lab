/-
Hoggar Bound Lab — Theorem 24 (All-`N` `PG(N-1,2)` Rigidity & Imaginary-Completion No-Go Theorem).

Motivated by Metod Saniga's 26 Nov 2026 question regarding `PG(7,2)`-centered contextuality
searches on the eight-qubit symplectic polar space `W(15,2)`:

For EVERY `N ≥ 1` (`D = 2^N`), fix the canonical `PG(N-1,2)`-centered CSS assignment `pgCssSign N`
on the hyperbolic quadric `Q⁺(2N-1,2) = realPoints N`, which sets `f = +1` on the pure-`Z` solid
`a = 0` and pure-`X` solid `c = 0`, and `f(a, c) = -(-1)^{ycount(a,c)/2}` on all mixed real points.

Main results (zero `sorry`, zero `native_decide`, zero `decide +kernel`, strictly
`[propext, Classical.choice, Quot.sound]`):
* `opA_realPoints_pgCssSign_decomp`: Exact all-`N` rank-two plus scalar decomposition
  `A_real = μ_+ P_+ + μ_- P_- - 3 I`, where `μ_± = (3D ± √D (D - 4)) / 2` and `P_±` are explicit
  orthogonal real rank-one projectors.
* `trace_opA_realPoints_pgCssSign_cube`: Exact cubic trace
  `Re tr(A_real³) = 9 · D (D - 1)(D - 2)(D - 4) / 4`.
* `pgCssSign_violatedLines_real`: Exact all-`N` forced violation count on `Q⁺(2N-1,2)`:
  `96 · |violatedLines (realPoints N) (pgCssSign N)| = (D - 1)(D - 2)(D² - 12D + 80)`.
* `two_trace_proj_mul_sq_le_of_skew`: Skew-symmetric Hermitian Frobenius inequality
  `2 · Re tr(P T²) ≤ Re tr(T²)` for any real rank-one projector `P` and skew-symmetric Hermitian `T`.
* `pg_rigidity_lower_bound_all_N`: Exact all-`N` (`N ≥ 4`) imaginary-completion no-go bound:
  every `±1` extension `f` of `pgCssSign N` to `W(2N-1,2)` satisfies
  `#outsideFlags - 2 · #violatedOutsideFlags ≤ 3 · ((D - 4)(√D + 3) / 4) · |imagPoints N|`.
* Concrete corollaries for `N = 4, 5, 6, 7, 8`:
  - `pg_rigidity_n4`: `1,575 ≤ |violatedLines (allPoints 4) f|`
  - `pg_rigidity_n5`: `31,081 ≤ |violatedLines (allPoints 5) f|`
  - `pg_rigidity_n6`: `571,095 ≤ |violatedLines (allPoints 6) f|`
  - `pg_rigidity_n7`: `9,907,702 ≤ |violatedLines (allPoints 7) f|`
  - `pg_rigidity_n8`: `166,115,415 ≤ |violatedLines (allPoints 8) f|`
    (strictly above the verified `W(15,2)` witness `161,360,335` by `4,755,080` contexts).
-/
import HoggarBound.Quadric
import HoggarBound.IndependentContexts
import HoggarBound.Kramers

open Finset Matrix HoggarBound

namespace HoggarBound.PGRigidity

variable {N : ℕ}

/-! ### Part 1. Imaginary points and canonical `PG(N-1,2)`-centered real assignment -/

/-- The imaginary Pauli observables (`qform u = 1`, odd number of `Y` factors). -/
def imagPoints (N : ℕ) : Finset (Pt N) :=
  univ.filter fun u => qform u = 1

lemma mem_imagPoints {u : Pt N} : u ∈ imagPoints N ↔ qform u = 1 := by
  simp [imagPoints]

lemma zero_not_mem_imagPoints : (0 : Pt N) ∉ imagPoints N := by
  simp [imagPoints, qform_zero]

lemma card_imagPoints (N : ℕ) : 2 * (imagPoints N).card + 2 ^ N = 4 ^ N := by
  have h0 := card_qzero (N := N)
  have hsplit := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Pt N)))
    (fun u : Pt N => qform u = 0)
  have h1 : (univ.filter fun u : Pt N => ¬ qform u = 0) = imagPoints N := by
    ext u
    simp only [imagPoints, mem_filter, mem_univ, true_and]
    rcases zmod2_cases (qform u) with h | h <;> simp [h]
  rw [h1, Finset.card_univ, card_pt] at hsplit
  omega

/-- The canonical `PG(N-1,2)`-centered CSS assignment on `Q⁺(2N-1,2)`:
`+1` on the pure-`Z` solid (`a = 0`) and pure-`X` solid (`c = 0`), and `-(-1)^{ycount(u)/2}`
on all mixed real observables (`a ≠ 0`, `c ≠ 0`, `qform u = 0`). -/
def pgCssSign (N : ℕ) (u : Pt N) : ℝ :=
  if u.1 = 0 ∨ u.2 = 0 then 1 else -((-1 : ℝ) ^ (ycount u / 2))

lemma pgCssSign_values (N : ℕ) (u : Pt N) : pgCssSign N u = 1 ∨ pgCssSign N u = -1 := by
  unfold pgCssSign
  split_ifs
  · exact Or.inl rfl
  · rcases neg_one_pow_eq_or ℝ (ycount u / 2) with h | h <;> simp [h]

private lemma ycount_eq_zero_of_fst_or_snd_zero {u : Pt N} (h : u.1 = 0 ∨ u.2 = 0) :
    ycount u = 0 := by
  unfold ycount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  rcases h with h1 | h2
  · simp [h1, h01]
  · simp [h2, h01]

private lemma pgCssSign_smul_pauli_real {u : Pt N} (hq : qform u = 0) :
    ((pgCssSign N u : ℝ) : ℂ) • pauli u =
      (if u.1 = 0 ∨ u.2 = 0 then (1 : ℂ) else -1) • weyl u := by
  unfold pgCssSign pauli
  split_ifs with h
  · rw [ycount_eq_zero_of_fst_or_snd_zero h]
    simp
  · rw [smul_smul]
    congr 1
    have heven : 2 ∣ ycount u := by
      have h0 : ((ycount u : ℕ) : ZMod 2) = 0 := by rw [← dot_eq_ycount]; exact hq
      exact (ZMod.natCast_eq_zero_iff _ _).mp h0
    obtain ⟨k, hk⟩ := heven
    have hdiv : ycount u / 2 = k := by omega
    rw [hdiv, hk, pow_mul, Complex.I_sq]
    push_cast
    have hsq : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by rw [← mul_pow]; simp
    linear_combination -hsq

/-! ### Part 2. Exact entrywise formula & rank-two decomposition of `A_real` -/

private lemma sum_chi_eq_comm (v : Vec N) :
    ∑ c : Vec N, chi c v = if v = 0 then (2 : ℂ) ^ N else 0 := by
  have : ∀ c : Vec N, chi c v = chi v c := fun c => by unfold chi; rw [dotProduct_comm]
  simp_rw [this]
  exact sum_chi v

/-- Exact entrywise formula for `A_real = opA (realPoints N) (pgCssSign N)` for every `N`. -/
theorem opA_realPoints_pgCssSign_apply (N : ℕ) (x y : Vec N) :
    opA (realPoints N) (pgCssSign N) x y =
      (if x = 0 ∧ y = 0 then 2 * (2 : ℂ) ^ N else 0) + 2
        - ((2 : ℂ) ^ N / 2) * ((if x = 0 then 1 else 0) + (if y = 0 then 1 else 0))
        - (if x = y then 3 else 0) := by
  unfold opA
  have hcongr : ∑ u ∈ realPoints N, ((pgCssSign N u : ℝ) : ℂ) • pauli u =
      ∑ u ∈ realPoints N, (if u.1 = 0 ∨ u.2 = 0 then (1 : ℂ) else -1) • weyl u :=
    Finset.sum_congr rfl fun u hu => pgCssSign_smul_pauli_real (Finset.mem_filter.mp hu).2.2
  rw [hcongr]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [realPoints, Finset.sum_filter, Fintype.sum_prod_type]
  have houter : ∀ a : Vec N,
      (∑ c : Vec N, if (a, c) ≠ 0 ∧ qform (a, c) = 0 then
          (if a = 0 ∨ c = 0 then (1 : ℂ) else -1) * weyl (a, c) x y else 0) =
      if a = x + y then
        ∑ c : Vec N, if (a, c) ≠ 0 ∧ qform (a, c) = 0 then
          (if a = 0 ∨ c = 0 then (1 : ℂ) else -1) * chi c y else 0
      else 0 := by
    intro a
    by_cases ha : a = x + y
    · subst ha
      rw [ite_eq_left rfl]
      refine Finset.sum_congr rfl fun c _ => ?_
      have hxy : x = y + (x + y) := by
        calc x = x + (y + y) := by rw [vec_add_self, add_zero]
          _ = y + (x + y) := by abel
      unfold weyl
      rw [ite_eq_left hxy]
    · rw [ite_eq_right ha]
      refine Finset.sum_eq_zero fun c _ => ?_
      have hne : x ≠ y + a := by
        intro h
        apply ha
        calc a = (y + y) + a := by rw [vec_add_self, zero_add]
          _ = (y + a) + y := by abel
          _ = x + y := by rw [h]
      simp only [weyl, hne, ↓reduceIte, mul_zero, ite_self]
  simp_rw [houter]
  rw [Finset.sum_ite_eq']
  simp only [mem_univ, ↓reduceIte]
  by_cases hxy : x = y
  · subst hxy
    have hxx : x + x = 0 := vec_add_self x
    rw [hxx]
    have hinner : ∀ c : Vec N,
        (if ((0 : Vec N), c) ≠ 0 ∧ qform ((0 : Vec N), c) = 0 then
            (if (0 : Vec N) = 0 ∨ c = 0 then (1 : ℂ) else -1) * chi c x else 0) =
        if c = 0 then 0 else chi c x := by
      intro c
      have hq : qform ((0 : Vec N), c) = 0 := by simp [qform]
      by_cases hc : c = 0
      · subst hc; simp
      · have hne : ((0 : Vec N), c) ≠ 0 := fun h => hc (congrArg Prod.snd h)
        rw [ite_eq_left ⟨hne, hq⟩, ite_eq_left (Or.inl rfl), one_mul, ite_eq_right hc]
    rw [Finset.sum_congr rfl fun c _ => hinner c]
    have hsum : (∑ c : Vec N, if c = 0 then (0 : ℂ) else chi c x) =
        (∑ c : Vec N, chi c x) - 1 := by
      have hsplit : ∑ c : Vec N, chi c x =
          (∑ c : Vec N, if c = 0 then chi c x else 0) +
          (∑ c : Vec N, if c = 0 then 0 else chi c x) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        split_ifs <;> simp
      have hzero : (∑ c : Vec N, if c = 0 then chi c x else 0) = 1 := by
        rw [Finset.sum_ite_eq']; simp
      rw [hzero] at hsplit
      linear_combination -hsplit
    rw [hsum, sum_chi_eq_comm]
    by_cases hx0 : x = 0 <;> simp [hx0] <;> ring
  · have ha0 : x + y ≠ 0 := by
      intro h
      apply hxy
      calc x = x + (y + y) := by rw [vec_add_self, add_zero]
        _ = (x + y) + y := by abel
        _ = y := by rw [h, zero_add]
    have hinner : ∀ c : Vec N,
        (if (x + y, c) ≠ 0 ∧ qform (x + y, c) = 0 then
            (if x + y = 0 ∨ c = 0 then (1 : ℂ) else -1) * chi c y else 0) =
        (if c = 0 then (2 : ℂ) else 0) - (if qform (x + y, c) = 0 then chi c y else 0) := by
      intro c
      have hne : (x + y, c) ≠ 0 := fun h => ha0 (congrArg Prod.fst h)
      by_cases hc : c = 0
      · subst hc; simp [qform, ha0]; ring
      · by_cases hq : qform (x + y, c) = 0
        · simp [hne, ha0, hc, hq]
        · simp [hne, hc, hq]
    simp_rw [hinner, Finset.sum_sub_distrib]
    have hfirst : (∑ c : Vec N, if c = 0 then (2 : ℂ) else 0) = 2 := by
      rw [Finset.sum_ite_eq']; simp
    have hsecond : (∑ c : Vec N, if qform (x + y, c) = 0 then chi c y else 0) =
        ((2 : ℂ) ^ N / 2) * ((if x = 0 then 1 else 0) + (if y = 0 then 1 else 0)) := by
      have hind : ∀ c : Vec N, (if qform (x + y, c) = 0 then chi c y else 0) =
          (chi c y + chi c x) / 2 := by
        intro c
        have h1 : (if qform (x + y, c) = 0 then chi c y else 0) =
            (if qform (x + y, c) = 0 then (1 : ℂ) else 0) * chi c y := by
          split_ifs <;> simp
        rw [h1, indicator_eq]
        have hq : eps (qform (x + y, c)) = chi c (x + y) := rfl
        rw [hq, div_mul_eq_mul_div, add_mul, one_mul, ← chi_add_right]
        have hxyy : x + y + y = x := by rw [add_assoc, vec_add_self, add_zero]
        rw [hxyy]
      simp_rw [hind, ← Finset.sum_div, Finset.sum_add_distrib, sum_chi_eq_comm]
      by_cases hx0 : x = 0 <;> by_cases hy0 : y = 0 <;> simp [hx0, hy0]
      ring
    rw [hfirst, hsecond, ite_eq_right hxy]
    have hnot00 : ¬ (x = 0 ∧ y = 0) := fun ⟨h1, h2⟩ => hxy (h1.trans h2.symm)
    rw [ite_eq_right hnot00]
    ring

/-! ### Part 3. Explicit orthogonal real eigenvectors `w_+`, `w_-` and exact cubic trace -/

/-- Unnormalized top real eigenvector `w_+` of `A_real`. -/
noncomputable def wPlus (N : ℕ) (x : Vec N) : ℝ :=
  if x = 0 then (2 : ℝ) ^ N - 1 else -(Real.sqrt ((2 : ℝ) ^ N) + 1)

/-- Unnormalized second real eigenvector `w_-` of `A_real`. -/
noncomputable def wMinus (N : ℕ) (x : Vec N) : ℝ :=
  if x = 0 then (2 : ℝ) ^ N - 1 else Real.sqrt ((2 : ℝ) ^ N) - 1

/-- Squared Euclidean norm `‖w_+‖² = 2 √D (D - 1) (√D + 1)`. -/
noncomputable def nPlus (N : ℕ) : ℝ :=
  2 * Real.sqrt ((2 : ℝ) ^ N) * ((2 : ℝ) ^ N - 1) * (Real.sqrt ((2 : ℝ) ^ N) + 1)

/-- Squared Euclidean norm `‖w_-‖² = 2 √D (D - 1) (√D - 1)`. -/
noncomputable def nMinus (N : ℕ) : ℝ :=
  2 * Real.sqrt ((2 : ℝ) ^ N) * ((2 : ℝ) ^ N - 1) * (Real.sqrt ((2 : ℝ) ^ N) - 1)

/-- Shifted top eigenvalue `μ_+ = γ_+ + 3 = (3D + √D (D - 4)) / 2`. -/
noncomputable def muPlus (N : ℕ) : ℝ :=
  (3 * (2 : ℝ) ^ N + Real.sqrt ((2 : ℝ) ^ N) * ((2 : ℝ) ^ N - 4)) / 2

/-- Shifted second eigenvalue `μ_- = γ_- + 3 = (3D - √D (D - 4)) / 2`. -/
noncomputable def muMinus (N : ℕ) : ℝ :=
  (3 * (2 : ℝ) ^ N - Real.sqrt ((2 : ℝ) ^ N) * ((2 : ℝ) ^ N - 4)) / 2

/-- Real rank-one matrix `|u⟩⟨v|` lifted to `Matrix (Vec N) (Vec N) ℂ`. -/
def rankOnePair (u v : Vec N → ℝ) : Matrix (Vec N) (Vec N) ℂ :=
  Matrix.of fun x y => ((u x * v y : ℝ) : ℂ)

/-- Real rank-one matrix `|v⟩⟨v|` lifted to `Matrix (Vec N) (Vec N) ℂ`. -/
def rankOne (v : Vec N → ℝ) : Matrix (Vec N) (Vec N) ℂ :=
  rankOnePair v v

/-- Normalized real rank-one projector `P_+ = |w_+⟩⟨w_+| / ‖w_+‖²`. -/
noncomputable def projPlus (N : ℕ) : Matrix (Vec N) (Vec N) ℂ :=
  (((1 / nPlus N : ℝ) : ℂ)) • rankOne (wPlus N)

/-- Normalized real rank-one projector `P_- = |w_-⟩⟨w_-| / ‖w_-‖²`. -/
noncomputable def projMinus (N : ℕ) : Matrix (Vec N) (Vec N) ℂ :=
  (((1 / nMinus N : ℝ) : ℂ)) • rankOne (wMinus N)

private lemma sqrt_two_pow_sq (N : ℕ) : Real.sqrt ((2 : ℝ) ^ N) ^ 2 = (2 : ℝ) ^ N :=
  Real.sq_sqrt (by positivity)

private lemma sqrt_two_pow_gt_one {N : ℕ} (hN : 1 ≤ N) : (1 : ℝ) < Real.sqrt ((2 : ℝ) ^ N) := by
  have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ N := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
  rw [Real.lt_sqrt (by norm_num)]
  linarith

private lemma nPlus_pos {N : ℕ} (hN : 1 ≤ N) : 0 < nPlus N := by
  have hs := sqrt_two_pow_gt_one hN
  have hD : (2 : ℝ) ≤ (2 : ℝ) ^ N := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
  unfold nPlus
  have h1 : 0 < Real.sqrt ((2 : ℝ) ^ N) := by linarith
  have h2 : 0 < (2 : ℝ) ^ N - 1 := by linarith
  have h3 : 0 < Real.sqrt ((2 : ℝ) ^ N) + 1 := by linarith
  positivity

private lemma nMinus_pos {N : ℕ} (hN : 1 ≤ N) : 0 < nMinus N := by
  have hs := sqrt_two_pow_gt_one hN
  have hD : (2 : ℝ) ≤ (2 : ℝ) ^ N := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
  unfold nMinus
  have h1 : 0 < Real.sqrt ((2 : ℝ) ^ N) := by linarith
  have h2 : 0 < (2 : ℝ) ^ N - 1 := by linarith
  have h3 : 0 < Real.sqrt ((2 : ℝ) ^ N) - 1 := by linarith
  positivity

private lemma sum_if_zero_vec (a b : ℝ) :
    (∑ x : Vec N, if x = 0 then a else b) = a + ((2 : ℝ) ^ N - 1) * b := by
  have hcard : ((univ.erase (0 : Vec N)).card : ℝ) = (2 : ℝ) ^ N - 1 := by
    have h1 : (univ.erase (0 : Vec N)).card + 1 = 2 ^ N := by
      rw [Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, card_vec]
      have hpos : 1 ≤ 2 ^ N := Nat.one_le_two_pow
      omega
    have h2 : ((univ.erase (0 : Vec N)).card : ℝ) + 1 = (2 : ℝ) ^ N := by exact_mod_cast h1
    linarith
  rw [← Finset.add_sum_erase _ _ (mem_univ (0 : Vec N))]
  simp only [↓reduceIte]
  have hrest : ∑ x ∈ univ.erase (0 : Vec N), (if x = 0 then a else b) =
      ∑ _x ∈ univ.erase (0 : Vec N), b :=
    Finset.sum_congr rfl fun x hx => ite_eq_right (Finset.ne_of_mem_erase hx)
  rw [hrest, Finset.sum_const, nsmul_eq_mul, hcard]

private lemma wPlus_dot_wPlus (N : ℕ) : ∑ x : Vec N, wPlus N x * wPlus N x = nPlus N := by
  have hterm : ∀ x : Vec N, wPlus N x * wPlus N x =
      if x = 0 then ((2 : ℝ) ^ N - 1) ^ 2 else (Real.sqrt ((2 : ℝ) ^ N) + 1) ^ 2 := by
    intro x; unfold wPlus; split_ifs <;> ring
  simp_rw [hterm, sum_if_zero_vec]
  unfold nPlus
  have hs := sqrt_two_pow_sq N
  linear_combination -((2 : ℝ) ^ N - 1) * hs

private lemma wMinus_dot_wMinus (N : ℕ) : ∑ x : Vec N, wMinus N x * wMinus N x = nMinus N := by
  have hterm : ∀ x : Vec N, wMinus N x * wMinus N x =
      if x = 0 then ((2 : ℝ) ^ N - 1) ^ 2 else (Real.sqrt ((2 : ℝ) ^ N) - 1) ^ 2 := by
    intro x; unfold wMinus; split_ifs <;> ring
  simp_rw [hterm, sum_if_zero_vec]
  unfold nMinus
  have hs := sqrt_two_pow_sq N
  linear_combination -((2 : ℝ) ^ N - 1) * hs

private lemma wPlus_dot_wMinus (N : ℕ) : ∑ x : Vec N, wPlus N x * wMinus N x = 0 := by
  have hterm : ∀ x : Vec N, wPlus N x * wMinus N x =
      if x = 0 then ((2 : ℝ) ^ N - 1) ^ 2
      else -(Real.sqrt ((2 : ℝ) ^ N) + 1) * (Real.sqrt ((2 : ℝ) ^ N) - 1) := by
    intro x; unfold wPlus wMinus; split_ifs <;> ring
  simp_rw [hterm, sum_if_zero_vec]
  have hs := sqrt_two_pow_sq N
  linear_combination -((2 : ℝ) ^ N - 1) * hs

private lemma rankOne_mul_rankOne (u v : Vec N → ℝ) :
    rankOne u * rankOne v = (((∑ z : Vec N, u z * v z : ℝ) : ℂ)) • rankOnePair u v := by
  ext x y
  simp only [Matrix.mul_apply, rankOne, rankOnePair, Matrix.of_apply, Matrix.smul_apply,
    smul_eq_mul, Complex.ofReal_sum]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  push_cast; ring

private lemma projPlus_mul_self {N : ℕ} (hN : 1 ≤ N) :
    projPlus N * projPlus N = projPlus N := by
  unfold projPlus
  rw [Matrix.smul_mul, Matrix.mul_smul, rankOne_mul_rankOne, wPlus_dot_wPlus,
    show rankOnePair (wPlus N) (wPlus N) = rankOne (wPlus N) from rfl,
    smul_smul, smul_smul]
  have hne : (nPlus N : ℝ) ≠ 0 := ne_of_gt (nPlus_pos hN)
  congr 1
  exact_mod_cast (by field_simp [hne] : (1 / nPlus N) * (1 / nPlus N) * nPlus N = 1 / nPlus N)

private lemma projMinus_mul_self {N : ℕ} (hN : 1 ≤ N) :
    projMinus N * projMinus N = projMinus N := by
  unfold projMinus
  rw [Matrix.smul_mul, Matrix.mul_smul, rankOne_mul_rankOne, wMinus_dot_wMinus,
    show rankOnePair (wMinus N) (wMinus N) = rankOne (wMinus N) from rfl,
    smul_smul, smul_smul]
  have hne : (nMinus N : ℝ) ≠ 0 := ne_of_gt (nMinus_pos hN)
  congr 1
  exact_mod_cast (by field_simp [hne] : (1 / nMinus N) * (1 / nMinus N) * nMinus N = 1 / nMinus N)

private lemma projPlus_mul_projMinus (N : ℕ) : projPlus N * projMinus N = 0 := by
  unfold projPlus projMinus
  rw [Matrix.smul_mul, Matrix.mul_smul, rankOne_mul_rankOne, wPlus_dot_wMinus]
  simp

private lemma projMinus_mul_projPlus (N : ℕ) : projMinus N * projPlus N = 0 := by
  unfold projPlus projMinus
  rw [Matrix.smul_mul, Matrix.mul_smul, rankOne_mul_rankOne]
  have h0 : ∑ z : Vec N, wMinus N z * wPlus N z = 0 := by
    rw [← wPlus_dot_wMinus N]
    refine Finset.sum_congr rfl fun z _ => mul_comm _ _
  rw [h0]
  simp

private lemma trace_projPlus {N : ℕ} (hN : 1 ≤ N) : (projPlus N).trace = 1 := by
  unfold projPlus
  rw [Matrix.trace_smul, smul_eq_mul, Matrix.trace]
  simp only [Matrix.diag_apply, rankOne, rankOnePair, Matrix.of_apply, ← Complex.ofReal_sum,
    wPlus_dot_wPlus]
  have hne : (nPlus N : ℝ) ≠ 0 := ne_of_gt (nPlus_pos hN)
  exact_mod_cast (by field_simp [hne] : (1 / nPlus N) * nPlus N = 1)

private lemma trace_projMinus {N : ℕ} (hN : 1 ≤ N) : (projMinus N).trace = 1 := by
  unfold projMinus
  rw [Matrix.trace_smul, smul_eq_mul, Matrix.trace]
  simp only [Matrix.diag_apply, rankOne, rankOnePair, Matrix.of_apply, ← Complex.ofReal_sum,
    wMinus_dot_wMinus]
  have hne : (nMinus N : ℝ) ≠ 0 := ne_of_gt (nMinus_pos hN)
  exact_mod_cast (by field_simp [hne] : (1 / nMinus N) * nMinus N = 1)

private lemma projPlus_isHermitian (N : ℕ) : (projPlus N).IsHermitian := by
  unfold Matrix.IsHermitian projPlus
  ext x y
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, rankOne, rankOnePair, Matrix.of_apply,
    smul_eq_mul, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
  ring

private lemma projMinus_isHermitian (N : ℕ) : (projMinus N).IsHermitian := by
  unfold Matrix.IsHermitian projMinus
  ext x y
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, rankOne, rankOnePair, Matrix.of_apply,
    smul_eq_mul, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
  ring

/-- **Exact all-`N` rank-two plus scalar spectral decomposition of `A_real`:**
`opA (realPoints N) (pgCssSign N) = μ_+ P_+ + μ_- P_- - 3 I`. -/
theorem opA_realPoints_pgCssSign_decomp {N : ℕ} (hN : 1 ≤ N) :
    opA (realPoints N) (pgCssSign N) =
      ((muPlus N : ℝ) : ℂ) • projPlus N + ((muMinus N : ℝ) : ℂ) • projMinus N - (3 : ℂ) • 1 := by
  have hs := sqrt_two_pow_sq N
  set D : ℝ := (2 : ℝ) ^ N
  set s : ℝ := Real.sqrt D
  have hsp : s ≠ 0 := by have := sqrt_two_pow_gt_one hN; linarith
  have hDm1 : D - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ D := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
    linarith
  have hsp1 : s + 1 ≠ 0 := by have := sqrt_two_pow_gt_one hN; linarith
  have hsm1 : s - 1 ≠ 0 := by have := sqrt_two_pow_gt_one hN; linarith
  ext x y
  rw [opA_realPoints_pgCssSign_apply]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    projPlus, projMinus, rankOne, rankOnePair, Matrix.of_apply]
  by_cases hx : x = 0 <;> by_cases hy : y = 0
  · subst hx; subst hy
    simp only [↓reduceIte, and_self, mul_one, wPlus, wMinus]
    have hR : 2 * D + 2 - D / 2 * (1 + 1) - 3 =
        muPlus N * (1 / nPlus N * ((D - 1) * (D - 1))) +
        muMinus N * (1 / nMinus N * ((D - 1) * (D - 1))) - 3 := by
      unfold muPlus muMinus nPlus nMinus
      change 2 * D + 2 - D / 2 * (1 + 1) - 3 =
        (3 * D + s * (D - 4)) / 2 * (1 / (2 * s * (D - 1) * (s + 1)) * ((D - 1) * (D - 1))) +
        (3 * D - s * (D - 4)) / 2 * (1 / (2 * s * (D - 1) * (s - 1)) * ((D - 1) * (D - 1))) - 3
      field_simp [hsp, hDm1, hsp1, hsm1]
      linear_combination (4 * s * (D + 2)) * hs
    have hC := congrArg (fun r : ℝ => (r : ℂ)) hR
    push_cast [D, s] at hC ⊢
    exact hC
  · subst hx
    have hne : (0 : Vec N) ≠ y := fun h => hy h.symm
    simp only [hy, hne, ↓reduceIte, and_false, add_zero, zero_add, mul_zero, sub_zero, wPlus, wMinus]
    have hR : 2 - D / 2 * 1 =
        muPlus N * (1 / nPlus N * ((D - 1) * -(s + 1))) +
        muMinus N * (1 / nMinus N * ((D - 1) * (s - 1))) := by
      unfold muPlus muMinus nPlus nMinus
      change 2 - D / 2 * 1 =
        (3 * D + s * (D - 4)) / 2 * (1 / (2 * s * (D - 1) * (s + 1)) * ((D - 1) * -(s + 1))) +
        (3 * D - s * (D - 4)) / 2 * (1 / (2 * s * (D - 1) * (s - 1)) * ((D - 1) * (s - 1)))
      field_simp [hsp, hDm1, hsp1, hsm1]
      ring
    have hC := congrArg (fun r : ℝ => (r : ℂ)) hR
    push_cast [D, s] at hC ⊢
    exact hC
  · subst hy
    simp only [hx, ↓reduceIte, false_and, zero_add, mul_zero, sub_zero, wPlus, wMinus]
    have hR : 2 - D / 2 * 1 =
        muPlus N * (1 / nPlus N * (-(s + 1) * (D - 1))) +
        muMinus N * (1 / nMinus N * ((s - 1) * (D - 1))) := by
      unfold muPlus muMinus nPlus nMinus
      change 2 - D / 2 * 1 =
        (3 * D + s * (D - 4)) / 2 * (1 / (2 * s * (D - 1) * (s + 1)) * (-(s + 1) * (D - 1))) +
        (3 * D - s * (D - 4)) / 2 * (1 / (2 * s * (D - 1) * (s - 1)) * ((s - 1) * (D - 1)))
      field_simp [hsp, hDm1, hsp1, hsm1]
      ring
    have hC := congrArg (fun r : ℝ => (r : ℂ)) hR
    push_cast [D, s] at hC ⊢
    exact hC
  · simp only [hx, hy, ↓reduceIte, and_self, add_zero, zero_add, mul_zero, sub_zero, wPlus, wMinus]
    have hR : (2 : ℝ) =
        muPlus N * (1 / nPlus N * (-(s + 1) * -(s + 1))) +
        muMinus N * (1 / nMinus N * ((s - 1) * (s - 1))) := by
      unfold muPlus muMinus nPlus nMinus
      change (2 : ℝ) =
        (3 * D + s * (D - 4)) / 2 * (1 / (2 * s * (D - 1) * (s + 1)) * (-(s + 1) * -(s + 1))) +
        (3 * D - s * (D - 4)) / 2 * (1 / (2 * s * (D - 1) * (s - 1)) * ((s - 1) * (s - 1)))
      field_simp [hsp, hDm1, hsp1, hsm1]
      ring
    by_cases hxy : x = y
    · simp only [hxy, ↓reduceIte, mul_one]
      have hR2 : (2 : ℝ) - 3 =
          muPlus N * (1 / nPlus N * (-(s + 1) * -(s + 1))) +
          muMinus N * (1 / nMinus N * ((s - 1) * (s - 1))) - 3 := by linarith
      have hC := congrArg (fun r : ℝ => (r : ℂ)) hR2
      push_cast [D, s] at hC ⊢
      exact hC
    · simp only [hxy, ↓reduceIte, mul_zero, sub_zero]
      have hC := congrArg (fun r : ℝ => (r : ℂ)) hR
      push_cast [D, s] at hC ⊢
      exact hC

/-- Exact cubic trace of `A_real` for every `N ≥ 1`:
`Re tr(A_real³) = 9 · D (D - 1)(D - 2)(D - 4) / 4`. -/
theorem trace_opA_realPoints_pgCssSign_cube {N : ℕ} (hN : 1 ≤ N) :
    ((opA (realPoints N) (pgCssSign N) ^ 3).trace).re =
      9 * (2 : ℝ) ^ N * ((2 : ℝ) ^ N - 1) * ((2 : ℝ) ^ N - 2) * ((2 : ℝ) ^ N - 4) / 4 := by
  set P1 := projPlus N
  set P2 := projMinus N
  set a : ℂ := ((muPlus N : ℝ) : ℂ)
  set b : ℂ := ((muMinus N : ℝ) : ℂ)
  have hA : opA (realPoints N) (pgCssSign N) = a • P1 + b • P2 - (3 : ℂ) • 1 :=
    opA_realPoints_pgCssSign_decomp hN
  have h11 : P1 * P1 = P1 := projPlus_mul_self hN
  have h22 : P2 * P2 = P2 := projMinus_mul_self hN
  have h12 : P1 * P2 = 0 := projPlus_mul_projMinus N
  have h21 : P2 * P1 = 0 := projMinus_mul_projPlus N
  have hcube : (a • P1 + b • P2 - (3 : ℂ) • 1) ^ 3 =
      ((a - 3) ^ 3 + 27) • P1 + ((b - 3) ^ 3 + 27) • P2 - (27 : ℂ) • 1 := by
    rw [pow_three]
    simp only [sub_mul, add_mul, mul_sub, mul_add, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, one_mul, mul_one, h11, h22, h12, h21, smul_zero, add_zero, zero_add]
    ext x y
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hA, hcube, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_smul, trace_projPlus hN, trace_projMinus hN, Matrix.trace_one, card_vec]
  simp only [smul_eq_mul, mul_one, a, b]
  have hC : (((((muPlus N - 3) ^ 3 + 27) + ((muMinus N - 3) ^ 3 + 27) - 27 * (2 : ℝ) ^ N : ℝ) : ℂ)) =
      (((muPlus N : ℝ) : ℂ) - 3) ^ 3 + 27 + ((((muMinus N : ℝ) : ℂ) - 3) ^ 3 + 27) -
        27 * ((2 ^ N : ℕ) : ℂ) := by
    push_cast; ring
  rw [← hC, Complex.ofReal_re]
  unfold muPlus muMinus
  set D : ℝ := (2 : ℝ) ^ N
  set s : ℝ := Real.sqrt D
  have hs : s ^ 2 = D := sqrt_two_pow_sq N
  linear_combination (3 / 4 * (D - 4) ^ 2 * (3 * D - 6)) * hs

/-- **Exact all-`N` forced violation count of `pgCssSign N` on `Q⁺(2N-1,2)`:**
`96 · |violatedLines (realPoints N) (pgCssSign N)| = (D - 1)(D - 2)(D² - 12D + 80)`. -/
theorem pgCssSign_violatedLines_real {N : ℕ} (hN : 1 ≤ N) :
    96 * ((violatedLines (realPoints N) (pgCssSign N)).card : ℝ) =
      ((2 : ℝ) ^ N - 1) * ((2 : ℝ) ^ N - 2) * (((2 : ℝ) ^ N) ^ 2 - 12 * (2 : ℝ) ^ N + 80) := by
  have h0 : (0 : Pt N) ∉ realPoints N := by simp [realPoints]
  have hf : ∀ u ∈ realPoints N, pgCssSign N u = 1 ∨ pgCssSign N u = -1 := fun u _ =>
    pgCssSign_values N u
  have htr := trace_opA_realPoints_pgCssSign_cube hN
  rw [trace_opA_cube, Complex.ofReal_re, beta6_eq_card (realPoints N) (pgCssSign N) hf] at htr
  have hDpos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have hS_nat := card_realPoints (N := N)
  have hS : ((realPoints N).card : ℝ) = ((2 : ℝ) ^ N - 1) * ((2 : ℝ) ^ N + 2) / 2 := by
    have hR : 2 * ((realPoints N).card : ℝ) + 2 = (4 : ℝ) ^ N + (2 : ℝ) ^ N := by exact_mod_cast hS_nat
    have h42 : (4 : ℝ) ^ N = ((2 : ℝ) ^ N) ^ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm 2 N, pow_mul]
    rw [h42] at hR; linarith
  have hF_nat := card_flags_real (N := N)
  have hF : ((flags (realPoints N)).card : ℝ) =
      ((2 : ℝ) ^ N - 1) * ((2 : ℝ) ^ N + 2) * ((2 : ℝ) ^ N - 2) * ((2 : ℝ) ^ N + 4) / 8 := by
    have hR : 4 * ((flags (realPoints N)).card : ℝ) + 8 * ((realPoints N).card : ℝ) =
        ((realPoints N).card : ℝ) * ((4 : ℝ) ^ N + 2 * (2 : ℝ) ^ N) := by exact_mod_cast hF_nat
    have h42 : (4 : ℝ) ^ N = ((2 : ℝ) ^ N) ^ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm 2 N, pow_mul]
    rw [h42, hS] at hR; linarith
  have h6 : ((violated (realPoints N) (pgCssSign N)).card : ℝ) =
      6 * ((violatedLines (realPoints N) (pgCssSign N)).card : ℝ) := by
    exact_mod_cast card_violated_eq_six (realPoints N) h0 (pgCssSign N)
  have hcancel : ((flags (realPoints N)).card : ℝ) - 2 * ((violated (realPoints N) (pgCssSign N)).card : ℝ) =
      9 * ((2 : ℝ) ^ N - 1) * ((2 : ℝ) ^ N - 2) * ((2 : ℝ) ^ N - 4) / 4 := by
    have hmul : (2 : ℝ) ^ N * (((flags (realPoints N)).card : ℝ) -
          2 * ((violated (realPoints N) (pgCssSign N)).card : ℝ)) =
        (2 : ℝ) ^ N * (9 * ((2 : ℝ) ^ N - 1) * ((2 : ℝ) ^ N - 2) * ((2 : ℝ) ^ N - 4) / 4) := by
      linear_combination htr
    exact mul_left_cancel₀ (ne_of_gt hDpos) hmul
  rw [hF, h6] at hcancel
  linear_combination -8 * hcancel

/-! ### Part 4. Skew-symmetric Hermitian Frobenius inequality & outside-flag identity -/

private lemma opA_imag_transpose (f : Pt N → ℝ) :
    (opA (imagPoints N) f)ᵀ = -opA (imagPoints N) f := by
  unfold opA
  rw [Matrix.transpose_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hq : qform u = 1 := (Finset.mem_filter.mp hu).2
  have hstar : (pauli u).map star = -pauli u := by
    rw [pauli_map_star, hq, eps_one, neg_one_smul]
  have htr : (pauli u)ᵀ = -pauli u := by
    have hh : (pauli u)ᴴ = pauli u := (pauli_isHermitian u).eq
    ext x y
    have h1 := congrFun (congrFun hh y) x
    have h2 := congrFun (congrFun hstar x) y
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.neg_apply,
      Matrix.transpose_apply] at h1 h2 ⊢
    calc pauli u y x = star (pauli u x y) := h1.symm
      _ = -pauli u x y := h2
  rw [Matrix.transpose_smul, htr, smul_neg]

private lemma rankOne_mul_skew_mul_rankOne (v : Vec N → ℝ)
    {T : Matrix (Vec N) (Vec N) ℂ} (hskew : Tᵀ = -T) :
    rankOne v * T * rankOne v = 0 := by
  ext x y
  simp only [Matrix.mul_apply, rankOne, rankOnePair, Matrix.of_apply, Matrix.zero_apply]
  have hquad : ∑ a : Vec N, ∑ b : Vec N, ((v a : ℝ) : ℂ) * T a b * ((v b : ℝ) : ℂ) = 0 := by
    have hswap : ∑ a : Vec N, ∑ b : Vec N, ((v a : ℝ) : ℂ) * T a b * ((v b : ℝ) : ℂ) =
        -(∑ a : Vec N, ∑ b : Vec N, ((v a : ℝ) : ℂ) * T a b * ((v b : ℝ) : ℂ)) := by
      calc ∑ a : Vec N, ∑ b : Vec N, ((v a : ℝ) : ℂ) * T a b * ((v b : ℝ) : ℂ)
          = ∑ b : Vec N, ∑ a : Vec N, ((v a : ℝ) : ℂ) * T a b * ((v b : ℝ) : ℂ) := Finset.sum_comm
        _ = ∑ b : Vec N, ∑ a : Vec N, -(((v b : ℝ) : ℂ) * T b a * ((v a : ℝ) : ℂ)) := by
              refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
              have hba : T b a = -T a b := by
                simpa [Matrix.transpose_apply, Matrix.neg_apply] using congrFun (congrFun hskew a) b
              rw [hba]; ring
        _ = -(∑ b : Vec N, ∑ a : Vec N, ((v b : ℝ) : ℂ) * T b a * ((v a : ℝ) : ℂ)) := by
              simp only [Finset.sum_neg_distrib]
    have h2 : (2 : ℂ) * (∑ a : Vec N, ∑ b : Vec N, ((v a : ℝ) : ℂ) * T a b * ((v b : ℝ) : ℂ)) = 0 := by
      linear_combination hswap
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  have hfact2 : ∑ k : Vec N, (∑ j : Vec N, ((v x * v j : ℝ) : ℂ) * T j k) * ((v k * v y : ℝ) : ℂ) =
      ((v x * v y : ℝ) : ℂ) * ∑ j : Vec N, ∑ k : Vec N, ((v j : ℝ) : ℂ) * T j k * ((v k : ℝ) : ℂ) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast; ring
  rw [hfact2, hquad, mul_zero]

private lemma trace_conjTranspose_mul_self_re_nonneg {n : Type*} [Fintype n]
    (M : Matrix n n ℂ) : 0 ≤ ((Mᴴ * M).trace).re := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  have hre : (star (M j i) * M j i).re = (M j i).re ^ 2 + (M j i).im ^ 2 := by
    simp [Complex.mul_re]; ring
  rw [hre]
  positivity

/-- **Skew-symmetric Hermitian Frobenius inequality:**
If `P` is a Hermitian projector (`P² = P`, `Pᴴ = P`, `P T P = 0`) and `T` is Hermitian,
then `2 · Re tr(P T²) ≤ Re tr(T²)`. -/
theorem two_trace_proj_mul_sq_le_of_skew {P T : Matrix (Vec N) (Vec N) ℂ}
    (hPh : P.IsHermitian) (hP2 : P * P = P) (hTh : T.IsHermitian) (hPTP : P * T * P = 0) :
    2 * ((P * T ^ 2).trace).re ≤ ((T ^ 2).trace).re := by
  set Q : Matrix (Vec N) (Vec N) ℂ := 1 - P
  have hQh : Q.IsHermitian := by
    unfold Matrix.IsHermitian Q
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPh.eq]
  have hQ2 : Q * Q = Q := by
    simp only [Q, sub_mul, mul_sub, one_mul, mul_one, hP2]
    abel
  have hQTQh : (Q * T * Q).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQh.eq, hTh.eq, Matrix.mul_assoc]
  have hnonneg : 0 ≤ (((Q * T * Q) ^ 2).trace).re := by
    have h := trace_conjTranspose_mul_self_re_nonneg (Q * T * Q)
    rwa [hQTQh.eq, ← pow_two] at h
  have hdecomp : (T ^ 2).trace = 2 * (P * T ^ 2).trace + ((Q * T * Q) ^ 2).trace := by
    have hQTQ2 : ((Q * T * Q) ^ 2).trace = (Q * T * Q * T).trace := by
      rw [pow_two]
      calc (Q * T * Q * (Q * T * Q)).trace
          = (Q * (Q * T * Q * (Q * T))).trace := by
              have hc := Matrix.trace_mul_comm (Q * T * Q * (Q * T)) Q
              simpa only [Matrix.mul_assoc] using hc
        _ = (Q * T * Q * T).trace := by
              have h1 : Q * (Q * T * Q * (Q * T)) = (Q * Q) * T * (Q * Q) * T := by
                simp only [Matrix.mul_assoc]
              rw [h1, hQ2]
    have hexpand : (Q * T * Q * T).trace = (T ^ 2).trace - 2 * (P * T ^ 2).trace := by
      have h1 : Q * T * Q * T = T ^ 2 - P * T ^ 2 - T * P * T + P * T * P * T := by
        dsimp [Q]
        rw [pow_two]
        simp only [sub_mul, mul_sub, one_mul, mul_one, Matrix.mul_assoc]
        abel
      rw [h1, hPTP, Matrix.zero_mul, add_zero, Matrix.trace_sub, Matrix.trace_sub]
      have hTPT : (T * P * T).trace = (P * T ^ 2).trace := by
        rw [pow_two]
        calc (T * P * T).trace = (T * (T * P)).trace := Matrix.trace_mul_comm _ _
          _ = (T * T * P).trace := by rw [Matrix.mul_assoc]
          _ = (P * (T * T)).trace := Matrix.trace_mul_comm _ _
      rw [hTPT]; ring
    rw [hQTQ2, hexpand]; ring
  have hre : ((T ^ 2).trace).re = 2 * ((P * T ^ 2).trace).re + (((Q * T * Q) ^ 2).trace).re := by
    have := congrArg Complex.re hdecomp
    simpa using this
  linarith

private lemma trace_proj_mul_sq_re_nonneg {P T : Matrix (Vec N) (Vec N) ℂ}
    (hPh : P.IsHermitian) (hP2 : P * P = P) (hTh : T.IsHermitian) :
    0 ≤ ((P * T ^ 2).trace).re := by
  have h := trace_conjTranspose_mul_self_re_nonneg (P * T)
  have heq : ((P * T)ᴴ * (P * T)).trace = (P * T ^ 2).trace := by
    rw [Matrix.conjTranspose_mul, hTh.eq, hPh.eq, pow_two]
    calc (T * P * (P * T)).trace
        = (T * (P * P) * T).trace := by simp only [Matrix.mul_assoc]
      _ = (T * P * T).trace := by rw [hP2]
      _ = (T * (T * P)).trace := Matrix.trace_mul_comm _ _
      _ = (T * T * P).trace := by rw [Matrix.mul_assoc]
      _ = (P * (T * T)).trace := Matrix.trace_mul_comm _ _
  rwa [heq] at h

/-- Ordered pairs of commuting imaginary observables `(p, q)` whose product `p + q` is real. -/
private def imagFlags (N : ℕ) : Finset (Pt N × Pt N) :=
  (flags (allPoints N)).filter fun p => qform p.1 = 1 ∧ qform p.2 = 1

open Classical in
/-- Violated pairs inside `imagFlags N`. -/
private noncomputable def violatedImagFlags (N : ℕ) (f : Pt N → ℝ) : Finset (Pt N × Pt N) :=
  (violated (allPoints N) f).filter fun p => qform p.1 = 1 ∧ qform p.2 = 1

private lemma flags_outside_eq_three_imagFlags (N : ℕ) :
    3 * (imagFlags N).card + (flags (realPoints N)).card = (flags (allPoints N)).card := by
  classical
  set outF := (flags (allPoints N)).filter fun p => ¬ (qform p.1 = 0 ∧ qform p.2 = 0)
  have hreal_eq : (flags (allPoints N)).filter (fun p => qform p.1 = 0 ∧ qform p.2 = 0) =
      flags (realPoints N) := by
    ext p
    simp only [mem_filter, mem_flags, allPoints, realPoints, mem_erase, mem_univ, and_true, true_and]
    constructor
    · rintro ⟨⟨h1, h2, h3, hs⟩, hq1, hq2⟩
      exact ⟨⟨h1, hq1⟩, ⟨h2, hq2⟩, ⟨h3, by rw [qform_add, hq1, hq2, hs]; simp⟩, hs⟩
    · rintro ⟨⟨h1, hq1⟩, ⟨h2, hq2⟩, ⟨h3, _⟩, hs⟩
      exact ⟨⟨h1, h2, h3, hs⟩, hq1, hq2⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := flags (allPoints N))
    (fun p => qform p.1 = 0 ∧ qform p.2 = 0)
  rw [hreal_eq] at hsplit
  set C11 := outF.filter fun p => qform p.1 = 1 ∧ qform p.2 = 1
  set C01 := outF.filter fun p => qform p.1 = 0 ∧ qform p.2 = 1
  set C10 := outF.filter fun p => qform p.1 = 1 ∧ qform p.2 = 0
  have hC11 : C11 = imagFlags N := by
    ext p
    simp only [C11, outF, imagFlags, mem_filter]
    constructor
    · rintro ⟨⟨hp, _⟩, h1, h2⟩; exact ⟨hp, h1, h2⟩
    · rintro ⟨hp, h1, h2⟩
      exact ⟨⟨hp, fun h => absurd (h.1.symm.trans h1) (by decide)⟩, h1, h2⟩
  have hpart : outF = C11 ∪ (C01 ∪ C10) := by
    ext p
    simp only [C11, C01, C10, outF, mem_union, mem_filter]
    constructor
    · intro ⟨hp, hnot⟩
      rcases zmod2_cases (qform p.1) with h1 | h1 <;> rcases zmod2_cases (qform p.2) with h2 | h2
      · exact (hnot ⟨h1, h2⟩).elim
      · exact Or.inr (Or.inl ⟨⟨hp, hnot⟩, h1, h2⟩)
      · exact Or.inr (Or.inr ⟨⟨hp, hnot⟩, h1, h2⟩)
      · exact Or.inl ⟨⟨hp, hnot⟩, h1, h2⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hd1 : Disjoint C11 (C01 ∪ C10) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := (mem_filter.mp hp1).2
    rcases mem_union.mp hp2 with h | h
    · exact absurd ((mem_filter.mp h).2.1.symm.trans h1.1) (by decide)
    · exact absurd ((mem_filter.mp h).2.2.symm.trans h1.2) (by decide)
  have hd2 : Disjoint C01 C10 := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    exact absurd ((mem_filter.mp hp1).2.1.symm.trans (mem_filter.mp hp2).2.1) (by decide)
  have hrot1 : C11.card = C10.card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1 + p.2)) ?_ ?_ ?_
    · intro p hp
      obtain ⟨hpO, hq1, hq2⟩ := mem_filter.mp hp
      obtain ⟨hpF, _⟩ := mem_filter.mp hpO
      obtain ⟨h1, h2, h3, hs⟩ := mem_flags.mp hpF
      have hq3 : qform (p.1 + p.2) = 0 := by rw [qform_add, hq1, hq2, hs]; decide
      have hrotF : (p.2, p.1 + p.2) ∈ flags (allPoints N) := by
        rw [mem_flags]
        refine ⟨h2, h3, ?_, ?_⟩
        · have : p.2 + (p.1 + p.2) = p.1 := by rw [add_comm p.1 p.2, ← add_assoc, pt_add_self, zero_add]
          rwa [this]
        · rw [symp_add_right, symp_self, add_zero, symp_comm, hs]
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨hrotF, fun h => absurd (h.1.symm.trans hq2) (by decide)⟩, hq2, hq3⟩
    · intro p _ q _ h
      have h2 : p.2 = q.2 := congrArg Prod.fst h
      have h12 : p.1 + p.2 = q.1 + q.2 := congrArg Prod.snd h
      rw [h2] at h12
      exact Prod.ext (add_right_cancel h12) h2
    · intro r hr
      obtain ⟨hrO, hq1, hq2⟩ := mem_filter.mp hr
      obtain ⟨hrF, _⟩ := mem_filter.mp hrO
      obtain ⟨h1, h2, h3, hs⟩ := mem_flags.mp hrF
      have hq3 : qform (r.1 + r.2) = 1 := by rw [qform_add, hq1, hq2, hs]; decide
      refine ⟨(r.1 + r.2, r.1), ?_, ?_⟩
      · have hpreF : (r.1 + r.2, r.1) ∈ flags (allPoints N) := by
          rw [mem_flags]
          refine ⟨h3, h1, ?_, ?_⟩
          · have : r.1 + r.2 + r.1 = r.2 := by rw [add_comm r.1 r.2, add_assoc, pt_add_self, add_zero]
            rwa [this]
          · rw [symp_comm, symp_add_right, symp_self, zero_add, hs]
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨hpreF, fun h => absurd (h.1.symm.trans hq3) (by decide)⟩, hq3, hq1⟩
      · exact Prod.ext rfl (by rw [add_comm r.1 r.2, add_assoc, pt_add_self, add_zero])
  have hrot2 : C10.card = C01.card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp
      obtain ⟨hpO, hq1, hq2⟩ := mem_filter.mp hp
      obtain ⟨hpF, _⟩ := mem_filter.mp hpO
      obtain ⟨h1, h2, h3, hs⟩ := mem_flags.mp hpF
      have hswF : (p.2, p.1) ∈ flags (allPoints N) :=
        mem_flags.mpr ⟨h2, h1, by rwa [add_comm], by rwa [symp_comm]⟩
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨hswF, fun h => absurd (h.2.symm.trans hq1) (by decide)⟩, hq2, hq1⟩
    · intro p _ q _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    · intro r hr
      obtain ⟨hrO, hq1, hq2⟩ := mem_filter.mp hr
      obtain ⟨hrF, _⟩ := mem_filter.mp hrO
      obtain ⟨h1, h2, h3, hs⟩ := mem_flags.mp hrF
      refine ⟨(r.2, r.1), ?_, rfl⟩
      have hswF : (r.2, r.1) ∈ flags (allPoints N) :=
        mem_flags.mpr ⟨h2, h1, by rwa [add_comm], by rwa [symp_comm]⟩
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨hswF, fun h => absurd (h.1.symm.trans hq2) (by decide)⟩, hq2, hq1⟩
  have hout : outF.card = 3 * (imagFlags N).card := by
    rw [hpart, Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2,
      ← hrot2, ← hrot1, hC11]
    ring
  change (flags (realPoints N)).card + outF.card = (flags (allPoints N)).card at hsplit
  omega

private lemma violated_outside_eq_three_imagFlags (N : ℕ) (f : Pt N → ℝ) :
    3 * (violatedImagFlags N f).card + (violated (realPoints N) f).card =
      (violated (allPoints N) f).card := by
  classical
  set outV := (violated (allPoints N) f).filter fun p => ¬ (qform p.1 = 0 ∧ qform p.2 = 0)
  have hreal_eq : (violated (allPoints N) f).filter (fun p => qform p.1 = 0 ∧ qform p.2 = 0) =
      violated (realPoints N) f := by
    ext p
    simp only [violated, mem_filter, mem_flags, allPoints, realPoints, mem_erase, mem_univ,
      and_true, true_and]
    constructor
    · rintro ⟨⟨⟨h1, h2, h3, hs⟩, hbad⟩, hq1, hq2⟩
      exact ⟨⟨⟨h1, hq1⟩, ⟨h2, hq2⟩, ⟨h3, by rw [qform_add, hq1, hq2, hs]; simp⟩, hs⟩, hbad⟩
    · rintro ⟨⟨⟨h1, hq1⟩, ⟨h2, hq2⟩, ⟨h3, _⟩, hs⟩, hbad⟩
      exact ⟨⟨⟨h1, h2, h3, hs⟩, hbad⟩, hq1, hq2⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := violated (allPoints N) f)
    (fun p => qform p.1 = 0 ∧ qform p.2 = 0)
  rw [hreal_eq] at hsplit
  set C11 := outV.filter fun p => qform p.1 = 1 ∧ qform p.2 = 1
  set C01 := outV.filter fun p => qform p.1 = 0 ∧ qform p.2 = 1
  set C10 := outV.filter fun p => qform p.1 = 1 ∧ qform p.2 = 0
  have hC11 : C11 = violatedImagFlags N f := by
    ext p
    simp only [C11, outV, violatedImagFlags, mem_filter]
    constructor
    · rintro ⟨⟨hp, _⟩, h1, h2⟩; exact ⟨hp, h1, h2⟩
    · rintro ⟨hp, h1, h2⟩
      exact ⟨⟨hp, fun h => absurd (h.1.symm.trans h1) (by decide)⟩, h1, h2⟩
  have hpart : outV = C11 ∪ (C01 ∪ C10) := by
    ext p
    simp only [C11, C01, C10, outV, mem_union, mem_filter]
    constructor
    · intro ⟨hp, hnot⟩
      rcases zmod2_cases (qform p.1) with h1 | h1 <;> rcases zmod2_cases (qform p.2) with h2 | h2
      · exact (hnot ⟨h1, h2⟩).elim
      · exact Or.inr (Or.inl ⟨⟨hp, hnot⟩, h1, h2⟩)
      · exact Or.inr (Or.inr ⟨⟨hp, hnot⟩, h1, h2⟩)
      · exact Or.inl ⟨⟨hp, hnot⟩, h1, h2⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hd1 : Disjoint C11 (C01 ∪ C10) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := (mem_filter.mp hp1).2
    rcases mem_union.mp hp2 with h | h
    · exact absurd ((mem_filter.mp h).2.1.symm.trans h1.1) (by decide)
    · exact absurd ((mem_filter.mp h).2.2.symm.trans h1.2) (by decide)
  have hd2 : Disjoint C01 C10 := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    exact absurd ((mem_filter.mp hp1).2.1.symm.trans (mem_filter.mp hp2).2.1) (by decide)
  have hrot1 : C11.card = C10.card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1 + p.2)) ?_ ?_ ?_
    · intro p hp
      obtain ⟨hpO, hq1, hq2⟩ := mem_filter.mp hp
      obtain ⟨hpV, _⟩ := mem_filter.mp hpO
      have hs := (mem_flags.mp (mem_filter.mp hpV).1).2.2.2
      have hq3 : qform (p.1 + p.2) = 0 := by rw [qform_add, hq1, hq2, hs]; decide
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨violated_rotate hpV,
        fun h => absurd (h.1.symm.trans hq2) (by decide)⟩, hq2, hq3⟩
    · intro p _ q _ h
      have h2 : p.2 = q.2 := congrArg Prod.fst h
      have h12 : p.1 + p.2 = q.1 + q.2 := congrArg Prod.snd h
      rw [h2] at h12
      exact Prod.ext (add_right_cancel h12) h2
    · intro r hr
      obtain ⟨hrO, hq1, hq2⟩ := mem_filter.mp hr
      obtain ⟨hrV, _⟩ := mem_filter.mp hrO
      have hs := (mem_flags.mp (mem_filter.mp hrV).1).2.2.2
      have hq3 : qform (r.1 + r.2) = 1 := by rw [qform_add, hq1, hq2, hs]; decide
      have hr2 := violated_rotate (violated_rotate hrV)
      have hsimp : r.2 + (r.1 + r.2) = r.1 := by rw [add_comm r.1 r.2, ← add_assoc, pt_add_self, zero_add]
      rw [hsimp] at hr2
      refine ⟨(r.1 + r.2, r.1), ?_, ?_⟩
      · exact mem_filter.mpr ⟨mem_filter.mpr ⟨hr2,
          fun h => absurd (h.1.symm.trans hq3) (by decide)⟩, hq3, hq1⟩
      · exact Prod.ext rfl (by rw [add_comm r.1 r.2, add_assoc, pt_add_self, add_zero])
  have hrot2 : C10.card = C01.card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp
      obtain ⟨hpO, hq1, hq2⟩ := mem_filter.mp hp
      obtain ⟨hpV, _⟩ := mem_filter.mp hpO
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨violated_swap hpV,
        fun h => absurd (h.2.symm.trans hq1) (by decide)⟩, hq2, hq1⟩
    · intro p _ q _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    · intro r hr
      obtain ⟨hrO, hq1, hq2⟩ := mem_filter.mp hr
      obtain ⟨hrV, _⟩ := mem_filter.mp hrO
      refine ⟨(r.2, r.1), ?_, rfl⟩
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨violated_swap hrV,
        fun h => absurd (h.1.symm.trans hq2) (by decide)⟩, hq2, hq1⟩
  have hout : outV.card = 3 * (violatedImagFlags N f).card := by
    rw [hpart, Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2,
      ← hrot2, ← hrot1, hC11]
    ring
  change (violated (realPoints N) f).card + outV.card = (violated (allPoints N) f).card at hsplit
  omega

/-- Exact trace expansion connecting `tr(A_real · T_imag²)` to outside violated flags. -/
theorem trace_opA_real_mul_imag_sq (N : ℕ) (f : Pt N → ℝ)
    (hf : ∀ u ∈ allPoints N, f u = 1 ∨ f u = -1) :
    ((opA (realPoints N) f * opA (imagPoints N) f ^ 2).trace).re =
      (2 : ℝ) ^ N * (((imagFlags N).card : ℝ) - 2 * ((violatedImagFlags N f).card : ℝ)) := by
  classical
  set A := opA (realPoints N) f
  set T := opA (imagPoints N) f
  set G : Pt N × Pt N → ℂ := fun p =>
    ((f p.1 : ℝ) : ℂ) * ((f p.2 : ℝ) : ℂ) * ((f (p.1 + p.2) : ℝ) : ℂ) * tau p.1 p.2
  have hstep1 : (A * T ^ 2).trace =
      (2 : ℂ) ^ N * ∑ p ∈ ((imagPoints N) ×ˢ (imagPoints N)).filter (fun p => p.1 + p.2 ∈ realPoints N),
        G p := by
    rw [pow_two, Matrix.trace_mul_comm A (T * T), opA_mul_opA, Finset.sum_mul, Matrix.trace_sum,
      Finset.mul_sum, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul, trace_pauli_mul_opA, smul_eq_mul]
    by_cases hmem : u + v ∈ realPoints N
    · simp only [hmem, ↓reduceIte, G]; ring
    · simp [hmem]
  have hstep2 : ∑ p ∈ (((imagPoints N) ×ˢ (imagPoints N)).filter
      (fun p => p.1 + p.2 ∈ realPoints N)).filter (fun p => ¬ symp p.1 p.2 = 0), G p = 0 := by
    refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p hp
      have hs : symp p.1 p.2 = 1 := (zmod2_cases _).resolve_left (Finset.mem_filter.mp hp).2
      simp only [G]
      rw [tau_swap p.1 p.2, hs, eps_one, add_comm p.2 p.1]; ring
    · intro p hp _ hfix
      have hs := (Finset.mem_filter.mp hp).2
      have h12 : p.2 = p.1 := congrArg Prod.fst hfix
      apply hs; rw [h12]; exact symp_self _
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp1, hs⟩
      rcases Finset.mem_filter.mp hp1 with ⟨hp2, hsum⟩
      rcases Finset.mem_product.mp hp2 with ⟨h1, h2⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h2, h1⟩,
        by simpa [add_comm] using hsum⟩, by simpa [symp_comm] using hs⟩
    · intro p _; rfl
  have hfilt_eq : (((imagPoints N) ×ˢ (imagPoints N)).filter
      (fun p => p.1 + p.2 ∈ realPoints N)).filter (fun p => symp p.1 p.2 = 0) = imagFlags N := by
    ext p
    simp only [imagFlags, mem_filter, mem_product, mem_imagPoints, mem_flags, allPoints,
      realPoints, mem_erase, mem_univ, and_true, true_and]
    constructor
    · rintro ⟨⟨⟨hq1, hq2⟩, hp3, _⟩, hs⟩
      have h1 : p.1 ≠ 0 := fun h => absurd (h ▸ hq1) (by rw [qform_zero]; decide)
      have h2 : p.2 ≠ 0 := fun h => absurd (h ▸ hq2) (by rw [qform_zero]; decide)
      exact ⟨⟨h1, h2, hp3, hs⟩, hq1, hq2⟩
    · rintro ⟨⟨_, _, hp3, hs⟩, hq1, hq2⟩
      exact ⟨⟨⟨hq1, hq2⟩, hp3, by rw [qform_add, hq1, hq2, hs]; decide⟩, hs⟩
  rw [hstep1, ← Finset.sum_filter_add_sum_filter_not _ (fun p : Pt N × Pt N => symp p.1 p.2 = 0),
    hstep2, add_zero, hfilt_eq]
  have hreal_sum : ∑ p ∈ imagFlags N, G p =
      (((((imagFlags N).card : ℝ) - 2 * ((violatedImagFlags N f).card : ℝ)) : ℝ) : ℂ) := by
    have hterm : ∀ p ∈ imagFlags N, G p =
        ((if f p.1 * f p.2 * f (p.1 + p.2) ≠ lineSign p.1 p.2 then (-1 : ℝ) else 1 : ℝ) : ℂ) := by
      intro p hp
      have hpF : p ∈ flags (allPoints N) := (mem_filter.mp hp).1
      have hs : symp p.1 p.2 = 0 := (mem_flags.mp hpF).2.2.2
      simp only [G, tau_eq_lineSign hs]
      have hR := term_eq_ite hf hpF
      exact_mod_cast hR
    rw [Finset.sum_congr rfl hterm, ← Complex.ofReal_sum]
    congr 1
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one]
    have hv : (imagFlags N).filter (fun p => f p.1 * f p.2 * f (p.1 + p.2) ≠ lineSign p.1 p.2) =
        violatedImagFlags N f := by
      ext p
      simp only [imagFlags, violatedImagFlags, violated, mem_filter]
      tauto
    have hsplit := Finset.card_filter_add_card_filter_not (s := imagFlags N)
      (fun p => f p.1 * f p.2 * f (p.1 + p.2) ≠ lineSign p.1 p.2)
    rw [hv] at hsplit ⊢
    have hsplitR : ((violatedImagFlags N f).card : ℝ) +
        (((imagFlags N).filter fun p => ¬ f p.1 * f p.2 * f (p.1 + p.2) ≠ lineSign p.1 p.2).card : ℝ) =
        ((imagFlags N).card : ℝ) := by exact_mod_cast hsplit
    linarith
  rw [hreal_sum]
  have hC : (2 : ℂ) ^ N * (((((imagFlags N).card : ℝ) - 2 * ((violatedImagFlags N f).card : ℝ)) : ℝ) : ℂ) =
      (((2 : ℝ) ^ N * (((imagFlags N).card : ℝ) - 2 * ((violatedImagFlags N f).card : ℝ)) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hC, Complex.ofReal_re]

/-! ### Part 5. Main All-`N` (`N ≥ 4`) No-Go Bound & Corollaries (`N = 4..8`) -/

private lemma muMinus_nonpos {N : ℕ} (hN : 4 ≤ N) : muMinus N ≤ 0 := by
  unfold muMinus
  set D : ℝ := (2 : ℝ) ^ N
  set s : ℝ := Real.sqrt D
  have hD : (16 : ℝ) ≤ D := by
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
  have hs4 : (4 : ℝ) ≤ s := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  have hs2 : s ^ 2 = D := sqrt_two_pow_sq N
  have h1 : 3 * s ≤ s ^ 2 - 4 := by nlinarith
  have h2 : 3 * D ≤ s * (D - 4) := by nlinarith [hs2]
  linarith

/-- **Theorem 24 (All-`N` `PG(N-1,2)` Rigidity & Imaginary-Completion No-Go Bound).**
For every `N ≥ 4` and every `±1` assignment `f` on `W(2N-1,2)` whose restriction to `Q⁺(2N-1,2)`
equals `pgCssSign N`:
`#outsideFlags - 2 · #violatedOutsideFlags ≤ 3 · ((D - 4)(√D + 3) / 4) · |imagPoints N|`. -/
theorem pg_rigidity_lower_bound_all_N {N : ℕ} (hN : 4 ≤ N) (f : Pt N → ℝ)
    (hreal : ∀ u ∈ realPoints N, f u = pgCssSign N u)
    (hf : ∀ u ∈ allPoints N, f u = 1 ∨ f u = -1) :
    (((flags (allPoints N)).card : ℝ) - ((flags (realPoints N)).card : ℝ)) -
      2 * (((violated (allPoints N) f).card : ℝ) - ((violated (realPoints N) f).card : ℝ))
    ≤ 3 * ((((2 : ℝ) ^ N - 4) * (Real.sqrt ((2 : ℝ) ^ N) + 3) / 4) * ((imagPoints N).card : ℝ)) := by
  have hN1 : 1 ≤ N := by omega
  set T := opA (imagPoints N) f
  have hAeq : opA (realPoints N) f = opA (realPoints N) (pgCssSign N) := by
    unfold opA
    exact Finset.sum_congr rfl fun u hu => by rw [hreal u hu]
  have hTh : T.IsHermitian := opA_isHermitian (imagPoints N) f
  have hTskew : Tᵀ = -T := opA_imag_transpose f
  have hPTP : projPlus N * T * projPlus N = 0 := by
    unfold projPlus
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (rankOne (wPlus N)) T (rankOne (wPlus N)),
      rankOne_mul_skew_mul_rankOne (wPlus N) hTskew]
    simp
  have hfrob := two_trace_proj_mul_sq_le_of_skew (projPlus_isHermitian N)
    (projPlus_mul_self hN1) hTh hPTP
  have hpm_nonneg := trace_proj_mul_sq_re_nonneg (projMinus_isHermitian N)
    (projMinus_mul_self hN1) hTh
  have hmu_pos : 0 ≤ muPlus N := by
    unfold muPlus
    have hD : (16 : ℝ) ≤ (2 : ℝ) ^ N := by
      calc (16 : ℝ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
    have hs : 0 ≤ Real.sqrt ((2 : ℝ) ^ N) := Real.sqrt_nonneg _
    nlinarith
  have hmu_neg : muMinus N ≤ 0 := muMinus_nonpos hN
  have htr_T2 : ((T ^ 2).trace).re = (2 : ℝ) ^ N * ((imagPoints N).card : ℝ) := by
    have hfi : ∀ u ∈ imagPoints N, f u = 1 ∨ f u = -1 := fun u hu =>
      hf u (mem_erase.mpr ⟨fun h => zero_not_mem_imagPoints (h ▸ hu), mem_univ _⟩)
    rw [trace_opA_sq (imagPoints N) f hfi, Complex.ofReal_re]
  have htr_AT2 : ((opA (realPoints N) f * T ^ 2).trace).re =
      muPlus N * ((projPlus N * T ^ 2).trace).re +
      muMinus N * ((projMinus N * T ^ 2).trace).re -
      3 * ((T ^ 2).trace).re := by
    rw [hAeq, opA_realPoints_pgCssSign_decomp hN1, sub_mul, add_mul,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul, one_mul,
      Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul]
    simp only [smul_eq_mul, Complex.sub_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, sub_zero]
  have hbound : ((opA (realPoints N) f * T ^ 2).trace).re ≤
      (muPlus N / 2 - 3) * ((T ^ 2).trace).re := by
    have h1 : muPlus N * ((projPlus N * T ^ 2).trace).re ≤
        muPlus N * (((T ^ 2).trace).re / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hmu_pos
    have h2 : muMinus N * ((projMinus N * T ^ 2).trace).re ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hmu_neg hpm_nonneg
    linarith
  have hcoef : muPlus N / 2 - 3 = ((2 : ℝ) ^ N - 4) * (Real.sqrt ((2 : ℝ) ^ N) + 3) / 4 := by
    unfold muPlus; ring
  rw [trace_opA_real_mul_imag_sq N f hf, htr_T2, hcoef] at hbound
  have hDpos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have hcancel : ((imagFlags N).card : ℝ) - 2 * ((violatedImagFlags N f).card : ℝ) ≤
      (((2 : ℝ) ^ N - 4) * (Real.sqrt ((2 : ℝ) ^ N) + 3) / 4) * ((imagPoints N).card : ℝ) := by
    have hmul : (2 : ℝ) ^ N * (((imagFlags N).card : ℝ) - 2 * ((violatedImagFlags N f).card : ℝ)) ≤
        (2 : ℝ) ^ N * ((((2 : ℝ) ^ N - 4) * (Real.sqrt ((2 : ℝ) ^ N) + 3) / 4) *
          ((imagPoints N).card : ℝ)) := by
      linear_combination hbound
    exact le_of_mul_le_mul_left hmul hDpos
  have hF3 : (3 : ℝ) * ((imagFlags N).card : ℝ) =
      ((flags (allPoints N)).card : ℝ) - ((flags (realPoints N)).card : ℝ) := by
    have h := flags_outside_eq_three_imagFlags N
    have hR : (3 : ℝ) * ((imagFlags N).card : ℝ) + ((flags (realPoints N)).card : ℝ) =
        ((flags (allPoints N)).card : ℝ) := by exact_mod_cast h
    linarith
  have hV3 : (3 : ℝ) * ((violatedImagFlags N f).card : ℝ) =
      ((violated (allPoints N) f).card : ℝ) - ((violated (realPoints N) f).card : ℝ) := by
    have h := violated_outside_eq_three_imagFlags N f
    have hR : (3 : ℝ) * ((violatedImagFlags N f).card : ℝ) + ((violated (realPoints N) f).card : ℝ) =
        ((violated (allPoints N) f).card : ℝ) := by exact_mod_cast h
    linarith
  linarith

private lemma violated_realPoints_congr {N : ℕ} {f g : Pt N → ℝ}
    (h : ∀ u ∈ realPoints N, f u = g u) :
    violated (realPoints N) f = violated (realPoints N) g := by
  classical
  ext p
  simp only [violated, mem_filter]
  refine and_congr_right fun hp => ?_
  obtain ⟨h1, h2, h3, _⟩ := mem_flags.mp hp
  rw [h _ h1, h _ h2, h _ h3]

private lemma pg_rigidity_lines_helper {N : ℕ} (hN : 4 ≤ N) (f : Pt N → ℝ)
    (hreal : ∀ u ∈ realPoints N, f u = pgCssSign N u)
    (hf : ∀ u ∈ allPoints N, f u = 1 ∨ f u = -1) :
    ((flags (allPoints N)).card : ℝ) - ((flags (realPoints N)).card : ℝ) -
      3 * ((((2 : ℝ) ^ N - 4) * (Real.sqrt ((2 : ℝ) ^ N) + 3) / 4) * ((imagPoints N).card : ℝ)) +
      12 * ((violatedLines (realPoints N) (pgCssSign N)).card : ℝ)
    ≤ 12 * ((violatedLines (allPoints N) f).card : ℝ) := by
  have hb := pg_rigidity_lower_bound_all_N hN f hreal hf
  have h0all : (0 : Pt N) ∉ allPoints N := by simp [allPoints]
  have h0real : (0 : Pt N) ∉ realPoints N := by simp [realPoints]
  have h6all : ((violated (allPoints N) f).card : ℝ) =
      6 * ((violatedLines (allPoints N) f).card : ℝ) := by
    exact_mod_cast card_violated_eq_six (allPoints N) h0all f
  have h6real : ((violated (realPoints N) f).card : ℝ) =
      6 * ((violatedLines (realPoints N) (pgCssSign N)).card : ℝ) := by
    rw [violated_realPoints_congr hreal]
    exact_mod_cast card_violated_eq_six (realPoints N) h0real (pgCssSign N)
  linarith

/-! ### Part 6. Concrete Corollaries (`N = 4, 5, 6, 7, 8`) -/

/-- **`N = 4` (`W(7,2)`):** Every `PG(3,2)`-centered extension violates at least `1,575` contexts. -/
theorem pg_rigidity_n4 (f : Pt 4 → ℝ)
    (hreal : ∀ u ∈ realPoints 4, f u = pgCssSign 4 u)
    (hf : ∀ u ∈ allPoints 4, f u = 1 ∨ f u = -1) :
    1575 ≤ (violatedLines (allPoints 4) f).card := by
  set V := (violatedLines (allPoints 4) f).card
  have h := pg_rigidity_lines_helper (N := 4) (by norm_num) f hreal hf
  have hFall : (flags (allPoints 4)).card = 32130 := by
    have := card_flags_all (N := 4); norm_num at this; omega
  have hSreal : (realPoints 4).card = 135 := by
    have := card_realPoints (N := 4); norm_num at this; omega
  have hFreal : (flags (realPoints 4)).card = 9450 := by
    have := card_flags_real (N := 4); rw [hSreal] at this; norm_num at this; omega
  have hI : (imagPoints 4).card = 120 := by
    have := card_imagPoints 4; norm_num at this; omega
  have hVQ : ((violatedLines (realPoints 4) (pgCssSign 4)).card : ℝ) = 315 := by
    have hv := pgCssSign_violatedLines_real (N := 4) (by norm_num)
    rw [show (2 : ℝ) ^ 4 = 16 by norm_num] at hv; linarith
  have hs : Real.sqrt ((2 : ℝ) ^ 4) = 4 := by
    rw [show ((2 : ℝ) ^ 4) = 4 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  rw [hFall, hFreal, hI, hVQ, hs] at h
  have h24 : (2 : ℝ) ^ 4 = 16 := by norm_num
  rw [h24] at h
  push_cast at h
  have hnat : (1575 : ℝ) ≤ (V : ℝ) := by linarith
  exact_mod_cast hnat

/-- **`N = 5` (`W(9,2)`):** Every `PG(4,2)`-centered extension violates at least `31,081` contexts. -/
theorem pg_rigidity_n5 (f : Pt 5 → ℝ)
    (hreal : ∀ u ∈ realPoints 5, f u = pgCssSign 5 u)
    (hf : ∀ u ∈ allPoints 5, f u = 1 ∨ f u = -1) :
    31081 ≤ (violatedLines (allPoints 5) f).card := by
  set V := (violatedLines (allPoints 5) f).card
  have h := pg_rigidity_lines_helper (N := 5) (by norm_num) f hreal hf
  have hFall : (flags (allPoints 5)).card = 521730 := by
    have := card_flags_all (N := 5); norm_num at this; omega
  have hSreal : (realPoints 5).card = 527 := by
    have := card_realPoints (N := 5); norm_num at this; omega
  have hFreal : (flags (realPoints 5)).card = 142290 := by
    have := card_flags_real (N := 5); rw [hSreal] at this; norm_num at this; omega
  have hI : (imagPoints 5).card = 496 := by
    have := card_imagPoints 5; norm_num at this; omega
  have hVQ : ((violatedLines (realPoints 5) (pgCssSign 5)).card : ℝ) = 6975 := by
    have hv := pgCssSign_violatedLines_real (N := 5) (by norm_num)
    rw [show (2 : ℝ) ^ 5 = 32 by norm_num] at hv; linarith
  have hs : Real.sqrt ((2 : ℝ) ^ 5) < 5.6569 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  rw [hFall, hFreal, hI, hVQ] at h
  have h25 : (2 : ℝ) ^ 5 = 32 := by norm_num
  rw [h25] at h hs
  push_cast at h
  by_contra hlt
  have hle : (V : ℝ) ≤ 31080 := by
    have : V ≤ 31080 := by omega
    exact_mod_cast this
  linarith

/-- **`N = 6` (`W(11,2)`):** Every `PG(5,2)`-centered extension violates at least `571,095` contexts. -/
theorem pg_rigidity_n6 (f : Pt 6 → ℝ)
    (hreal : ∀ u ∈ realPoints 6, f u = pgCssSign 6 u)
    (hf : ∀ u ∈ allPoints 6, f u = 1 ∨ f u = -1) :
    571095 ≤ (violatedLines (allPoints 6) f).card := by
  set V := (violatedLines (allPoints 6) f).card
  have h := pg_rigidity_lines_helper (N := 6) (by norm_num) f hreal hf
  have hFall : (flags (allPoints 6)).card = 8378370 := by
    have := card_flags_all (N := 6); norm_num at this; omega
  have hSreal : (realPoints 6).card = 2079 := by
    have := card_realPoints (N := 6); norm_num at this; omega
  have hFreal : (flags (realPoints 6)).card = 2191266 := by
    have := card_flags_real (N := 6); rw [hSreal] at this; norm_num at this; omega
  have hI : (imagPoints 6).card = 2016 := by
    have := card_imagPoints 6; norm_num at this; omega
  have hVQ : ((violatedLines (realPoints 6) (pgCssSign 6)).card : ℝ) = 138663 := by
    have hv := pgCssSign_violatedLines_real (N := 6) (by norm_num)
    rw [show (2 : ℝ) ^ 6 = 64 by norm_num] at hv; linarith
  have hs : Real.sqrt ((2 : ℝ) ^ 6) = 8 := by
    rw [show ((2 : ℝ) ^ 6) = 8 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  rw [hFall, hFreal, hI, hVQ, hs] at h
  have h26 : (2 : ℝ) ^ 6 = 64 := by norm_num
  rw [h26] at h
  push_cast at h
  have hnat : (571095 : ℝ) ≤ (V : ℝ) := by linarith
  exact_mod_cast hnat

/-- **`N = 7` (`W(13,2)`):** Every `PG(6,2)`-centered extension violates at least `9,907,702` contexts. -/
theorem pg_rigidity_n7 (f : Pt 7 → ℝ)
    (hreal : ∀ u ∈ realPoints 7, f u = pgCssSign 7 u)
    (hf : ∀ u ∈ allPoints 7, f u = 1 ∨ f u = -1) :
    9907702 ≤ (violatedLines (allPoints 7) f).card := by
  set V := (violatedLines (allPoints 7) f).card
  have h := pg_rigidity_lines_helper (N := 7) (by norm_num) f hreal hf
  have hFall : (flags (allPoints 7)).card = 134176770 := by
    have := card_flags_all (N := 7); norm_num at this; omega
  have hSreal : (realPoints 7).card = 8255 := by
    have := card_realPoints (N := 7); norm_num at this; omega
  have hFreal : (flags (realPoints 7)).card = 34324290 := by
    have := card_flags_real (N := 7); rw [hSreal] at this; norm_num at this; omega
  have hI : (imagPoints 7).card = 8128 := by
    have := card_imagPoints 7; norm_num at this; omega
  have hVQ : ((violatedLines (realPoints 7) (pgCssSign 7)).card : ℝ) = 2488311 := by
    have hv := pgCssSign_violatedLines_real (N := 7) (by norm_num)
    rw [show (2 : ℝ) ^ 7 = 128 by norm_num] at hv; linarith
  have hs : Real.sqrt ((2 : ℝ) ^ 7) < 11.31371 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  rw [hFall, hFreal, hI, hVQ] at h
  have h27 : (2 : ℝ) ^ 7 = 128 := by norm_num
  rw [h27] at h hs
  push_cast at h
  by_contra hlt
  have hle : (V : ℝ) ≤ 9907701 := by
    have : V ≤ 9907701 := by omega
    exact_mod_cast this
  linarith

/-- **`N = 8` (`W(15,2)` — Saniga's Question 2):**
Every `PG(7,2)`-centered extension to `W(15,2)` violates at least `166,115,415` contexts,
strictly above our verified `W(15,2)` witness `161,360,335` by `4,755,080` contexts! -/
theorem pg_rigidity_n8 (f : Pt 8 → ℝ)
    (hreal : ∀ u ∈ realPoints 8, f u = pgCssSign 8 u)
    (hf : ∀ u ∈ allPoints 8, f u = 1 ∨ f u = -1) :
    166115415 ≤ (violatedLines (allPoints 8) f).card := by
  set V := (violatedLines (allPoints 8) f).card
  have h := pg_rigidity_lines_helper (N := 8) (by norm_num) f hreal hf
  have hFall : (flags (allPoints 8)).card = 2147319810 := by
    have := card_flags_all (N := 8); norm_num at this; omega
  have hSreal : (realPoints 8).card = 32895 := by
    have := card_realPoints (N := 8); norm_num at this; omega
  have hFreal : (flags (realPoints 8)).card = 543096450 := by
    have := card_flags_real (N := 8); rw [hSreal] at this; norm_num at this; omega
  have hI : (imagPoints 8).card = 32640 := by
    have := card_imagPoints 8; norm_num at this; omega
  have hVQ : ((violatedLines (realPoints 8) (pgCssSign 8)).card : ℝ) = 42197655 := by
    have hv := pgCssSign_violatedLines_real (N := 8) (by norm_num)
    rw [show (2 : ℝ) ^ 8 = 256 by norm_num] at hv; linarith
  have hs : Real.sqrt ((2 : ℝ) ^ 8) = 16 := by
    rw [show ((2 : ℝ) ^ 8) = 16 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  rw [hFall, hFreal, hI, hVQ, hs] at h
  have h28 : (2 : ℝ) ^ 8 = 256 := by norm_num
  rw [h28] at h
  push_cast at h
  have hnat : (166115415 : ℝ) ≤ (V : ℝ) := by linarith
  exact_mod_cast hnat

end HoggarBound.PGRigidity
