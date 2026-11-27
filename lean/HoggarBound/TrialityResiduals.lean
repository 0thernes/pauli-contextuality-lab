/-
Hoggar Bound Lab — Theorem 23 (Four-Way `Q⁺(7,2)` Triality Residuals: `0`, `210`, `252`, `252`).

Answers Metod Saniga's 26 Nov 2026 triality questions on the four-qubit hyperbolic quadric
`Q⁺(7,2)` (`135` observables, `1,575` contexts), proving exact contextuality degrees for all four
`315`-line deletions (`1,260` residual contexts each):

1. **Case (0) — `DW(5,2)` deleted:** exact degree **`0`** (`dw52_residual_exact_zero`).
2. **Case (a) — Any 9-solid spread `S` deleted (Question 1a):**
   * `mermin_peres_4tuple_violated` : All-`N` pure Pauli-algebra Mermin–Peres contradiction.
   * `spread_residual_ge_210`       : **Universal** lower bound `210 ≤ d(Q⁺(7,2) \ S)` proved for
     *every* spread `S : SolidSpread` of 9 solids of `Q⁺(7,2)` (zero bitmasks, zero `decide`,
     pure `𝔽₂` linear algebra + exact inclusion-exclusion `16 - 7 - 7 = 2 ⇒ deg(u, v) = 48`).
   * `m1_spread_residual_exact_210` : Exact degree **`210`** on the canonical `M1` spread `m1Spread`,
     attained by `m1OptNeg` (`315 - 105 = 210`).
3. **Case (b) — Any `Q(6,2) = Q⁺(7,2) ∩ w⊥` (`qform w = 1`) deleted (Question 1b):**
   * `q62_residual_ge_252`          : **Universal** lower bound `252 ≤ d(Q⁺(7,2) \ Q(6,2))` proved
     for *every* off-quadric pole `w` (`qform w = 1`, all 120 copies simultaneously) via
     `kramers_even_mult` + Cauchy–Schwarz (`λ_max(A_σ) ≤ 21`) + PSD trace bound.
   * `q62_residual_exact_252`       : Exact degree **`252`** at `w = Y0 4`, attained by `ovoidOptNeg`
     (`315 - 63 = 252`).
4. **Case (a*) — Triality-dual 9-point ovoid `O` deleted (`126` observables, `1,260` contexts):**
   * `aniso_plane_q5minus_ge_9`     : Multiplicity-4 Kramers proof that every anisotropic 2-plane
     section `Q⁺(7,2) ∩ u⊥ ∩ v⊥ ≅ Q⁻(5,2)` (`27` pts, `45` lines) has `≥ 9` violated contexts.
   * `ovoid_residual_exact_252`     : Exact degree **`252`** on `Q⁺(7,2) \ O`, beating the
     Theorem 1 spectral floor `204` by `+48`, via 10-uniform double-counting over all `280`
     intact `Q⁻(5,2)` sections and exact attainment by `ovoidOptNeg`.

Zero `sorry`, zero `admit`, zero `native_decide`, strictly `[propext, Classical.choice, Quot.sound]`.
-/
import HoggarBound.Kramers
import HoggarBound.MaskRows
import HoggarBound.ExactDegreesN4N5

open Finset Matrix HoggarBound
open scoped InnerProductSpace

namespace HoggarBound.TrialityResiduals

/-! ### Part 1. All-`N` Pure Pauli-Algebra Mermin–Peres 4-Tuple Contradiction -/

/-- Exact Pauli sign product `-1` on any Mermin–Peres 4-tuple `(u, v, x, y)` for arbitrary `N`. -/
theorem mermin_peres_tau_prod {N : ℕ} {u v x y : Pt N}
    (huv : symp u v = 0) (hxy : symp x y = 0)
    (hux : symp u x = 0) (hvy : symp v y = 0)
    (huy : symp u y = 1) (hvx : symp v x = 1) :
    tau u v * tau x y * tau (u + x) (v + y) * tau u x * tau v y * tau (u + v) (x + y) = -1 := by
  have hrow2 : symp (u + x) (v + y) = 0 := by
    rw [symp_add_right, ExactDegreesN4N5.symp_add_left, ExactDegreesN4N5.symp_add_left,
      huv, symp_comm x v, hvx, huy, hxy]; decide
  have hcol2 : symp (u + v) (x + y) = 0 := by
    rw [symp_add_right, ExactDegreesN4N5.symp_add_left, ExactDegreesN4N5.symp_add_left,
      hux, huy, hvx, hvy]; decide
  -- Compute `(P_u P_v)(P_x P_y)` two ways.
  have hway1 : (pauli u * pauli v) * (pauli x * pauli y) =
      (tau u v * tau x y * tau (u + v) (x + y)) • pauli ((u + v) + (x + y)) := by
    rw [pauli_mul u v, pauli_mul x y, Matrix.smul_mul, Matrix.mul_smul, pauli_mul,
      smul_smul, smul_smul]
  have hanti : pauli v * pauli x = -(pauli x * pauli v) := by
    rw [pauli_comm x v, symp_comm x v, hvx, eps_one, neg_one_smul]
  have hway2 : (pauli u * pauli v) * (pauli x * pauli y) =
      (-(tau u x * tau v y * tau (u + x) (v + y))) • pauli ((u + x) + (v + y)) := by
    calc (pauli u * pauli v) * (pauli x * pauli y)
        = pauli u * (pauli v * pauli x) * pauli y := by simp only [Matrix.mul_assoc]
      _ = pauli u * (-(pauli x * pauli v)) * pauli y := by rw [hanti]
      _ = -((pauli u * pauli x) * (pauli v * pauli y)) := by
            simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = -((tau u x • pauli (u + x)) * (tau v y • pauli (v + y))) := by
            rw [pauli_mul u x, pauli_mul v y]
      _ = (-(tau u x * tau v y * tau (u + x) (v + y))) • pauli ((u + x) + (v + y)) := by
            rw [Matrix.smul_mul, Matrix.mul_smul, pauli_mul, smul_smul, smul_smul, ← neg_smul]
  have hsum : (u + v) + (x + y) = (u + x) + (v + y) := by abel
  rw [← hsum] at hway2
  have heqM := hway1.symm.trans hway2
  have htr := congrArg (fun M => (M * pauli ((u + v) + (x + y))).trace) heqM
  simp only [Matrix.smul_mul, Matrix.trace_smul, trace_pauli_mul, ↓reduceIte, smul_eq_mul] at htr
  have h2N : (2 : ℂ) ^ N ≠ 0 := pow_ne_zero N (by norm_num)
  have hsc : tau u v * tau x y * tau (u + v) (x + y) = -(tau u x * tau v y * tau (u + x) (v + y)) :=
    mul_right_cancel₀ h2N htr
  have hsq : ∀ {a b : Pt N}, symp a b = 0 → tau a b * tau a b = 1 := fun {a b} hab => by
    rw [← sq, tau_sq, hab, eps_zero]
  calc tau u v * tau x y * tau (u + x) (v + y) * tau u x * tau v y * tau (u + v) (x + y)
      = (tau u v * tau x y * tau (u + v) (x + y)) * (tau u x * tau v y * tau (u + x) (v + y)) := by ring
    _ = -((tau u x * tau u x) * (tau v y * tau v y) * (tau (u + x) (v + y) * tau (u + x) (v + y))) := by
          rw [hsc]; ring
    _ = -1 := by rw [hsq hux, hsq hvy, hsq hrow2]; ring

/-- **All-`N` Mermin–Peres 4-tuple contradiction:** for any `±1` assignment `f`, at least one of the
six commuting lines of `(u, v, x, y)` is violated. -/
theorem mermin_peres_4tuple_violated {N : ℕ} {u v x y : Pt N}
    (huv : symp u v = 0) (hxy : symp x y = 0)
    (hux : symp u x = 0) (hvy : symp v y = 0)
    (huy : symp u y = 1) (hvx : symp v x = 1)
    (f : Pt N → ℝ)
    (hf1 : f u = 1 ∨ f u = -1) (hf2 : f v = 1 ∨ f v = -1) (hf3 : f (u + v) = 1 ∨ f (u + v) = -1)
    (hf4 : f x = 1 ∨ f x = -1) (hf5 : f y = 1 ∨ f y = -1) (hf6 : f (x + y) = 1 ∨ f (x + y) = -1)
    (hf7 : f (u + x) = 1 ∨ f (u + x) = -1) (hf8 : f (v + y) = 1 ∨ f (v + y) = -1)
    (hf9 : f (u + v + (x + y)) = 1 ∨ f (u + v + (x + y)) = -1) :
    f u * f v * f (u + v) ≠ lineSign u v ∨
    f x * f y * f (x + y) ≠ lineSign x y ∨
    f (u + x) * f (v + y) * f ((u + x) + (v + y)) ≠ lineSign (u + x) (v + y) ∨
    f u * f x * f (u + x) ≠ lineSign u x ∨
    f v * f y * f (v + y) ≠ lineSign v y ∨
    f (u + v) * f (x + y) * f ((u + v) + (x + y)) ≠ lineSign (u + v) (x + y) := by
  by_contra hall
  push Not at hall
  rcases hall with ⟨h1, h2, h3, h4, h5, h6⟩
  have hrow2 : symp (u + x) (v + y) = 0 := by
    rw [symp_add_right, ExactDegreesN4N5.symp_add_left, ExactDegreesN4N5.symp_add_left,
      huv, symp_comm x v, hvx, huy, hxy]; decide
  have hcol2 : symp (u + v) (x + y) = 0 := by
    rw [symp_add_right, ExactDegreesN4N5.symp_add_left, ExactDegreesN4N5.symp_add_left,
      hux, huy, hvx, hvy]; decide
  have hlsProd : lineSign u v * lineSign x y * lineSign (u + x) (v + y) *
      lineSign u x * lineSign v y * lineSign (u + v) (x + y) = -1 := by
    have hC := mermin_peres_tau_prod huv hxy hux hvy huy hvx
    rw [tau_eq_lineSign huv, tau_eq_lineSign hxy, tau_eq_lineSign hrow2,
      tau_eq_lineSign hux, tau_eq_lineSign hvy, tau_eq_lineSign hcol2] at hC
    exact_mod_cast hC
  have hsum : (u + x) + (v + y) = (u + v) + (x + y) := by abel
  rw [hsum] at h3
  have hsq : ∀ {r : ℝ}, (r = 1 ∨ r = -1) → r * r = 1 := fun hr => by
    rcases hr with rfl | rfl <;> norm_num
  have h1eq : (f u * f v * f (u + v)) * (f x * f y * f (x + y)) *
      (f (u + x) * f (v + y) * f (u + v + (x + y))) *
      (f u * f x * f (u + x)) * (f v * f y * f (v + y)) *
      (f (u + v) * f (x + y) * f (u + v + (x + y))) = 1 := by
    calc _ = (f u * f u) * (f v * f v) * (f (u + v) * f (u + v)) *
             (f x * f x) * (f y * f y) * (f (x + y) * f (x + y)) *
             (f (u + x) * f (u + x)) * (f (v + y) * f (v + y)) *
             (f (u + v + (x + y)) * f (u + v + (x + y))) := by ring
      _ = 1 := by
          rw [hsq hf1, hsq hf2, hsq hf3, hsq hf4, hsq hf5, hsq hf6, hsq hf7, hsq hf8, hsq hf9]
          norm_num
  rw [h1, h2, h3, h4, h5, h6] at h1eq
  linarith

/-! ### Part 2. Universal `d(Q⁺(7,2) \ Spread) ≥ 210` for EVERY 9-Solid Spread -/

/-- Fast membership lemma for `realPoints 4` avoiding `Finset.filter` `DecidablePred` reduction under `classical`. -/
private lemma mem_real4 {u : Pt 4} : u ∈ realPoints 4 ↔ u ≠ 0 ∧ qform u = 0 := by
  simp [realPoints]

/-- Irreducible alias for `realPoints 4` preventing elaborator WHNF unfolding of `Fintype.piFinset` on `N = 4`. -/
irreducible_def q7pPts : Finset (Pt 4) := realPoints 4

lemma mem_q7pPts {u : Pt 4} : u ∈ q7pPts ↔ u ∈ realPoints 4 := by
  rw [q7pPts_def]

/-- Irreducible alias for `flags (realPoints 4)` preventing elaborator WHNF reduction on concrete `N = 4`. -/
irreducible_def q7pFlags : Finset (Pt 4 × Pt 4) := flags (realPoints 4)

lemma mem_q7pFlags {p : Pt 4 × Pt 4} :
    p ∈ q7pFlags ↔ p.1 ∈ realPoints 4 ∧ p.2 ∈ realPoints 4 ∧
      p.1 + p.2 ∈ realPoints 4 ∧ symp p.1 p.2 = 0 := by
  rw [q7pFlags_def, mem_flags]

lemma card_q7pFlags : q7pFlags.card = 9450 := by
  rw [q7pFlags_def]
  have hS : (realPoints 4).card = 135 := by have := card_realPoints (N := 4); norm_num at this; omega
  have hF := card_flags_real (N := 4); rw [hS] at hF; norm_num at hF; omega

/-- A spread of 9 pairwise-disjoint totally isotropic solids (`PG(3,2)`) partitioning `Q⁺(7,2)`. -/
structure SolidSpread where
  /-- The `i`-th solid (`15` observables forming a totally isotropic `PG(3,2)`) in the spread. -/
  solid : Fin 9 → Finset (Pt 4)
  sub_real : ∀ i, solid i ⊆ realPoints 4
  card_eq : ∀ i, (solid i).card = 15
  closed : ∀ i, ∀ u ∈ solid i, ∀ v ∈ solid i, u ≠ v → u + v ∈ solid i
  comm : ∀ i, ∀ u ∈ solid i, ∀ v ∈ solid i, symp u v = 0
  disj : ∀ i j, i ≠ j → Disjoint (solid i) (solid j)

namespace SolidSpread

open Classical in
/-- Residual flags of `Q⁺(7,2) \ Spread`: flags whose two points lie in distinct solids. -/
noncomputable def resFlags (S : SolidSpread) : Finset (Pt 4 × Pt 4) :=
  q7pFlags.filter fun p => ∀ i : Fin 9, ¬ (p.1 ∈ S.solid i ∧ p.2 ∈ S.solid i)

open Classical in
/-- Residual violated flags of `Q⁺(7,2) \ Spread`. -/
noncomputable def resViolated (S : SolidSpread) (f : Pt 4 → ℝ) : Finset (Pt 4 × Pt 4) :=
  (S.resFlags).filter fun p => f p.1 * f p.2 * f (p.1 + p.2) ≠ lineSign p.1 p.2

open Classical in
/-- Residual violated contexts of `Q⁺(7,2) \ Spread`. -/
noncomputable def resViolatedLines (S : SolidSpread) (f : Pt 4 → ℝ) : Finset (Finset (Pt 4)) :=
  (S.resViolated f).image lineOf

open Classical in
lemma mem_resFlags {S : SolidSpread} {p : Pt 4 × Pt 4} :
    p ∈ S.resFlags ↔ p ∈ q7pFlags ∧ ∀ i : Fin 9, ¬ (p.1 ∈ S.solid i ∧ p.2 ∈ S.solid i) :=
  by simp only [resFlags, mem_filter]

open Classical in
lemma mem_resViolated {S : SolidSpread} {f : Pt 4 → ℝ} {p : Pt 4 × Pt 4} :
    p ∈ S.resViolated f ↔ p ∈ S.resFlags ∧ f p.1 * f p.2 * f (p.1 + p.2) ≠ lineSign p.1 p.2 :=
  by simp only [resViolated, mem_filter]

/-- The 4-dimensional totally isotropic subspace `V_i = S_i ∪ {0}` (`16` vectors). -/
def subSpace (S : SolidSpread) (i : Fin 9) : Finset (Pt 4) := insert 0 (S.solid i)

lemma zero_not_mem_solid (S : SolidSpread) (i : Fin 9) : (0 : Pt 4) ∉ S.solid i := by
  intro h
  have := S.sub_real i h
  simp [realPoints] at this

lemma card_subSpace (S : SolidSpread) (i : Fin 9) : (S.subSpace i).card = 16 := by
  rw [subSpace, Finset.card_insert_of_notMem (S.zero_not_mem_solid i), S.card_eq i]

lemma subSpace_add (S : SolidSpread) (i : Fin 9) {a b : Pt 4}
    (ha : a ∈ S.subSpace i) (hb : b ∈ S.subSpace i) : a + b ∈ S.subSpace i := by
  simp only [subSpace, mem_insert] at ha hb ⊢
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · left; simp
  · right; simpa using hb
  · right; simpa using ha
  · by_cases hab : a = b
    · left; rw [hab, pt_add_self]
    · right; exact S.closed i a ha b hb hab

lemma subSpace_comm (S : SolidSpread) (i : Fin 9) {a b : Pt 4}
    (ha : a ∈ S.subSpace i) (hb : b ∈ S.subSpace i) : symp a b = 0 := by
  simp only [subSpace, mem_insert] at ha hb
  rcases ha with rfl | ha
  · rw [symp_comm, symp_zero_right]
  · rcases hb with rfl | hb
    · exact symp_zero_right _
    · exact S.comm i a ha b hb

lemma biUnion_eq_realPoints (S : SolidSpread) :
    (univ : Finset (Fin 9)).biUnion S.solid = realPoints 4 := by
  have hsub : (univ : Finset (Fin 9)).biUnion S.solid ⊆ realPoints 4 := by
    intro p hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    exact S.sub_real i hi
  have hcard : ((univ : Finset (Fin 9)).biUnion S.solid).card = 135 := by
    rw [Finset.card_biUnion (fun i _ j _ hij => S.disj i j hij)]
    simp [S.card_eq]
  have hcardR : (realPoints 4).card = 135 := by
    have := card_realPoints (N := 4); norm_num at this; omega
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hcardR])

lemma exists_unique_solid (S : SolidSpread) {p : Pt 4} (hp : p ∈ realPoints 4) :
    ∃! i : Fin 9, p ∈ S.solid i := by
  rw [← S.biUnion_eq_realPoints] at hp
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
  refine ⟨i, hi, fun j hj => ?_⟩
  by_contra hne
  exact Finset.disjoint_left.mp (S.disj j i hne) hj hi

/-- Parseval bound: any pairwise-commuting subset of `Pt N` has cardinality at most `2^N`. -/
private lemma card_commuting_set_le {N : ℕ} (W : Finset (Pt N))
    (hcomm : ∀ a ∈ W, ∀ b ∈ W, symp a b = 0) : W.card ≤ 2 ^ N := by
  let eR : ZMod 2 → ℝ := fun t => if t = 0 then 1 else -1
  have heR_add : ∀ s t : ZMod 2, eR (s + t) = eR s * eR t := by
    intro s t
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    rcases zmod2_cases s with rfl | rfl <;> rcases zmod2_cases t with rfl | rfl <;>
      simp [eR, h11]
  have heR_sum : ∀ u : Pt N, u ≠ 0 → ∑ v : Pt N, eR (symp u v) = 0 := by
    intro u hu
    have hC := sum_eps_symp hu
    have hre : (∑ v : Pt N, eps (symp u v)).re = ∑ v : Pt N, eR (symp u v) := by
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rcases zmod2_cases (symp u v) with h | h <;> simp [eps, eR, h]
    rw [← hre, hC, Complex.zero_re]
  have hexpand : ∑ v : Pt N, (∑ a ∈ W, eR (symp a v)) ^ 2 = (W.card : ℝ) * (4 : ℝ) ^ N := by
    have hsq : ∀ v : Pt N, (∑ a ∈ W, eR (symp a v)) ^ 2 =
        ∑ a ∈ W, ∑ b ∈ W, eR (symp (a + b) v) := by
      intro v
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [ExactDegreesN4N5.symp_add_left, heR_add]
    simp_rw [hsq]
    rw [Finset.sum_comm]
    have houter : ∀ a ∈ W, ∑ v : Pt N, ∑ b ∈ W, eR (symp (a + b) v) = (4 : ℝ) ^ N := by
      intro a ha
      rw [Finset.sum_comm]
      rw [Finset.sum_eq_single a]
      · simp only [pt_add_self, symp_comm, symp_zero_right, eR, ↓reduceIte, Finset.sum_const,
          Finset.card_univ, card_pt, nsmul_eq_mul, mul_one]
        push_cast; rfl
      · intro b _ hba
        have hab : a + b ≠ 0 := fun h => hba (pt_eq_of_add_eq_zero h).symm
        exact heR_sum (a + b) hab
      · intro h; exact absurd ha h
    rw [Finset.sum_congr rfl houter, Finset.sum_const, nsmul_eq_mul]
  have hlow : (W.card : ℝ) * (W.card : ℝ) ^ 2 ≤ ∑ v : Pt N, (∑ a ∈ W, eR (symp a v)) ^ 2 := by
    have hsub : ∑ v ∈ W, (∑ a ∈ W, eR (symp a v)) ^ 2 ≤ ∑ v : Pt N, (∑ a ∈ W, eR (symp a v)) ^ 2 :=
      Finset.sum_le_univ_sum_of_nonneg fun v => sq_nonneg _
    have hconst : ∑ v ∈ W, (∑ a ∈ W, eR (symp a v)) ^ 2 = (W.card : ℝ) * (W.card : ℝ) ^ 2 := by
      have hterm : ∀ v ∈ W, (∑ a ∈ W, eR (symp a v)) ^ 2 = (W.card : ℝ) ^ 2 := by
        intro v hv
        have : ∀ a ∈ W, eR (symp a v) = 1 := fun a ha => by rw [hcomm a ha v hv]; simp [eR]
        rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    linarith
  rw [hexpand] at hlow
  by_cases h0 : W.card = 0
  · rw [h0]; exact Nat.zero_le _
  · have hpos : (0 : ℝ) < (W.card : ℝ) := by positivity
    have hsqle : (W.card : ℝ) ^ 2 ≤ ((2 : ℝ) ^ N) ^ 2 := by
      have h4 : (4 : ℝ) ^ N = ((2 : ℝ) ^ N) ^ 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm 2 N, pow_mul]
      rw [h4] at hlow
      exact le_of_mul_le_mul_left hlow hpos
    have hleR : (W.card : ℝ) ≤ (2 : ℝ) ^ N := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) N]
    exact_mod_cast hleR

/-- Maximal isotropy of each solid: any `p ∉ S.subSpace i` anticommutes with some point of `S.solid i`. -/
lemma exists_anticomm_in_solid (S : SolidSpread) (i : Fin 9) {p : Pt 4}
    (hp : p ∉ S.subSpace i) : ∃ q ∈ S.solid i, symp p q = 1 := by
  by_contra hall
  push Not at hall
  have hcomm_p : ∀ q ∈ S.subSpace i, symp p q = 0 := by
    intro q hq
    simp only [subSpace, mem_insert] at hq
    rcases hq with rfl | hq
    · exact symp_zero_right _
    · exact (zmod2_cases _).resolve_right (hall q hq)
  set V := S.subSpace i
  set W := V ∪ V.image (fun z => z + p)
  have hdisj : Disjoint V (V.image (fun z => z + p)) := by
    rw [Finset.disjoint_left]
    intro x hxV hxI
    obtain ⟨z, hzV, rfl⟩ := mem_image.mp hxI
    apply hp
    have : p = z + (z + p) := by rw [← add_assoc, pt_add_self, zero_add]
    rw [this]
    exact S.subSpace_add i hzV hxV
  have hcardW : W.card = 32 := by
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (fun a b h => add_right_cancel h), S.card_subSpace i]
  have hcommW : ∀ a ∈ W, ∀ b ∈ W, symp a b = 0 := by
    intro a ha b hb
    rcases mem_union.mp ha with haV | haI <;> rcases mem_union.mp hb with hbV | hbI
    · exact S.subSpace_comm i haV hbV
    · obtain ⟨z, hzV, rfl⟩ := mem_image.mp hbI
      rw [symp_add_right, S.subSpace_comm i haV hzV, symp_comm a p, hcomm_p a haV, add_zero]
    · obtain ⟨z, hzV, rfl⟩ := mem_image.mp haI
      rw [ExactDegreesN4N5.symp_add_left, S.subSpace_comm i hzV hbV, hcomm_p b hbV, add_zero]
    · obtain ⟨z1, hz1, rfl⟩ := mem_image.mp haI
      obtain ⟨z2, hz2, rfl⟩ := mem_image.mp hbI
      rw [symp_add_right, ExactDegreesN4N5.symp_add_left, ExactDegreesN4N5.symp_add_left,
        S.subSpace_comm i hz1 hz2, symp_comm z1 p, hcomm_p z1 hz1, hcomm_p z2 hz2, symp_self]
      simp
  have hle := card_commuting_set_le W hcommW
  rw [hcardW] at hle
  norm_num at hle

/-- Every pair `(p, q)` with `p, q, p+q ∉ V_i` cuts `V_i` into four exact fibers of size `4`. -/
lemma card_subSpace_pair_filter (S : SolidSpread) (i : Fin 9) {p q : Pt 4}
    (hp : p ∉ S.subSpace i) (hq : q ∉ S.subSpace i) (hpq : p + q ∉ S.subSpace i)
    (b1 b2 : ZMod 2) :
    ((S.subSpace i).filter fun z => symp p z = b1 ∧ symp q z = b2).card = 4 := by
  obtain ⟨ep, hep, hpep⟩ := S.exists_anticomm_in_solid i hp
  obtain ⟨eq_, heq_, hqeq⟩ := S.exists_anticomm_in_solid i hq
  obtain ⟨epq, hepq, hpq_e⟩ := S.exists_anticomm_in_solid i hpq
  have hepV : ep ∈ S.subSpace i := mem_insert_of_mem hep
  have heqV : eq_ ∈ S.subSpace i := mem_insert_of_mem heq_
  have hepqV : epq ∈ S.subSpace i := mem_insert_of_mem hepq
  -- Construct `g1, g2 ∈ V_i` with `(symp p, symp q)` equal to `(1, 0)` and `(0, 1)`.
  have hex : ∃ g1 g2 : Pt 4, g1 ∈ S.subSpace i ∧ g2 ∈ S.subSpace i ∧
      symp p g1 = 1 ∧ symp q g1 = 0 ∧ symp p g2 = 0 ∧ symp q g2 = 1 := by
    rw [ExactDegreesN4N5.symp_add_left] at hpq_e
    rcases zmod2_cases (symp p epq) with h1 | h1 <;> rcases zmod2_cases (symp q epq) with h2 | h2
    · rw [h1, h2] at hpq_e; exact absurd hpq_e (by decide)
    · -- `epq` has `(0, 1)`.
      rcases zmod2_cases (symp q ep) with h3 | h3
      · exact ⟨ep, epq, hepV, hepqV, hpep, h3, h1, h2⟩
      · refine ⟨ep + epq, epq, S.subSpace_add i hepV hepqV, hepqV, ?_, ?_, h1, h2⟩
        · rw [symp_add_right, hpep, h1, add_zero]
        · rw [symp_add_right, h3, h2]; decide
    · -- `epq` has `(1, 0)`.
      rcases zmod2_cases (symp p eq_) with h3 | h3
      · exact ⟨epq, eq_, hepqV, heqV, h1, h2, h3, hqeq⟩
      · refine ⟨epq, eq_ + epq, hepqV, S.subSpace_add i heqV hepqV, h1, h2, ?_, ?_⟩
        · rw [symp_add_right, h3, h1]; decide
        · rw [symp_add_right, hqeq, h2, add_zero]
    · rw [h1, h2] at hpq_e; exact absurd hpq_e (by decide)
  obtain ⟨g1, g2, hg1, hg2, hp1, hq1, hp2, hq2⟩ := hex
  set F : ZMod 2 → ZMod 2 → Finset (Pt 4) :=
    fun c1 c2 => (S.subSpace i).filter fun z => symp p z = c1 ∧ symp q z = c2
  have hshift : ∀ (c1 c2 d1 d2 : ZMod 2) (g : Pt 4), g ∈ S.subSpace i →
      symp p g = d1 → symp q g = d2 → (F c1 c2).card = (F (c1 + d1) (c2 + d2)).card := by
    intro c1 c2 d1 d2 g hg hpg hqg
    refine Finset.card_nbij' (fun z => z + g) (fun z => z + g) ?_ ?_ ?_ ?_
    · intro z hz
      obtain ⟨hzV, hzp, hzq⟩ := mem_filter.mp hz
      exact mem_filter.mpr ⟨S.subSpace_add i hzV hg,
        by rw [symp_add_right, hzp, hpg], by rw [symp_add_right, hzq, hqg]⟩
    · intro z hz
      obtain ⟨hzV, hzp, hzq⟩ := mem_filter.mp hz
      exact mem_filter.mpr ⟨S.subSpace_add i hzV hg,
        by rw [symp_add_right, hzp, hpg, add_assoc, zmod2_add_self, add_zero],
        by rw [symp_add_right, hzq, hqg, add_assoc, zmod2_add_self, add_zero]⟩
    · intro z _; show z + g + g = z; rw [add_assoc, pt_add_self, add_zero]
    · intro z _; show z + g + g = z; rw [add_assoc, pt_add_self, add_zero]
  have e01 : (F 0 0).card = (F 0 1).card := by simpa using hshift 0 0 0 1 g2 hg2 hp2 hq2
  have e10 : (F 0 0).card = (F 1 0).card := by simpa using hshift 0 0 1 0 g1 hg1 hp1 hq1
  have e11 : (F 0 0).card = (F 1 1).card := by
    have := hshift 0 0 1 1 (g1 + g2) (S.subSpace_add i hg1 hg2)
      (by rw [symp_add_right, hp1, hp2, add_zero])
      (by rw [symp_add_right, hq1, hq2, zero_add])
    simpa using this
  have hpart : S.subSpace i = (F 0 0 ∪ F 0 1) ∪ (F 1 0 ∪ F 1 1) := by
    ext z
    simp only [F, mem_union, mem_filter]
    constructor
    · intro hz
      rcases zmod2_cases (symp p z) with h1 | h1 <;> rcases zmod2_cases (symp q z) with h2 | h2
      · exact Or.inl (Or.inl ⟨hz, h1, h2⟩)
      · exact Or.inl (Or.inr ⟨hz, h1, h2⟩)
      · exact Or.inr (Or.inl ⟨hz, h1, h2⟩)
      · exact Or.inr (Or.inr ⟨hz, h1, h2⟩)
    · rintro ((⟨h, _⟩ | ⟨h, _⟩) | (⟨h, _⟩ | ⟨h, _⟩)) <;> exact h
  have hd_l : Disjoint (F 0 0) (F 0 1) := by
    rw [Finset.disjoint_left]; intro z h1 h2
    exact absurd ((mem_filter.mp h1).2.2.symm.trans (mem_filter.mp h2).2.2) (by decide)
  have hd_r : Disjoint (F 1 0) (F 1 1) := by
    rw [Finset.disjoint_left]; intro z h1 h2
    exact absurd ((mem_filter.mp h1).2.2.symm.trans (mem_filter.mp h2).2.2) (by decide)
  have hd_lr : Disjoint (F 0 0 ∪ F 0 1) (F 1 0 ∪ F 1 1) := by
    rw [Finset.disjoint_left]; intro z h1 h2
    have hz1 : symp p z = 0 := by rcases mem_union.mp h1 with h | h <;> exact (mem_filter.mp h).2.1
    have hz2 : symp p z = 1 := by rcases mem_union.mp h2 with h | h <;> exact (mem_filter.mp h).2.1
    exact absurd (hz1.symm.trans hz2) (by decide)
  have htot := S.card_subSpace i
  rw [hpart, Finset.card_union_of_disjoint hd_lr, Finset.card_union_of_disjoint hd_l,
    Finset.card_union_of_disjoint hd_r, ← e01, ← e10, ← e11] at htot
  rcases zmod2_cases b1 with rfl | rfl <;> rcases zmod2_cases b2 with rfl | rfl <;>
    change (F _ _).card = 4 <;> omega

lemma card_solid_pair_filter (S : SolidSpread) (i : Fin 9) {p q : Pt 4}
    (hp : p ∉ S.subSpace i) (hq : q ∉ S.subSpace i) (hpq : p + q ∉ S.subSpace i)
    {b1 b2 : ZMod 2} (hb : b1 = 1 ∨ b2 = 1) :
    ((S.solid i).filter fun z => symp p z = b1 ∧ symp q z = b2).card = 4 := by
  have heq : (S.solid i).filter (fun z => symp p z = b1 ∧ symp q z = b2) =
      (S.subSpace i).filter fun z => symp p z = b1 ∧ symp q z = b2 := by
    ext z
    simp only [subSpace, mem_filter, mem_insert]
    constructor
    · rintro ⟨hz, h1, h2⟩; exact ⟨Or.inr hz, h1, h2⟩
    · rintro ⟨rfl | hz, h1, h2⟩
      · rw [symp_zero_right] at h1 h2
        rcases hb with rfl | rfl <;> exact absurd (by assumption) (by decide)
      · exact ⟨hz, h1, h2⟩
  rw [heq]
  exact S.card_subSpace_pair_filter i hp hq hpq b1 b2

/-- Direct-sum decomposition `V_i ⊕ V_j = Pt 4` for any two distinct solids `i ≠ j`. -/
lemma exists_unique_direct_sum (S : SolidSpread) {i j : Fin 9} (hij : i ≠ j) (w : Pt 4) :
    ∃! p : Pt 4 × Pt 4, p.1 ∈ S.subSpace i ∧ p.2 ∈ S.subSpace j ∧ p.1 + p.2 = w := by
  let f : Pt 4 × Pt 4 → Pt 4 := fun p => p.1 + p.2
  have hinj : Set.InjOn f ↑((S.subSpace i) ×ˢ (S.subSpace j)) := by
    intro a ha b hb hab
    obtain ⟨ha1, ha2⟩ := mem_product.mp (Finset.mem_coe.mp ha)
    obtain ⟨hb1, hb2⟩ := mem_product.mp (Finset.mem_coe.mp hb)
    have hsame : a.1 + b.1 = a.2 + b.2 := by
      have h1 : (a.1 + a.2) + (b.1 + b.2) = 0 := by change f a + f b = 0; rw [hab, pt_add_self]
      have h2 : (a.1 + b.1) + (a.2 + b.2) = 0 := by
        calc (a.1 + b.1) + (a.2 + b.2) = (a.1 + a.2) + (b.1 + b.2) := by abel
          _ = 0 := h1
      exact pt_eq_of_add_eq_zero h2
    have hmem_i : a.1 + b.1 ∈ S.subSpace i := S.subSpace_add i ha1 hb1
    have hmem_j : a.1 + b.1 ∈ S.subSpace j := hsame ▸ S.subSpace_add j ha2 hb2
    have h0 : a.1 + b.1 = 0 := by
      simp only [subSpace, mem_insert] at hmem_i hmem_j
      rcases hmem_i with h | hi'
      · exact h
      · rcases hmem_j with h | hj'
        · exact h
        · exact (Finset.disjoint_left.mp (S.disj i j hij) hi' hj').elim
    exact Prod.ext (pt_eq_of_add_eq_zero h0) (pt_eq_of_add_eq_zero (hsame.symm.trans h0))
  have hcard : (((S.subSpace i) ×ˢ (S.subSpace j)).image f).card = Fintype.card (Pt 4) := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_product, S.card_subSpace i, S.card_subSpace j,
      card_pt]; norm_num
  have himg : ((S.subSpace i) ×ˢ (S.subSpace j)).image f = univ :=
    Finset.eq_univ_of_card _ hcard
  have hw : w ∈ ((S.subSpace i) ×ˢ (S.subSpace j)).image f := himg ▸ mem_univ w
  obtain ⟨p, hp, hpw⟩ := mem_image.mp hw
  obtain ⟨hp1, hp2⟩ := mem_product.mp hp
  refine ⟨p, ⟨hp1, hp2, hpw⟩, fun q ⟨hq1, hq2, hqw⟩ => ?_⟩
  exact hinj (Finset.mem_coe.mpr (mem_product.mpr ⟨hq1, hq2⟩))
    (Finset.mem_coe.mpr (mem_product.mpr ⟨hp1, hp2⟩)) (hqw.trans hpw.symm)

/-- Character-sum count `|Y| = 16` for `{y ∈ Q⁺(7,2) : ⟨u,y⟩=1, ⟨v,y⟩=0, ⟨x,y⟩=0}`. -/
private lemma card_Y_eq_16 {u v x : Pt 4}
    (hu : u ∈ realPoints 4) (hv : v ∈ realPoints 4) (hx : x ∈ realPoints 4)
    (huv_ne : u + v ≠ 0) (huv : symp u v = 0) (hux : symp u x = 0) (hvx : symp v x = 1) :
    ((realPoints 4).filter fun y => symp u y = 1 ∧ symp v y = 0 ∧ symp x y = 0).card = 16 := by
  obtain ⟨hu0, hqu⟩ := (mem_filter.mp hu).2
  obtain ⟨hv0, hqv⟩ := (mem_filter.mp hv).2
  obtain ⟨hx0, hqx⟩ := (mem_filter.mp hx).2
  have heq : (realPoints 4).filter (fun y => symp u y = 1 ∧ symp v y = 0 ∧ symp x y = 0) =
      univ.filter fun y : Pt 4 => qform y = 0 ∧ symp u y = 1 ∧ symp v y = 0 ∧ symp x y = 0 := by
    ext y
    simp only [realPoints, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, hqy⟩, h1, h2, h3⟩; exact ⟨hqy, h1, h2, h3⟩
    · rintro ⟨hqy, h1, h2, h3⟩
      exact ⟨⟨fun h0 => absurd (by rw [h0, symp_zero_right] at h1; exact h1) (by decide), hqy⟩, h1, h2, h3⟩
  rw [heq]
  have hux_ne : u + x ≠ 0 := by
    intro h
    have : symp v (u + x) = 0 := by rw [h, symp_zero_right]
    rw [symp_add_right, symp_comm v u, huv, hvx] at this
    exact absurd this (by decide)
  have hvx_ne : v + x ≠ 0 := by
    intro h
    have : symp v (v + x) = 0 := by rw [h, symp_zero_right]
    rw [symp_add_right, symp_self, hvx] at this
    exact absurd this (by decide)
  have huvx_ne : u + v + x ≠ 0 := by
    intro h
    have : symp v (u + v + x) = 0 := by rw [h, symp_zero_right]
    rw [symp_add_right, symp_add_right, symp_comm v u, huv, symp_self, hvx] at this
    exact absurd this (by decide)
  have hquv : qform (u + v) = 0 := by rw [qform_add, hqu, hqv, huv]; simp
  have hqux : qform (u + x) = 0 := by rw [qform_add, hqu, hqx, hux]; simp
  have hqvx : qform (v + x) = 1 := by rw [qform_add, hqv, hqx, hvx]; simp
  have hquvx : qform (u + v + x) = 1 := by
    rw [qform_add, hquv, hqx, ExactDegreesN4N5.symp_add_left, hux, hvx]; simp
  have hind : ∀ y : Pt 4,
      (if qform y = 0 ∧ symp u y = 1 ∧ symp v y = 0 ∧ symp x y = 0 then (1 : ℂ) else 0) =
      ((1 + eps (qform y)) * (1 - eps (symp u y)) * (1 + eps (symp v y)) * (1 + eps (symp x y))) / 16 := by
    intro y
    have hq : (if qform y = 0 then (1 : ℂ) else 0) = (1 + eps (qform y)) / 2 := indicator_eq _
    have h1 : (if symp u y = 1 then (1 : ℂ) else 0) = (1 - eps (symp u y)) / 2 := by
      rcases zmod2_cases (symp u y) with h | h <;> simp [h]
    have h2 : (if symp v y = 0 then (1 : ℂ) else 0) = (1 + eps (symp v y)) / 2 := indicator_eq _
    have h3 : (if symp x y = 0 then (1 : ℂ) else 0) = (1 + eps (symp x y)) / 2 := indicator_eq _
    have hmul : (if qform y = 0 ∧ symp u y = 1 ∧ symp v y = 0 ∧ symp x y = 0 then (1 : ℂ) else 0) =
        (if qform y = 0 then (1 : ℂ) else 0) * (if symp u y = 1 then (1 : ℂ) else 0) *
        (if symp v y = 0 then (1 : ℂ) else 0) * (if symp x y = 0 then (1 : ℂ) else 0) := by
      by_cases c0 : qform y = 0 <;> by_cases c1 : symp u y = 1 <;>
        by_cases c2 : symp v y = 0 <;> by_cases c3 : symp x y = 0 <;> simp [c0, c1, c2, c3]
    rw [hmul, hq, h1, h2, h3]; ring
  have hC : (((univ.filter fun y : Pt 4 => qform y = 0 ∧ symp u y = 1 ∧ symp v y = 0 ∧ symp x y = 0).card : ℕ) : ℂ) = 16 := by
    rw [Finset.card_filter]; push_cast
    simp_rw [hind, ← Finset.sum_div]
    have hexp : ∀ y : Pt 4,
        (1 + eps (qform y)) * (1 - eps (symp u y)) * (1 + eps (symp v y)) * (1 + eps (symp x y)) =
        1 - eps (symp u y) + eps (symp v y) + eps (symp x y) -
          eps (symp (u + v) y) - eps (symp (u + x) y) + eps (symp (v + x) y) -
          eps (symp (u + v + x) y) +
          eps (qform y) - eps (qform y + symp u y) + eps (qform y + symp v y) +
          eps (qform y + symp x y) - eps (qform y + symp (u + v) y) -
          eps (qform y + symp (u + x) y) + eps (qform y + symp (v + x) y) -
          eps (qform y + symp (u + v + x) y) := by
      intro y
      simp only [ExactDegreesN4N5.symp_add_left, eps_add]
      ring
    simp only [hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      sum_eps_symp hu0, sum_eps_symp hv0, sum_eps_symp hx0, sum_eps_symp huv_ne,
      sum_eps_symp hux_ne, sum_eps_symp hvx_ne, sum_eps_symp huvx_ne,
      sum_eps_qform, sum_eps_qform_add_symp, hqu, hqv, hqx, hquv, hqux, hqvx, hquvx,
      eps_zero, eps_one, Finset.sum_const, Finset.card_univ, card_pt, nsmul_eq_mul, mul_one]
    norm_num
  exact_mod_cast hC

open Classical in
/-- The set of all residual Mermin–Peres 4-tuples `(u, v, x, y)` in `Q⁺(7,2) \ S`. -/
noncomputable def mpTuples (S : SolidSpread) : Finset ((Pt 4 × Pt 4) × (Pt 4 × Pt 4)) :=
  (S.resFlags ×ˢ S.resFlags).filter fun g =>
    let u := g.1.1; let v := g.1.2; let x := g.2.1; let y := g.2.2
    (u + x, v + y) ∈ S.resFlags ∧
    (u, x) ∈ S.resFlags ∧
    (v, y) ∈ S.resFlags ∧
    (u + v, x + y) ∈ S.resFlags ∧
    symp u y = 1 ∧ symp v x = 1

open Classical in
lemma mem_mpTuples {S : SolidSpread} {g : (Pt 4 × Pt 4) × (Pt 4 × Pt 4)} :
    g ∈ S.mpTuples ↔ g.1 ∈ S.resFlags ∧ g.2 ∈ S.resFlags ∧
      (g.1.1 + g.2.1, g.1.2 + g.2.2) ∈ S.resFlags ∧
      (g.1.1, g.2.1) ∈ S.resFlags ∧
      (g.1.2, g.2.2) ∈ S.resFlags ∧
      (g.1.1 + g.1.2, g.2.1 + g.2.2) ∈ S.resFlags ∧
      symp g.1.1 g.2.2 = 1 ∧ symp g.1.2 g.2.1 = 1 := by
  simp only [mpTuples, mem_filter, mem_product, and_assoc]

set_option maxHeartbeats 400000 in
/-- **Key Exact Fiber Count:** every residual flag `(u, v) ∈ S.resFlags` extends to
EXACTLY `48 = 24 × 2` residual Mermin–Peres 4-tuples `(u, v, x, y) ∈ S.mpTuples`! -/
theorem card_mpTuples_fiber (S : SolidSpread) {p : Pt 4 × Pt 4} (hp : p ∈ S.resFlags) :
    ((S.mpTuples).filter fun g => g.1 = p).card = 48 := by
  classical
  rcases p with ⟨u, v⟩
  obtain ⟨hpF, hnot_same⟩ := mem_resFlags.mp hp
  obtain ⟨huR, hvR, huvR, huv⟩ := mem_q7pFlags.mp hpF
  dsimp only at huR hvR huvR huv hnot_same
  have hu0 : u ≠ 0 := (mem_real4.mp huR).1
  have hv0 : v ≠ 0 := (mem_real4.mp hvR).1
  have huv_ne : u + v ≠ 0 := (mem_real4.mp huvR).1
  have hqu : qform u = 0 := (mem_real4.mp huR).2
  have hqv : qform v = 0 := (mem_real4.mp hvR).2
  obtain ⟨a, ha, ha_uniq⟩ := S.exists_unique_solid huR
  obtain ⟨b, hb, hb_uniq⟩ := S.exists_unique_solid hvR
  obtain ⟨c, hc, hc_uniq⟩ := S.exists_unique_solid huvR
  have hab : a ≠ b := fun h => hnot_same a ⟨ha, h ▸ hb⟩
  have hac : a ≠ c := by
    intro h
    have hv_in : v ∈ S.subSpace a := by
      have : v = u + (u + v) := by rw [← add_assoc, pt_add_self, zero_add]
      rw [this]; exact S.subSpace_add a (mem_insert_of_mem ha) (mem_insert_of_mem (h ▸ hc))
    rcases mem_insert.mp hv_in with hv0' | hva
    · exact hv0 hv0'
    · exact hab (ha_uniq b (by exact absurd hva (Finset.disjoint_left.mp (S.disj b a hab.symm) hb))).symm
  have hbc : b ≠ c := by
    intro h
    have hu_in : u ∈ S.subSpace b := by
      have : u = v + (u + v) := by rw [add_comm u v, ← add_assoc, pt_add_self, zero_add]
      rw [this]; exact S.subSpace_add b (mem_insert_of_mem hb) (mem_insert_of_mem (h ▸ hc))
    rcases mem_insert.mp hu_in with hu0' | hub
    · exact hu0 hu0'
    · exact hab (ha_uniq b hub).symm
  -- Define the `24`-element set `Xset` of valid `x` using irreducible `q7pPts`.
  let Xset : Finset (Pt 4) := q7pPts.filter fun x =>
    symp u x = 0 ∧ symp v x = 1 ∧ x ∉ S.solid a
  have mem_Xset : ∀ {x : Pt 4}, x ∈ Xset ↔ x ∈ realPoints 4 ∧ symp u x = 0 ∧ symp v x = 1 ∧ x ∉ S.solid a := by
    intro x; simp only [Xset, mem_filter, mem_q7pPts]
  -- Helper: any valid `x` lies in some `S.solid d` with `d ∉ {a, b, c}`.
  have hX_solid : ∀ {x : Pt 4}, x ∈ realPoints 4 → symp u x = 0 → symp v x = 1 → x ∉ S.solid a →
      ∃ d : Fin 9, d ≠ a ∧ d ≠ b ∧ d ≠ c ∧ x ∈ S.solid d := by
    intro x hxR hux hvx hxa
    obtain ⟨d, hd, _⟩ := S.exists_unique_solid hxR
    refine ⟨d, fun h => hxa (h ▸ hd), ?_, ?_, hd⟩
    · intro h
      have := S.comm b v hb x (h ▸ hd)
      rw [hvx] at this; exact absurd this (by decide)
    · intro h
      have := S.comm c (u + v) hc x (h ▸ hd)
      rw [ExactDegreesN4N5.symp_add_left, hux, hvx] at this
      exact absurd this (by decide)
  -- `|Xset| = 24 = 6 * 4`.
  have hX_card : Xset.card = 24 := by
    let rem : Finset (Fin 9) := ((univ.erase a).erase b).erase c
    have hrem_card : rem.card = 6 := by
      have hc_mem : c ∈ (univ.erase a).erase b :=
        mem_erase.mpr ⟨hbc.symm, mem_erase.mpr ⟨hac.symm, mem_univ c⟩⟩
      have hb_mem : b ∈ univ.erase a := mem_erase.mpr ⟨hab.symm, mem_univ b⟩
      rw [Finset.card_erase_of_mem hc_mem, Finset.card_erase_of_mem hb_mem,
        Finset.card_erase_of_mem (mem_univ a), Finset.card_univ, Fintype.card_fin]
    have hpart : Xset = rem.biUnion fun d => (S.solid d).filter fun x => symp u x = 0 ∧ symp v x = 1 := by
      ext x
      simp only [mem_Xset, mem_biUnion, mem_filter]
      constructor
      · rintro ⟨hxR, hux, hvx, hxa⟩
        obtain ⟨d, hda, hdb, hdc, hxd⟩ := hX_solid hxR hux hvx hxa
        exact ⟨d, mem_erase.mpr ⟨hdc, mem_erase.mpr ⟨hdb, mem_erase.mpr ⟨hda, mem_univ d⟩⟩⟩,
          hxd, hux, hvx⟩
      · rintro ⟨d, hd, hxd, hux, hvx⟩
        have hda : d ≠ a := (mem_erase.mp (mem_erase.mp (mem_erase.mp hd).2).2).1
        exact ⟨S.sub_real d hxd, hux, hvx,
          fun hxa => Finset.disjoint_left.mp (S.disj d a hda) hxd hxa⟩
    rw [hpart, Finset.card_biUnion]
    · have hterm : ∀ d ∈ rem, ((S.solid d).filter fun x => symp u x = 0 ∧ symp v x = 1).card = 4 := by
        intro d hd
        have hdc : d ≠ c := (mem_erase.mp hd).1
        have hdb : d ≠ b := (mem_erase.mp (mem_erase.mp hd).2).1
        have hda : d ≠ a := (mem_erase.mp (mem_erase.mp (mem_erase.mp hd).2).2).1
        have hu_not : u ∉ S.subSpace d := by
          simp only [subSpace, mem_insert, not_or]
          exact ⟨hu0, fun h => hda (ha_uniq d h)⟩
        have hv_not : v ∉ S.subSpace d := by
          simp only [subSpace, mem_insert, not_or]
          exact ⟨hv0, fun h => hdb (hb_uniq d h)⟩
        have huv_not : u + v ∉ S.subSpace d := by
          simp only [subSpace, mem_insert, not_or]
          exact ⟨huv_ne, fun h => hdc (hc_uniq d h)⟩
        exact S.card_solid_pair_filter d hu_not hv_not huv_not (Or.inr rfl)
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, hrem_card]; norm_num
    · intro d1 _ d2 _ hne
      exact Finset.disjoint_filter_filter (S.disj d1 d2 hne)
  -- For each fixed `x ∈ Xset`, count valid `y` and prove there are EXACTLY `2`!
  let Yvalid : Pt 4 → Finset (Pt 4) := fun x =>
    (q7pPts.filter fun y => symp u y = 1 ∧ symp v y = 0 ∧ symp x y = 0).filter fun y =>
      ((u, v), (x, y)) ∈ S.mpTuples
  have hYvalid_card : ∀ x ∈ Xset, (Yvalid x).card = 2 := by
    intro x hx
    obtain ⟨hxR, hux, hvx, hxa⟩ := mem_Xset.mp hx
    have hx0 : x ≠ 0 := (mem_real4.mp hxR).1
    have hqx : qform x = 0 := (mem_real4.mp hxR).2
    obtain ⟨d, hda, hdb, hdc, hxd⟩ := hX_solid hxR hux hvx hxa
    have hux_ne : u + x ≠ 0 := by
      intro h
      have : symp v (u + x) = 0 := by rw [h, symp_zero_right]
      rw [symp_add_right, symp_comm v u, huv, hvx] at this; exact absurd this (by decide)
    have huxR : u + x ∈ realPoints 4 :=
      mem_real4.mpr ⟨hux_ne, by rw [qform_add, hqu, hqx, hux]; simp⟩
    obtain ⟨g, hg, hg_uniq⟩ := S.exists_unique_solid huxR
    have hga : g ≠ a := by
      intro h
      have hx_in : x ∈ S.subSpace a := by
        have : x = u + (u + x) := by rw [← add_assoc, pt_add_self, zero_add]
        rw [this]; exact S.subSpace_add a (mem_insert_of_mem ha) (mem_insert_of_mem (h ▸ hg))
      rcases mem_insert.mp hx_in with hx0' | hxa'
      · exact hx0 hx0'
      · exact hda (by exact absurd hxa' (Finset.disjoint_left.mp (S.disj d a hda) hxd))
    have hgd : g ≠ d := by
      intro h
      have hu_in : u ∈ S.subSpace d := by
        have : u = x + (u + x) := by rw [add_comm u x, ← add_assoc, pt_add_self, zero_add]
        rw [this]; exact S.subSpace_add d (mem_insert_of_mem hxd) (mem_insert_of_mem (h ▸ hg))
      rcases mem_insert.mp hu_in with hu0' | hud
      · exact hu0 hu0'
      · exact hda (ha_uniq d hud)
    have hgb : g ≠ b := by
      intro h
      have := S.comm b v hb (u + x) (h ▸ hg)
      rw [symp_add_right, symp_comm v u, huv, hvx] at this; exact absurd this (by decide)
    have hgc : g ≠ c := by
      intro h
      have := S.comm c (u + v) hc (u + x) (h ▸ hg)
      rw [symp_add_right, ExactDegreesN4N5.symp_add_left, ExactDegreesN4N5.symp_add_left,
        symp_self, symp_comm v u, huv, hux, hvx] at this; exact absurd this (by decide)
    set Y := q7pPts.filter fun y => symp u y = 1 ∧ symp v y = 0 ∧ symp x y = 0
    have mem_Y : ∀ {y : Pt 4}, y ∈ Y ↔ y ∈ realPoints 4 ∧ symp u y = 1 ∧ symp v y = 0 ∧ symp x y = 0 := by
      intro y; simp only [Y, mem_filter, mem_q7pPts]
    have hY16 : Y.card = 16 := by
      have hYeq : Y = (realPoints 4).filter fun y => symp u y = 1 ∧ symp v y = 0 ∧ symp x y = 0 := by
        ext y; simp only [mem_Y, mem_filter]
      rw [hYeq]; exact card_Y_eq_16 huR hvR hxR huv_ne huv hux hvx
    -- The four bad subsets of `Y`:
    set B1 := Y.filter fun y => y ∈ S.solid b
    set B2 := Y.filter fun y => y ∈ S.solid d
    set B3 := Y.filter fun y => v + y ∈ S.solid g
    set B4 := Y.filter fun y => x + y ∈ S.solid c
    have mem_B1 : ∀ {y : Pt 4}, y ∈ B1 ↔ y ∈ Y ∧ y ∈ S.solid b := fun {y} => by simp only [B1, mem_filter]
    have mem_B2 : ∀ {y : Pt 4}, y ∈ B2 ↔ y ∈ Y ∧ y ∈ S.solid d := fun {y} => by simp only [B2, mem_filter]
    have mem_B3 : ∀ {y : Pt 4}, y ∈ B3 ↔ y ∈ Y ∧ v + y ∈ S.solid g := fun {y} => by simp only [B3, mem_filter]
    have mem_B4 : ∀ {y : Pt 4}, y ∈ B4 ↔ y ∈ Y ∧ x + y ∈ S.solid c := fun {y} => by simp only [B4, mem_filter]
    -- Show `Yvalid x = Y \ (B1 ∪ B4 ∪ (B2 ∪ B3))`!
    have hYvalid_eq : Yvalid x = Y \ ((B1 ∪ B4) ∪ (B2 ∪ B3)) := by
      ext y
      simp only [Yvalid, mem_filter, mem_q7pPts, mem_sdiff, mem_union, not_or, mem_B1, mem_B2, mem_B3, mem_B4]
      constructor
      · rintro ⟨hyY0, hmp⟩
        have hyY : y ∈ Y := mem_Y.mpr hyY0
        obtain ⟨_, hxyF, hrow2F, _, hvyF, hcol2F, _, _⟩ := mem_mpTuples.mp hmp
        refine ⟨hyY, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
        · rintro ⟨_, hyb⟩
          exact (mem_resFlags.mp hvyF).2 b ⟨hb, hyb⟩
        · rintro ⟨_, hxyc⟩
          exact (mem_resFlags.mp hcol2F).2 c ⟨hc, hxyc⟩
        · rintro ⟨_, hyd⟩
          exact (mem_resFlags.mp hxyF).2 d ⟨hxd, hyd⟩
        · rintro ⟨_, hvyg⟩
          exact (mem_resFlags.mp hrow2F).2 g ⟨hg, hvyg⟩
      · rintro ⟨hyY, ⟨hnb, hnc⟩, ⟨hnd, hng⟩⟩
        obtain ⟨hyR, huy, hvy, hxy⟩ := mem_Y.mp hyY
        refine ⟨⟨hyR, huy, hvy, hxy⟩, ?_⟩
        have hqy : qform y = 0 := (mem_real4.mp hyR).2
        have hxy_ne : x + y ≠ 0 := by
          intro h
          have : symp u (x + y) = 0 := by rw [h, symp_zero_right]
          rw [symp_add_right, hux, huy] at this; exact absurd this (by decide)
        have hvy_ne : v + y ≠ 0 := by
          intro h
          have : symp u (v + y) = 0 := by rw [h, symp_zero_right]
          rw [symp_add_right, huv, huy] at this; exact absurd this (by decide)
        have huvxy_ne : (u + x) + (v + y) ≠ 0 := by
          intro h
          have hy_eq : y = u + v + x := by
            have : (u + v + x) + y = 0 := by
              calc (u + v + x) + y = (u + x) + (v + y) := by abel
                _ = 0 := h
            exact (pt_eq_of_add_eq_zero this).symm
          have hqy' := hqy
          rw [hy_eq, qform_add, qform_add, hqu, hqv, hqx, huv, ExactDegreesN4N5.symp_add_left, hux, hvx] at hqy'
          exact absurd hqy' (by decide)
        have hxyR : x + y ∈ realPoints 4 :=
          mem_real4.mpr ⟨hxy_ne, by rw [qform_add, hqx, hqy, hxy]; simp⟩
        have hvyR : v + y ∈ realPoints 4 :=
          mem_real4.mpr ⟨hvy_ne, by rw [qform_add, hqv, hqy, hvy]; simp⟩
        have hrow2_symp : symp (u + x) (v + y) = 0 := by
          rw [symp_add_right, ExactDegreesN4N5.symp_add_left, ExactDegreesN4N5.symp_add_left,
            huv, symp_comm x v, hvx, huy, hxy]; decide
        have hcol2_symp : symp (u + v) (x + y) = 0 := by
          rw [symp_add_right, ExactDegreesN4N5.symp_add_left, ExactDegreesN4N5.symp_add_left,
            hux, huy, hvx, hvy]; decide
        have huvxyR : (u + x) + (v + y) ∈ realPoints 4 :=
          mem_real4.mpr ⟨huvxy_ne, by
            rw [qform_add, (mem_real4.mp huxR).2, (mem_real4.mp hvyR).2, hrow2_symp]; simp⟩
        have huvxyR' : (u + v) + (x + y) ∈ realPoints 4 := by
          have : (u + v) + (x + y) = (u + x) + (v + y) := by abel
          rwa [this]
        have hres_xy : (x, y) ∈ S.resFlags := mem_resFlags.mpr ⟨mem_q7pFlags.mpr ⟨hxR, hyR, hxyR, hxy⟩,
          fun i ⟨hxi, hyi⟩ => hnd ⟨hyY, (by
            have hid : i = d := by
              by_contra hne; exact Finset.disjoint_left.mp (S.disj i d hne) hxi hxd
            exact hid ▸ hyi)⟩⟩
        have hres_ux : (u, x) ∈ S.resFlags := mem_resFlags.mpr ⟨mem_q7pFlags.mpr ⟨huR, hxR, huxR, hux⟩,
          fun i ⟨hui, hxi⟩ => hda (by
            have hia : i = a := ha_uniq i hui
            have hid : i = d := by
              by_contra hne; exact Finset.disjoint_left.mp (S.disj i d hne) hxi hxd
            exact hid.symm.trans hia)⟩
        have hres_vy : (v, y) ∈ S.resFlags := mem_resFlags.mpr ⟨mem_q7pFlags.mpr ⟨hvR, hyR, hvyR, hvy⟩,
          fun i ⟨hvi, hyi⟩ => hnb ⟨hyY, hb_uniq i hvi ▸ hyi⟩⟩
        have hres_r2 : (u + x, v + y) ∈ S.resFlags :=
          mem_resFlags.mpr ⟨mem_q7pFlags.mpr ⟨huxR, hvyR, huvxyR, hrow2_symp⟩,
            fun i ⟨h1, h2⟩ => hng ⟨hyY, hg_uniq i h1 ▸ h2⟩⟩
        have hres_c2 : (u + v, x + y) ∈ S.resFlags :=
          mem_resFlags.mpr ⟨mem_q7pFlags.mpr ⟨huvR, hxyR, huvxyR', hcol2_symp⟩,
            fun i ⟨h1, h2⟩ => hnc ⟨hyY, hc_uniq i h1 ▸ h2⟩⟩
        exact mem_mpTuples.mpr ⟨hp, hres_xy, hres_r2, hres_ux, hres_vy, hres_c2,
          huy, hvx⟩
    -- Compute `|B1| = |B2| = |B3| = |B4| = 4`.
    have hnot_in : ∀ (k : Fin 9) (p0 : Pt 4), p0 ∈ realPoints 4 →
        (∀ j, p0 ∈ S.solid j → j ≠ k) → p0 ∉ S.subSpace k := by
      intro k p0 hp0 hneq hmem
      rcases mem_insert.mp hmem with h0 | hk
      · exact (mem_real4.mp hp0).1 h0
      · exact hneq k hk rfl
    have hB1 : B1.card = 4 := by
      have heq : B1 = (S.solid b).filter fun y => symp u y = 1 ∧ symp x y = 0 := by
        ext y; simp only [mem_B1, mem_Y, mem_filter]
        constructor
        · rintro ⟨⟨_, huy, _, hxy⟩, hyb⟩; exact ⟨hyb, huy, hxy⟩
        · rintro ⟨hyb, huy, hxy⟩; exact ⟨⟨S.sub_real b hyb, huy, S.comm b v hb y hyb, hxy⟩, hyb⟩
      rw [heq]
      exact S.card_solid_pair_filter b
        (hnot_in b u huR fun j hj => (ha_uniq j hj).symm ▸ hab)
        (hnot_in b x hxR fun j hj => by
          have : j = d := by by_contra hne; exact Finset.disjoint_left.mp (S.disj j d hne) hj hxd
          exact this.symm ▸ hdb)
        (hnot_in b (u + x) huxR fun j hj => (hg_uniq j hj).symm ▸ hgb)
        (Or.inl rfl)
    have hB2 : B2.card = 4 := by
      have heq : B2 = (S.solid d).filter fun y => symp u y = 1 ∧ symp v y = 0 := by
        ext y; simp only [mem_B2, mem_Y, mem_filter]
        constructor
        · rintro ⟨⟨_, huy, hvy, _⟩, hyd⟩; exact ⟨hyd, huy, hvy⟩
        · rintro ⟨hyd, huy, hvy⟩; exact ⟨⟨S.sub_real d hyd, huy, hvy, S.comm d x hxd y hyd⟩, hyd⟩
      rw [heq]
      exact S.card_solid_pair_filter d
        (hnot_in d u huR fun j hj => (ha_uniq j hj).symm ▸ hda.symm)
        (hnot_in d v hvR fun j hj => (hb_uniq j hj).symm ▸ hdb.symm)
        (hnot_in d (u + v) huvR fun j hj => (hc_uniq j hj).symm ▸ hdc.symm)
        (Or.inl rfl)
    have hB3 : B3.card = 4 := by
      have hbij : B3.card = ((S.solid g).filter fun z => symp u z = 1 ∧ symp v z = 0).card := by
        refine Finset.card_nbij' (fun y => v + y) (fun z => v + z) ?_ ?_ ?_ ?_
        · intro y hy
          obtain ⟨hyY, hvy_g⟩ := mem_B3.mp hy
          obtain ⟨_, huy, hvy, _⟩ := mem_Y.mp hyY
          exact mem_filter.mpr ⟨hvy_g, by rw [symp_add_right, huv, huy, zero_add],
            by rw [symp_add_right, symp_self, hvy, zero_add]⟩
        · intro z hz
          simp only [mem_coe, mem_filter] at hz
          obtain ⟨hzg, huz, hvz⟩ := hz
          have hzv_ne : v + z ≠ 0 := by
            intro h; have : symp u (v + z) = 0 := by rw [h, symp_zero_right]
            rw [symp_add_right, huv, huz] at this; exact absurd this (by decide)
          have hzvR : v + z ∈ realPoints 4 := mem_real4.mpr ⟨hzv_ne, by
            rw [qform_add, hqv, (mem_real4.mp (S.sub_real g hzg)).2, hvz]; simp⟩
          have hxz : symp x z = 1 := by
            have := S.comm g (u + x) hg z hzg
            rw [ExactDegreesN4N5.symp_add_left, huz] at this
            rcases zmod2_cases (symp x z) with h | h
            · rw [h] at this; exact absurd this (by decide)
            · exact h
          exact mem_B3.mpr ⟨mem_Y.mpr ⟨hzvR,
            by rw [symp_add_right, huv, huz, zero_add],
            by rw [symp_add_right, symp_self, hvz, zero_add],
            by rw [symp_add_right, symp_comm x v, hvx, hxz]; decide⟩,
            by rw [← add_assoc, pt_add_self, zero_add]; exact hzg⟩
        · intro y _; show v + (v + y) = y; rw [← add_assoc, pt_add_self, zero_add]
        · intro z _; show v + (v + z) = z; rw [← add_assoc, pt_add_self, zero_add]
      rw [hbij]
      exact S.card_solid_pair_filter g
        (hnot_in g u huR fun j hj => (ha_uniq j hj).symm ▸ hga.symm)
        (hnot_in g v hvR fun j hj => (hb_uniq j hj).symm ▸ hgb.symm)
        (hnot_in g (u + v) huvR fun j hj => (hc_uniq j hj).symm ▸ hgc.symm)
        (Or.inl rfl)
    have hB4 : B4.card = 4 := by
      have hbij : B4.card = ((S.solid c).filter fun z => symp u z = 1 ∧ symp x z = 0).card := by
        refine Finset.card_nbij' (fun y => x + y) (fun z => x + z) ?_ ?_ ?_ ?_
        · intro y hy
          obtain ⟨hyY, hxy_c⟩ := mem_B4.mp hy
          obtain ⟨_, huy, _, hxy⟩ := mem_Y.mp hyY
          exact mem_filter.mpr ⟨hxy_c, by rw [symp_add_right, hux, huy, zero_add],
            by rw [symp_add_right, symp_self, hxy, zero_add]⟩
        · intro z hz
          simp only [mem_coe, mem_filter] at hz
          obtain ⟨hzc, huz, hxz⟩ := hz
          have hzx_ne : x + z ≠ 0 := by
            intro h; have : symp u (x + z) = 0 := by rw [h, symp_zero_right]
            rw [symp_add_right, hux, huz] at this; exact absurd this (by decide)
          have hzxR : x + z ∈ realPoints 4 := mem_real4.mpr ⟨hzx_ne, by
            rw [qform_add, hqx, (mem_real4.mp (S.sub_real c hzc)).2, hxz]; simp⟩
          have hvz : symp v z = 1 := by
            have := S.comm c (u + v) hc z hzc
            rw [ExactDegreesN4N5.symp_add_left, huz] at this
            rcases zmod2_cases (symp v z) with h | h
            · rw [h] at this; exact absurd this (by decide)
            · exact h
          exact mem_B4.mpr ⟨mem_Y.mpr ⟨hzxR,
            by rw [symp_add_right, hux, huz, zero_add],
            by rw [symp_add_right, hvx, hvz]; decide,
            by rw [symp_add_right, symp_self, hxz, zero_add]⟩,
            by rw [← add_assoc, pt_add_self, zero_add]; exact hzc⟩
        · intro y _; show x + (x + y) = y; rw [← add_assoc, pt_add_self, zero_add]
        · intro z _; show x + (x + z) = z; rw [← add_assoc, pt_add_self, zero_add]
      rw [hbij]
      exact S.card_solid_pair_filter c
        (hnot_in c u huR fun j hj => (ha_uniq j hj).symm ▸ hac)
        (hnot_in c x hxR fun j hj => by
          have : j = d := by by_contra hne; exact Finset.disjoint_left.mp (S.disj j d hne) hj hxd
          exact this.symm ▸ hdc)
        (hnot_in c (u + x) huxR fun j hj => (hg_uniq j hj).symm ▸ hgc)
        (Or.inl rfl)
    -- `|B1 ∩ B4| = 1` via direct sum `V_b ⊕ V_c = Pt 4` applied to `x`!
    have hB14 : (B1 ∩ B4).card = 1 := by
      obtain ⟨⟨y0, z0⟩, ⟨hy0V, hz0V, hyz⟩, huniq⟩ := S.exists_unique_direct_sum hbc x
      have hy0_ne : y0 ≠ 0 := by
        rintro rfl; rw [zero_add] at hyz
        rcases mem_insert.mp hz0V with h0 | hzc
        · exact hx0 (hyz.symm.trans h0)
        · exact hdc (by
            have : c = d := by by_contra hne; exact Finset.disjoint_left.mp (S.disj c d hne) (hyz ▸ hzc) hxd
            exact this.symm)
      have hz0_ne : z0 ≠ 0 := by
        rintro rfl; rw [add_zero] at hyz
        rcases mem_insert.mp hy0V with h0 | hyb
        · exact hx0 (hyz.symm.trans h0)
        · exact hdb (by
            have : b = d := by by_contra hne; exact Finset.disjoint_left.mp (S.disj b d hne) (hyz ▸ hyb) hxd
            exact this.symm)
      have hy0b : y0 ∈ S.solid b := (mem_insert.mp hy0V).resolve_left hy0_ne
      have hz0c : z0 ∈ S.solid c := (mem_insert.mp hz0V).resolve_left hz0_ne
      have hxy0_eq : x + y0 = z0 := by rw [← hyz, add_comm y0 z0, add_assoc, pt_add_self, add_zero]
      have hxy0 : symp x y0 = 0 := by
        have hqz : qform (x + y0) = 0 := hxy0_eq ▸ (mem_real4.mp (S.sub_real c hz0c)).2
        rw [qform_add, hqx, (mem_real4.mp (S.sub_real b hy0b)).2] at hqz
        simpa using hqz
      have hvy0 : symp v y0 = 0 := S.comm b v hb y0 hy0b
      have huy0 : symp u y0 = 1 := by
        have hcz := S.comm c (u + v) hc z0 hz0c
        rw [← hxy0_eq, symp_add_right, ExactDegreesN4N5.symp_add_left,
          ExactDegreesN4N5.symp_add_left, hux, hvx, hvy0] at hcz
        rcases zmod2_cases (symp u y0) with h | h
        · rw [h] at hcz; exact absurd hcz (by decide)
        · exact h
      have heq_s : B1 ∩ B4 = {y0} := by
        ext y
        simp only [mem_inter, mem_B1, mem_B4, mem_Y, mem_singleton]
        constructor
        · rintro ⟨⟨_, hyb⟩, ⟨_, hxyc⟩⟩
          have h := huniq (y, x + y) ⟨mem_insert_of_mem hyb, mem_insert_of_mem hxyc,
            by rw [add_comm x y, ← add_assoc, pt_add_self, zero_add]⟩
          exact congrArg Prod.fst h
        · rintro rfl
          exact ⟨⟨⟨S.sub_real b hy0b, huy0, hvy0, hxy0⟩, hy0b⟩,
            ⟨⟨S.sub_real b hy0b, huy0, hvy0, hxy0⟩, hxy0_eq ▸ hz0c⟩⟩
      rw [heq_s, Finset.card_singleton]
    -- `|B2 ∩ B3| = 1` via direct sum `V_d ⊕ V_g = Pt 4` applied to `v`!
    have hB23 : (B2 ∩ B3).card = 1 := by
      obtain ⟨⟨y0, z0⟩, ⟨hy0V, hz0V, hyz⟩, huniq⟩ := S.exists_unique_direct_sum hgd.symm v
      have hy0_ne : y0 ≠ 0 := by
        rintro rfl; rw [zero_add] at hyz
        rcases mem_insert.mp hz0V with h0 | hzg
        · exact hv0 (hyz.symm.trans h0)
        · exact hgb (hb_uniq g (hyz ▸ hzg))
      have hz0_ne : z0 ≠ 0 := by
        rintro rfl; rw [add_zero] at hyz
        rcases mem_insert.mp hy0V with h0 | hyd
        · exact hv0 (hyz.symm.trans h0)
        · exact hdb (hb_uniq d (hyz ▸ hyd))
      have hy0d : y0 ∈ S.solid d := (mem_insert.mp hy0V).resolve_left hy0_ne
      have hz0g : z0 ∈ S.solid g := (mem_insert.mp hz0V).resolve_left hz0_ne
      have hvy0_eq : v + y0 = z0 := by rw [← hyz, add_comm y0 z0, add_assoc, pt_add_self, add_zero]
      have hvy0 : symp v y0 = 0 := by
        have hqz : qform (v + y0) = 0 := hvy0_eq ▸ (mem_real4.mp (S.sub_real g hz0g)).2
        rw [qform_add, hqv, (mem_real4.mp (S.sub_real d hy0d)).2] at hqz
        simpa using hqz
      have hxy0 : symp x y0 = 0 := S.comm d x hxd y0 hy0d
      have huy0 : symp u y0 = 1 := by
        have hgz := S.comm g (u + x) hg z0 hz0g
        rw [← hvy0_eq, symp_add_right, ExactDegreesN4N5.symp_add_left,
          ExactDegreesN4N5.symp_add_left, huv, symp_comm x v, hvx, hxy0] at hgz
        rcases zmod2_cases (symp u y0) with h | h
        · rw [h] at hgz; exact absurd hgz (by decide)
        · exact h
      have heq_s : B2 ∩ B3 = {y0} := by
        ext y
        simp only [mem_inter, mem_B2, mem_B3, mem_Y, mem_singleton]
        constructor
        · rintro ⟨⟨_, hyd⟩, ⟨_, hvyg⟩⟩
          have h := huniq (y, v + y) ⟨mem_insert_of_mem hyd, mem_insert_of_mem hvyg,
            by rw [add_comm v y, ← add_assoc, pt_add_self, zero_add]⟩
          exact congrArg Prod.fst h
        · rintro rfl
          exact ⟨⟨⟨S.sub_real d hy0d, huy0, hvy0, hxy0⟩, hy0d⟩,
            ⟨⟨S.sub_real d hy0d, huy0, hvy0, hxy0⟩, hvy0_eq ▸ hz0g⟩⟩
      rw [heq_s, Finset.card_singleton]
    -- `B1 ∪ B4` and `B2 ∪ B3` are DISJOINT (including the 5-line proof of `B3 ∩ B4 = ∅`)!
    have hdisj_groups : Disjoint (B1 ∪ B4) (B2 ∪ B3) := by
      rw [Finset.disjoint_left]
      intro y hL hR
      rcases mem_union.mp hL with h1 | h4 <;> rcases mem_union.mp hR with h2 | h3
      · exact Finset.disjoint_left.mp (S.disj b d hdb.symm) (mem_B1.mp h1).2 (mem_B2.mp h2).2
      · have hyb := (mem_B1.mp h1).2
        have hvyg := (mem_B3.mp h3).2
        have hvy_in_b : v + y ∈ S.subSpace b := S.subSpace_add b (mem_insert_of_mem hb) (mem_insert_of_mem hyb)
        rcases mem_insert.mp hvy_in_b with h0 | hvyb
        · exact S.zero_not_mem_solid g (h0 ▸ hvyg)
        · exact Finset.disjoint_left.mp (S.disj b g hgb.symm) hvyb hvyg
      · have hxyc := (mem_B4.mp h4).2
        have hyd := (mem_B2.mp h2).2
        have hxy_in_d : x + y ∈ S.subSpace d := S.subSpace_add d (mem_insert_of_mem hxd) (mem_insert_of_mem hyd)
        rcases mem_insert.mp hxy_in_d with h0 | hxyd
        · exact S.zero_not_mem_solid c (h0 ▸ hxyc)
        · exact Finset.disjoint_left.mp (S.disj c d hdc.symm) hxyc hxyd
      · -- The 5-line jewel: `v + y ∈ S_g` and `x + y ∈ S_c` force `u + v + x + y ∈ V_g ∩ V_c = {0}`!
        have hvyg := (mem_B3.mp h3).2
        have hxyc := (mem_B4.mp h4).2
        have hyY := (mem_B3.mp h3).1
        have hqy : qform y = 0 := (mem_real4.mp (mem_Y.mp hyY).1).2
        have h_in_g : (u + x) + (v + y) ∈ S.subSpace g :=
          S.subSpace_add g (mem_insert_of_mem hg) (mem_insert_of_mem hvyg)
        have h_in_c : (u + x) + (v + y) ∈ S.subSpace c := by
          have : (u + x) + (v + y) = (u + v) + (x + y) := by abel
          rw [this]
          exact S.subSpace_add c (mem_insert_of_mem hc) (mem_insert_of_mem hxyc)
        have hzero : (u + x) + (v + y) = 0 := by
          rcases mem_insert.mp h_in_g with h0 | hg'
          · exact h0
          · rcases mem_insert.mp h_in_c with h0 | hc'
            · exact h0
            · exact (Finset.disjoint_left.mp (S.disj g c hgc) hg' hc').elim
        have hy_eq : y = u + v + x := by
          have : (u + v + x) + y = 0 := by
            calc (u + v + x) + y = (u + x) + (v + y) := by abel
              _ = 0 := hzero
          exact (pt_eq_of_add_eq_zero this).symm
        rw [hy_eq, qform_add, qform_add, hqu, hqv, hqx, huv, ExactDegreesN4N5.symp_add_left, hux, hvx] at hqy
        exact absurd hqy (by decide)
    -- Finish `|Yvalid x| = 16 - (7 + 7) = 2`!
    have hsubU : (B1 ∪ B4) ∪ (B2 ∪ B3) ⊆ Y := by
      intro y hy
      rcases mem_union.mp hy with hL | hR
      · rcases mem_union.mp hL with h | h
        · exact (mem_B1.mp h).1
        · exact (mem_B4.mp h).1
      · rcases mem_union.mp hR with h | h
        · exact (mem_B2.mp h).1
        · exact (mem_B3.mp h).1
    have h14 : (B1 ∪ B4).card = 7 := by
      have := Finset.card_union_add_card_inter B1 B4
      rw [hB1, hB4, hB14] at this; omega
    have h23 : (B2 ∪ B3).card = 7 := by
      have := Finset.card_union_add_card_inter B2 B3
      rw [hB2, hB3, hB23] at this; omega
    rw [hYvalid_eq, Finset.card_sdiff_of_subset hsubU, Finset.card_union_of_disjoint hdisj_groups,
      hY16, h14, h23]
  -- Now sum `|Yvalid x| = 2` over all `24` elements `x ∈ Xset` to get `48`!
  have hbij : ((S.mpTuples).filter fun g => g.1 = (u, v)).card =
      ∑ x ∈ Xset, (Yvalid x).card := by
    rw [← Finset.card_sigma]
    refine Finset.card_bij (fun g hg => ?_) ?_ ?_ ?_
    · exact ⟨g.2.1, g.2.2⟩
    · intro g hg
      rw [mem_filter] at hg
      obtain ⟨hgM, hg1⟩ := hg
      obtain ⟨_, h2F, _, huxF, hvyF, _, huy, hvx⟩ := mem_mpTuples.mp hgM
      rw [hg1] at huxF hvyF huy hvx
      have hxR : g.2.1 ∈ realPoints 4 := (mem_q7pFlags.mp (mem_resFlags.mp huxF).1).2.1
      have hux : symp u g.2.1 = 0 := (mem_q7pFlags.mp (mem_resFlags.mp huxF).1).2.2.2
      have hxa : g.2.1 ∉ S.solid a := fun h => (mem_resFlags.mp huxF).2 a ⟨ha, h⟩
      have hxX : g.2.1 ∈ Xset := mem_Xset.mpr ⟨hxR, hux, hvx, hxa⟩
      have hyR : g.2.2 ∈ realPoints 4 := (mem_q7pFlags.mp (mem_resFlags.mp hvyF).1).2.1
      have hvy : symp v g.2.2 = 0 := (mem_q7pFlags.mp (mem_resFlags.mp hvyF).1).2.2.2
      have hxy : symp g.2.1 g.2.2 = 0 := (mem_q7pFlags.mp (mem_resFlags.mp h2F).1).2.2.2
      have hyY : g.2.2 ∈ Yvalid g.2.1 := by
        simp only [Yvalid, mem_filter, mem_q7pPts]
        exact ⟨⟨hyR, huy, hvy, hxy⟩, by rw [← hg1]; exact hgM⟩
      exact Finset.mem_sigma.mpr ⟨hxX, hyY⟩
    · intro g1 hg1 g2 hg2 heq
      rw [mem_filter] at hg1 hg2
      have h1 := hg1.2
      have h2 := hg2.2
      have hx : g1.2.1 = g2.2.1 := congrArg Sigma.fst heq
      have hy : g1.2.2 = g2.2.2 := by
        simpa using congrArg Sigma.snd heq
      exact Prod.ext (h1.trans h2.symm) (Prod.ext hx hy)
    · intro s hs
      obtain ⟨hxX, hyY⟩ := Finset.mem_sigma.mp hs
      simp only [Yvalid, mem_filter, mem_q7pPts] at hyY
      exact ⟨((u, v), (s.1, s.2)), by simp only [mem_filter]; exact ⟨hyY.2, trivial⟩, rfl⟩
  rw [hbij, Finset.sum_congr rfl hYvalid_card, Finset.sum_const, hX_card]; norm_num

/-- Total residual flags of ANY 9-solid spread of `Q⁺(7,2)`: `|resFlags S| = 7,560`. -/
lemma card_resFlags (S : SolidSpread) : (S.resFlags).card = 7560 := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := q7pFlags)
    (fun p => ∀ i : Fin 9, ¬ (p.1 ∈ S.solid i ∧ p.2 ∈ S.solid i))
  have hres_eq : q7pFlags.filter (fun p => ∀ i : Fin 9, ¬ (p.1 ∈ S.solid i ∧ p.2 ∈ S.solid i)) =
      S.resFlags := by
    ext p; simp only [mem_resFlags, mem_filter]
  have hin_eq : q7pFlags.filter (fun p => ¬ ∀ i : Fin 9, ¬ (p.1 ∈ S.solid i ∧ p.2 ∈ S.solid i)) =
      (univ : Finset (Fin 9)).biUnion fun i => flags (S.solid i) := by
    ext p
    simp only [mem_filter, mem_biUnion, mem_univ, true_and, mem_q7pFlags, mem_flags]
    constructor
    · rintro ⟨⟨_, _, h3, hs⟩, hnot⟩
      push Not at hnot
      obtain ⟨i, h1, h2⟩ := hnot
      have hne : p.1 ≠ p.2 := fun h => (mem_filter.mp h3).2.1 (by rw [h, pt_add_self])
      exact ⟨i, h1, h2, S.closed i p.1 h1 p.2 h2 hne, hs⟩
    · rintro ⟨i, h1, h2, h3, hs⟩
      exact ⟨⟨S.sub_real i h1, S.sub_real i h2, S.sub_real i h3, hs⟩,
        fun hall => hall i ⟨h1, h2⟩⟩
  have hsolid_flags : ∀ i : Fin 9, (flags (S.solid i)).card = 210 := by
    intro i
    have hfl : flags (S.solid i) = (S.solid i).offDiag := by
      ext p
      simp only [mem_flags, mem_offDiag]
      constructor
      · rintro ⟨h1, h2, h3, _⟩
        exact ⟨h1, h2, fun h => S.zero_not_mem_solid i (by rwa [h, pt_add_self] at h3)⟩
      · rintro ⟨h1, h2, hne⟩
        exact ⟨h1, h2, S.closed i p.1 h1 p.2 h2 hne, S.comm i p.1 h1 p.2 h2⟩
    rw [hfl, Finset.offDiag_card, S.card_eq i]
  have hdisj : Set.PairwiseDisjoint (↑(univ : Finset (Fin 9))) fun i => flags (S.solid i) := by
    intro i _ j _ hij
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    exact Finset.disjoint_left.mp (S.disj i j hij) (mem_flags.mp hp1).1 (mem_flags.mp hp2).1
  have hin_card : ((univ : Finset (Fin 9)).biUnion fun i => flags (S.solid i)).card = 1890 := by
    rw [Finset.card_biUnion hdisj]
    simp [hsolid_flags]
  rw [hres_eq, hin_eq, hin_card, card_q7pFlags] at hsplit
  omega

/-- Each violated residual context carries at most `6` residual flags. -/
lemma card_resViolated_le_six (S : SolidSpread) (f : Pt 4 → ℝ) :
    (S.resViolated f).card ≤ 6 * (S.resViolatedLines f).card := by
  have h0 : (0 : Pt 4) ∉ realPoints 4 := by simp [realPoints]
  refine Finset.card_le_mul_card_image (S.resViolated f) 6 ?_
  intro L hL
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hL
  have hsub : ((S.resViolated f).filter fun p => lineOf p = lineOf q) ⊆ (lineOf q).offDiag := by
    intro p hp
    obtain ⟨hpv, hpl⟩ := mem_filter.mp hp
    have hpf : p ∈ q7pFlags := (mem_resFlags.mp (mem_resViolated.mp hpv).1).1
    obtain ⟨_, _, h3, _⟩ := mem_q7pFlags.mp hpf
    have hne : p.1 ≠ p.2 := fun h => h0 (by rwa [h, pt_add_self] at h3)
    rw [mem_offDiag, ← hpl]
    exact ⟨by simp [lineOf], by simp [lineOf], hne⟩
  calc ((S.resViolated f).filter fun p => lineOf p = lineOf q).card
      ≤ (lineOf q).offDiag.card := Finset.card_le_card hsub
    _ = (lineOf q).card * (lineOf q).card - (lineOf q).card := Finset.offDiag_card _
    _ ≤ 6 := by
        have h3 : (lineOf q).card ≤ 3 := by
          unfold lineOf
          exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ (by simp))))
        set k := (lineOf q).card; interval_cases k <;> norm_num

/-- **Theorem 23(a) — Universal Lower Bound (`d(Q⁺(7,2) \ Spread) ≥ 210`):**
For EVERY spread `S : SolidSpread` of 9 solids of `Q⁺(7,2)` and EVERY `±1` assignment `f`,
at least `210` of the `1,260` residual contexts are violated. -/
theorem spread_residual_ge_210 (S : SolidSpread) (f : Pt 4 → ℝ)
    (hf : ∀ u ∈ realPoints 4, f u = 1 ∨ f u = -1) :
    210 ≤ (S.resViolatedLines f).card := by
  classical
  let φ1 : ((Pt 4 × Pt 4) × (Pt 4 × Pt 4)) → ((Pt 4 × Pt 4) × (Pt 4 × Pt 4)) := fun g => g
  let φ2 : ((Pt 4 × Pt 4) × (Pt 4 × Pt 4)) → ((Pt 4 × Pt 4) × (Pt 4 × Pt 4)) := fun g => (g.2, g.1)
  let φ3 : ((Pt 4 × Pt 4) × (Pt 4 × Pt 4)) → ((Pt 4 × Pt 4) × (Pt 4 × Pt 4)) :=
    fun g => ((g.1.1 + g.2.1, g.1.2 + g.2.2), (g.2.1, g.2.2))
  let φ4 : ((Pt 4 × Pt 4) × (Pt 4 × Pt 4)) → ((Pt 4 × Pt 4) × (Pt 4 × Pt 4)) :=
    fun g => ((g.1.1, g.2.1), (g.1.2, g.2.2))
  let φ5 : ((Pt 4 × Pt 4) × (Pt 4 × Pt 4)) → ((Pt 4 × Pt 4) × (Pt 4 × Pt 4)) :=
    fun g => ((g.1.2, g.2.2), (g.1.1, g.2.1))
  let φ5i : ((Pt 4 × Pt 4) × (Pt 4 × Pt 4)) → ((Pt 4 × Pt 4) × (Pt 4 × Pt 4)) :=
    fun g => ((g.2.1, g.1.1), (g.2.2, g.1.2))
  let φ6 : ((Pt 4 × Pt 4) × (Pt 4 × Pt 4)) → ((Pt 4 × Pt 4) × (Pt 4 × Pt 4)) :=
    fun g => ((g.1.1 + g.1.2, g.2.1 + g.2.2), (g.1.2, g.2.2))
  let φ6i : ((Pt 4 × Pt 4) × (Pt 4 × Pt 4)) → ((Pt 4 × Pt 4) × (Pt 4 × Pt 4)) :=
    fun g => ((g.1.1 + g.2.1, g.2.1), (g.1.2 + g.2.2, g.2.2))
  have hres_swap : ∀ {a b : Pt 4}, (a, b) ∈ S.resFlags → (b, a) ∈ S.resFlags := by
    intro a b h
    obtain ⟨hF, hnot⟩ := mem_resFlags.mp h
    obtain ⟨h1, h2, h3, hs⟩ := mem_q7pFlags.mp hF
    exact mem_resFlags.mpr ⟨mem_q7pFlags.mpr ⟨h2, h1, by rwa [add_comm], by rwa [symp_comm]⟩,
      fun i ⟨hb, ha⟩ => hnot i ⟨ha, hb⟩⟩
  have hres_rot : ∀ {a b : Pt 4}, (a, b) ∈ S.resFlags → (a + b, b) ∈ S.resFlags := by
    intro a b h
    obtain ⟨hF, hnot⟩ := mem_resFlags.mp h
    obtain ⟨h1, h2, h3, hs⟩ := mem_q7pFlags.mp hF
    refine mem_resFlags.mpr ⟨mem_q7pFlags.mpr ⟨h3, h2, by rwa [add_assoc, pt_add_self, add_zero],
      by rw [ExactDegreesN4N5.symp_add_left, hs, symp_self, add_zero]⟩, fun i ⟨hab, hb⟩ => ?_⟩
    have ha_in : a ∈ S.subSpace i := by
      have : a = (a + b) + b := by rw [add_assoc, pt_add_self, add_zero]
      rw [this]; exact S.subSpace_add i (mem_insert_of_mem hab) (mem_insert_of_mem hb)
    rcases mem_insert.mp ha_in with ha0 | hai
    · exact (mem_filter.mp h1).2.1 ha0
    · exact hnot i ⟨hai, hb⟩
  have hcard_bij : ∀ (φ ψ : ((Pt 4 × Pt 4) × (Pt 4 × Pt 4)) → ((Pt 4 × Pt 4) × (Pt 4 × Pt 4))),
      (∀ g ∈ S.mpTuples, φ g ∈ S.mpTuples) →
      (∀ g ∈ S.mpTuples, ψ g ∈ S.mpTuples) →
      (∀ g, ψ (φ g) = g) → (∀ g, φ (ψ g) = g) →
      ((S.mpTuples).filter fun g => (φ g).1 ∈ S.resViolated f).card =
        ((S.mpTuples).filter fun g => g.1 ∈ S.resViolated f).card := by
    intro φ ψ hφ hψ hli hri
    refine Finset.card_nbij' φ ψ ?_ ?_ (fun g _ => hli g) (fun g _ => hri g)
    · intro g hg
      obtain ⟨hgM, hgv⟩ := mem_filter.mp hg
      exact mem_filter.mpr ⟨hφ g hgM, hgv⟩
    · intro g hg
      obtain ⟨hgM, hgv⟩ := mem_filter.mp hg
      exact mem_filter.mpr ⟨hψ g hgM, by rwa [hri]⟩
  have h1_mem : ∀ g ∈ S.mpTuples, φ1 g ∈ S.mpTuples := fun _ hg => hg
  have h2_mem : ∀ g ∈ S.mpTuples, φ2 g ∈ S.mpTuples := by
    intro g hg
    obtain ⟨h1, h2, hr2, hux, hvy, hc2, huy, hvx⟩ := mem_mpTuples.mp hg
    refine mem_mpTuples.mpr ⟨h2, h1, ?_, hres_swap hux, hres_swap hvy, hres_swap hc2,
      by rw [symp_comm]; exact hvx, by rw [symp_comm]; exact huy⟩
    simpa [φ2, add_comm] using hr2
  have h3_mem : ∀ g ∈ S.mpTuples, φ3 g ∈ S.mpTuples := by
    intro g hg
    obtain ⟨h1, h2, hr2, hux, hvy, hc2, huy, hvx⟩ := mem_mpTuples.mp hg
    have hx : symp g.2.1 g.2.2 = 0 := (mem_q7pFlags.mp (mem_resFlags.mp h2).1).2.2.2
    refine mem_mpTuples.mpr ⟨hr2, h2, ?_, hres_rot hux, hres_rot hvy, ?_, ?_, ?_⟩
    · simpa [φ3, add_assoc, pt_add_self, add_zero] using h1
    · have heq : g.1.1 + g.2.1 + (g.1.2 + g.2.2) = (g.1.1 + g.1.2) + (g.2.1 + g.2.2) := by abel
      dsimp only [φ3]; rw [heq]; exact hres_rot hc2
    · dsimp only [φ3]; rw [ExactDegreesN4N5.symp_add_left, huy, hx, add_zero]
    · dsimp only [φ3]; rw [ExactDegreesN4N5.symp_add_left, hvx, symp_comm g.2.2 g.2.1, hx, add_zero]
  have h4_mem : ∀ g ∈ S.mpTuples, φ4 g ∈ S.mpTuples := by
    intro g hg
    obtain ⟨h1, h2, hr2, hux, hvy, hc2, huy, hvx⟩ := mem_mpTuples.mp hg
    exact mem_mpTuples.mpr ⟨hux, hvy, hc2, h1, h2, hr2, huy, by rw [symp_comm]; exact hvx⟩
  have h5_mem : ∀ g ∈ S.mpTuples, φ5 g ∈ S.mpTuples := by
    intro g hg
    obtain ⟨h1, h2, hr2, hux, hvy, hc2, huy, hvx⟩ := mem_mpTuples.mp hg
    refine mem_mpTuples.mpr ⟨hvy, hux, ?_, hres_swap h1, hres_swap h2, ?_, hvx,
      by rw [symp_comm]; exact huy⟩
    · simpa [φ5, add_comm] using hc2
    · simpa [φ5, add_comm] using hres_swap hr2
  have h5i_mem : ∀ g ∈ S.mpTuples, φ5i g ∈ S.mpTuples := by
    intro g hg
    obtain ⟨h1, h2, hr2, hux, hvy, hc2, huy, hvx⟩ := mem_mpTuples.mp hg
    refine mem_mpTuples.mpr ⟨hres_swap hux, hres_swap hvy, ?_, h2, h1, ?_, by rw [symp_comm]; exact hvx, huy⟩
    · simpa [φ5i, add_comm] using hres_swap hc2
    · simpa [φ5i, add_comm] using hr2
  have h6_mem : ∀ g ∈ S.mpTuples, φ6 g ∈ S.mpTuples := by
    intro g hg
    obtain ⟨h1, h2, hr2, hux, hvy, hc2, huy, hvx⟩ := mem_mpTuples.mp hg
    have hvys : symp g.1.2 g.2.2 = 0 := (mem_q7pFlags.mp (mem_resFlags.mp hvy).1).2.2.2
    refine mem_mpTuples.mpr ⟨hc2, hvy, ?_, hres_rot h1, hres_rot h2, ?_, ?_, ?_⟩
    · dsimp only [φ6]
      have heq1 : g.1.1 + g.1.2 + g.1.2 = g.1.1 := by rw [add_assoc, pt_add_self, add_zero]
      have heq2 : g.2.1 + g.2.2 + g.2.2 = g.2.1 := by rw [add_assoc, pt_add_self, add_zero]
      rw [heq1, heq2]; exact hux
    · dsimp only [φ6]
      have heq : g.1.1 + g.1.2 + (g.2.1 + g.2.2) = (g.1.1 + g.2.1) + (g.1.2 + g.2.2) := by abel
      rw [heq]; exact hres_rot hr2
    · dsimp only [φ6]; rw [ExactDegreesN4N5.symp_add_left, huy, hvys, add_zero]
    · dsimp only [φ6]; rw [ExactDegreesN4N5.symp_add_left, symp_comm g.2.1 g.1.2, hvx, symp_comm g.2.2 g.1.2, hvys, add_zero]
  have h6i_mem : ∀ g ∈ S.mpTuples, φ6i g ∈ S.mpTuples := by
    intro g hg
    obtain ⟨h1, h2, hr2, hux, hvy, hc2, huy, hvx⟩ := mem_mpTuples.mp hg
    have h2s : symp g.2.1 g.2.2 = 0 := (mem_q7pFlags.mp (mem_resFlags.mp h2).1).2.2.2
    refine mem_mpTuples.mpr ⟨hres_rot hux, hres_rot hvy, ?_, ?_, h2, ?_, ?_, ?_⟩
    · dsimp only [φ6i]
      have heq : (g.1.1 + g.2.1) + (g.1.2 + g.2.2) = (g.1.1 + g.1.2) + (g.2.1 + g.2.2) := by abel
      rw [heq]; exact hres_rot hc2
    · exact hr2
    · dsimp only [φ6i]
      have heq1 : g.1.1 + g.2.1 + g.2.1 = g.1.1 := by rw [add_assoc, pt_add_self, add_zero]
      have heq2 : g.1.2 + g.2.2 + g.2.2 = g.1.2 := by rw [add_assoc, pt_add_self, add_zero]
      rw [heq1, heq2]; exact h1
    · dsimp only [φ6i]; rw [ExactDegreesN4N5.symp_add_left, huy, h2s, add_zero]
    · dsimp only [φ6i]; rw [symp_add_right, symp_comm g.2.1 g.1.2, hvx, h2s, add_zero]
  have hsum_all : (S.mpTuples).card = 48 * (S.resFlags).card := by
    have hfib : (S.mpTuples).card = ∑ p ∈ S.resFlags, ((S.mpTuples).filter fun g => g.1 = p).card := by
      rw [← Finset.card_biUnion]
      · congr 1; ext g; simp only [mem_biUnion, mem_filter]
        constructor
        · intro hg; exact ⟨g.1, (mem_mpTuples.mp hg).1, hg, rfl⟩
        · rintro ⟨_, _, hg, _⟩; exact hg
      · intro p1 _ p2 _ hne; change Disjoint _ _; rw [Finset.disjoint_left]; intro g h1 h2
        exact hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)
    rw [hfib, Finset.sum_congr rfl fun p hp => S.card_mpTuples_fiber hp, Finset.sum_const, smul_eq_mul,
      Nat.mul_comm]
  have hsum_viol : ((S.mpTuples).filter fun g => g.1 ∈ S.resViolated f).card =
      48 * (S.resViolated f).card := by
    have hfib : ((S.mpTuples).filter fun g => g.1 ∈ S.resViolated f).card =
        ∑ p ∈ S.resViolated f, ((S.mpTuples).filter fun g => g.1 = p).card := by
      rw [← Finset.card_biUnion]
      · congr 1; ext g; simp only [mem_biUnion, mem_filter]
        constructor
        · rintro ⟨hg, hgv⟩; exact ⟨g.1, hgv, hg, rfl⟩
        · rintro ⟨p, hp, hg, rfl⟩; exact ⟨hg, hp⟩
      · intro p1 _ p2 _ hne; change Disjoint _ _; rw [Finset.disjoint_left]; intro g h1 h2
        exact hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)
    rw [hfib]
    have hterm : ∀ p ∈ S.resViolated f,
        ((S.mpTuples).filter fun g => g.1 = p).card = 48 := fun p hp => by
      have := S.card_mpTuples_fiber (mem_resViolated.mp hp).1
      convert this
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hcov : ∀ g ∈ S.mpTuples,
      (φ1 g).1 ∈ S.resViolated f ∨ (φ2 g).1 ∈ S.resViolated f ∨ (φ3 g).1 ∈ S.resViolated f ∨
      (φ4 g).1 ∈ S.resViolated f ∨ (φ5 g).1 ∈ S.resViolated f ∨ (φ6 g).1 ∈ S.resViolated f := by
    intro g hg
    obtain ⟨h1, h2, hr2, hux, hvy, hc2, huy, hvx⟩ := mem_mpTuples.mp hg
    obtain ⟨huR, hvR, huvR, huv⟩ := mem_q7pFlags.mp (mem_resFlags.mp h1).1
    obtain ⟨hxR, hyR, hxyR, hxy⟩ := mem_q7pFlags.mp (mem_resFlags.mp h2).1
    obtain ⟨huxR, hvyR, huvxyR, _⟩ := mem_q7pFlags.mp (mem_resFlags.mp hr2).1
    have huvxyR' : g.1.1 + g.1.2 + (g.2.1 + g.2.2) ∈ realPoints 4 := by
      have : g.1.1 + g.1.2 + (g.2.1 + g.2.2) = (g.1.1 + g.2.1) + (g.1.2 + g.2.2) := by abel
      rwa [this]
    have huxs : symp g.1.1 g.2.1 = 0 := (mem_q7pFlags.mp (mem_resFlags.mp hux).1).2.2.2
    have hvys : symp g.1.2 g.2.2 = 0 := (mem_q7pFlags.mp (mem_resFlags.mp hvy).1).2.2.2
    have hmp := mermin_peres_4tuple_violated huv hxy huxs hvys huy hvx f
      (hf _ huR) (hf _ hvR) (hf _ huvR) (hf _ hxR) (hf _ hyR) (hf _ hxyR)
      (hf _ huxR) (hf _ hvyR) (hf _ huvxyR')
    rcases hmp with h | h | h | h | h | h
    · exact Or.inl (mem_resViolated.mpr ⟨h1, h⟩)
    · exact Or.inr (Or.inl (mem_resViolated.mpr ⟨h2, h⟩))
    · exact Or.inr (Or.inr (Or.inl (mem_resViolated.mpr ⟨hr2, h⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (mem_resViolated.mpr ⟨hux, h⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (mem_resViolated.mpr ⟨hvy, h⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (mem_resViolated.mpr ⟨hc2, h⟩)))))
  have hle : (S.mpTuples).card ≤ 6 * ((S.mpTuples).filter fun g => g.1 ∈ S.resViolated f).card := by
    set V := fun (φ : ((Pt 4 × Pt 4) × (Pt 4 × Pt 4)) → ((Pt 4 × Pt 4) × (Pt 4 × Pt 4))) =>
      (S.mpTuples).filter fun g => (φ g).1 ∈ S.resViolated f
    have hsub : S.mpTuples ⊆ V φ1 ∪ (V φ2 ∪ (V φ3 ∪ (V φ4 ∪ (V φ5 ∪ V φ6)))) := by
      intro g hg
      rcases hcov g hg with h | h | h | h | h | h
      · exact mem_union_left _ (mem_filter.mpr ⟨hg, h⟩)
      · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hg, h⟩))
      · exact mem_union_right _ (mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hg, h⟩)))
      · exact mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hg, h⟩))))
      · exact mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hg, h⟩)))))
      · exact mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hg, h⟩)))))
    have h1 := Finset.card_le_card hsub
    have h2 : (V φ1 ∪ (V φ2 ∪ (V φ3 ∪ (V φ4 ∪ (V φ5 ∪ V φ6))))).card ≤
        (V φ1).card + (V φ2).card + (V φ3).card + (V φ4).card + (V φ5).card + (V φ6).card := by
      have u1 := Finset.card_union_le (V φ1) (V φ2 ∪ (V φ3 ∪ (V φ4 ∪ (V φ5 ∪ V φ6))))
      have u2 := Finset.card_union_le (V φ2) (V φ3 ∪ (V φ4 ∪ (V φ5 ∪ V φ6)))
      have u3 := Finset.card_union_le (V φ3) (V φ4 ∪ (V φ5 ∪ V φ6))
      have u4 := Finset.card_union_le (V φ4) (V φ5 ∪ V φ6)
      have u5 := Finset.card_union_le (V φ5) (V φ6)
      omega
    have c1 := hcard_bij φ1 φ1 h1_mem h1_mem (fun _ => rfl) (fun _ => rfl)
    have c2 := hcard_bij φ2 φ2 h2_mem h2_mem (fun g => by cases g; rfl) (fun g => by cases g; rfl)
    have c3 := hcard_bij φ3 φ3 h3_mem h3_mem
      (fun g => by rcases g with ⟨⟨u, v⟩, ⟨x, y⟩⟩; simp only [φ3, add_assoc, pt_add_self, add_zero])
      (fun g => by rcases g with ⟨⟨u, v⟩, ⟨x, y⟩⟩; simp only [φ3, add_assoc, pt_add_self, add_zero])
    have c4 := hcard_bij φ4 φ4 h4_mem h4_mem
      (fun g => by rcases g with ⟨⟨u, v⟩, ⟨x, y⟩⟩; rfl)
      (fun g => by rcases g with ⟨⟨u, v⟩, ⟨x, y⟩⟩; rfl)
    have c5 := hcard_bij φ5 φ5i h5_mem h5i_mem
      (fun g => by rcases g with ⟨⟨u, v⟩, ⟨x, y⟩⟩; rfl)
      (fun g => by rcases g with ⟨⟨u, v⟩, ⟨x, y⟩⟩; rfl)
    have c6 := hcard_bij φ6 φ6i h6_mem h6i_mem
      (fun g => by rcases g with ⟨⟨u, v⟩, ⟨x, y⟩⟩; simp only [φ6, φ6i, add_assoc, pt_add_self, add_zero])
      (fun g => by rcases g with ⟨⟨u, v⟩, ⟨x, y⟩⟩; simp only [φ6, φ6i, add_assoc, pt_add_self, add_zero])
    change (V φ1).card = _ at c1; change (V φ2).card = _ at c2; change (V φ3).card = _ at c3
    change (V φ4).card = _ at c4; change (V φ5).card = _ at c5; change (V φ6).card = _ at c6
    omega
  rw [hsum_all, hsum_viol, S.card_resFlags] at hle
  have h6 := S.card_resViolated_le_six f
  omega

end SolidSpread

/-! ### Part 3. Theorem 23(b) — Universal `d(Q⁺(7,2) \ Q(6,2)) ≥ 252` via Kramers + PSD Trace -/

open Classical in
/-- Residual flags of `Q⁺(7,2) \ Q(6,2)` for an off-quadric pole `w` (`qform w = 1`):
flags of `Q⁺(7,2)` NOT contained in `w⊥`. -/
noncomputable def q62ResFlags (w : Pt 4) : Finset (Pt 4 × Pt 4) :=
  q7pFlags.filter fun p => ¬ (symp w p.1 = 0 ∧ symp w p.2 = 0)

open Classical in
/-- Residual flags of `Q⁺(7,2) \ Q(6,2)` violated by the sign assignment `f`. -/
noncomputable def q62ResViolated (w : Pt 4) (f : Pt 4 → ℝ) : Finset (Pt 4 × Pt 4) :=
  (q62ResFlags w).filter fun p => f p.1 * f p.2 * f (p.1 + p.2) ≠ lineSign p.1 p.2

open Classical in
/-- Distinct violated residual contexts (lines) of `Q⁺(7,2) \ Q(6,2)` under `f`. -/
noncomputable def q62ResViolatedLines (w : Pt 4) (f : Pt 4 → ℝ) : Finset (Finset (Pt 4)) :=
  (q62ResViolated w f).image lineOf

open Classical in
lemma mem_q62ResFlags {w : Pt 4} {p : Pt 4 × Pt 4} :
    p ∈ q62ResFlags w ↔ p ∈ q7pFlags ∧ ¬ (symp w p.1 = 0 ∧ symp w p.2 = 0) :=
  by simp only [q62ResFlags, mem_filter]

open Classical in
lemma mem_q62ResViolated {w : Pt 4} {f : Pt 4 → ℝ} {p : Pt 4 × Pt 4} :
    p ∈ q62ResViolated w f ↔ p ∈ q62ResFlags w ∧ f p.1 * f p.2 * f (p.1 + p.2) ≠ lineSign p.1 p.2 :=
  by simp only [q62ResViolated, mem_filter]

/-- If a `16 × 16` Hermitian matrix `A` has `tr A = 0`, `tr(A²) = 1008`, and every eigenvalue has
even multiplicity, then every eigenvalue satisfies `λ ≤ 21`. -/
private lemma eigenvalue_le_21_of_even_mult {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (hcard : Fintype.card n = 16)
    (heven : ∀ r : ℝ, Even (univ.filter fun i : n => hA.eigenvalues i = r).card)
    (h1 : A.trace = 0) (h2 : (A ^ 2).trace = 1008) (i₀ : n) :
    hA.eigenvalues i₀ ≤ 21 := by
  have e1 : ∑ i : n, hA.eigenvalues i = 0 := by
    have h := hA.trace_eq_sum_eigenvalues
    rw [h1] at h
    exact RCLike.ofReal_eq_zero.mp (by exact_mod_cast h.symm)
  have e2 : ∑ i : n, hA.eigenvalues i ^ 2 = 1008 := by
    have h := trace_pow_eq_sum_eigenvalues_pow hA 2
    rw [h2] at h
    exact_mod_cast h.symm
  set lam := hA.eigenvalues i₀
  have hge2 : 2 ≤ (univ.filter fun i : n => hA.eigenvalues i = lam).card := by
    have hpos : 0 < (univ.filter fun i : n => hA.eigenvalues i = lam).card :=
      Finset.card_pos.mpr ⟨i₀, mem_filter.mpr ⟨mem_univ i₀, rfl⟩⟩
    obtain ⟨k, hk⟩ := heven lam
    omega
  have hex : ∃ i₁ : n, i₁ ≠ i₀ ∧ hA.eigenvalues i₁ = lam := by
    have hi0_mem : i₀ ∈ univ.filter fun i : n => hA.eigenvalues i = lam :=
      mem_filter.mpr ⟨mem_univ i₀, rfl⟩
    have hne : ((univ.filter fun i : n => hA.eigenvalues i = lam).erase i₀).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have hcard1 : ((univ.filter fun i : n => hA.eigenvalues i = lam).erase i₀).card = 0 := by
        rw [hempty, Finset.card_empty]
      rw [Finset.card_erase_of_mem hi0_mem] at hcard1
      omega
    obtain ⟨i₁, hi₁⟩ := hne
    exact ⟨i₁, (mem_erase.mp hi₁).1, (mem_filter.mp (mem_erase.mp hi₁).2).2⟩
  obtain ⟨i₁, hne, hi₁⟩ := hex
  set R : Finset n := (univ.erase i₀).erase i₁
  have hRcard : R.card = 14 := by
    rw [Finset.card_erase_of_mem (mem_erase.mpr ⟨hne, mem_univ i₁⟩),
      Finset.card_erase_of_mem (mem_univ i₀), Finset.card_univ, hcard]
  have hR1 : ∑ i ∈ R, hA.eigenvalues i = -(2 * lam) := by
    have h := Finset.add_sum_erase univ hA.eigenvalues (mem_univ i₀)
    have h' := Finset.add_sum_erase (univ.erase i₀) hA.eigenvalues (mem_erase.mpr ⟨hne, mem_univ i₁⟩)
    rw [← h', hi₁] at h
    change lam + (lam + ∑ i ∈ R, hA.eigenvalues i) = ∑ i : n, hA.eigenvalues i at h
    linarith
  have hR2 : ∑ i ∈ R, hA.eigenvalues i ^ 2 = 1008 - 2 * lam ^ 2 := by
    have h := Finset.add_sum_erase univ (fun i => hA.eigenvalues i ^ 2) (mem_univ i₀)
    have h' := Finset.add_sum_erase (univ.erase i₀) (fun i => hA.eigenvalues i ^ 2)
      (mem_erase.mpr ⟨hne, mem_univ i₁⟩)
    rw [← h', hi₁] at h
    change lam ^ 2 + (lam ^ 2 + ∑ i ∈ R, hA.eigenvalues i ^ 2) = ∑ i : n, hA.eigenvalues i ^ 2 at h
    linarith
  have hcs := sq_sum_le_card_mul_sum_sq (s := R) (f := hA.eigenvalues)
  rw [hRcard, hR1, hR2] at hcs
  push_cast at hcs
  nlinarith

/-- PSD trace inequality: if `A, T` are Hermitian and every eigenvalue of `A` is `≤ c`,
then `Re tr(A T²) ≤ c · Re tr(T²)`. -/
private lemma trace_mul_sq_le_of_eigenvalues_le {n : Type*} [Fintype n] [DecidableEq n]
    {A T : Matrix n n ℂ} (hA : A.IsHermitian) (hT : T.IsHermitian) (c : ℝ)
    (hle : ∀ i : n, hA.eigenvalues i ≤ c) :
    ((A * T ^ 2).trace).re ≤ c * ((T ^ 2).trace).re := by
  let U : Matrix n n ℂ := hA.eigenvectorUnitary
  have hU : U * Uᴴ = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  have hspec : A = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * Uᴴ := hA.spectral_theorem
  set B : Matrix n n ℂ := Uᴴ * T * U
  have hBh : B.IsHermitian := by
    unfold Matrix.IsHermitian B
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hT.eq, Matrix.mul_assoc]
  have htr_T2 : (T ^ 2).trace = (B ^ 2).trace := by
    rw [pow_two, pow_two]
    dsimp [B]
    calc (T * T).trace
        = (T * 1 * T).trace := by rw [mul_one]
      _ = (T * (U * Uᴴ) * T).trace := by rw [hU]
      _ = (U * Uᴴ * T * (U * Uᴴ) * T).trace := by rw [hU, one_mul]
      _ = (Uᴴ * T * (U * Uᴴ) * T * U).trace := by
            have := Matrix.trace_mul_comm U (Uᴴ * T * (U * Uᴴ) * T)
            simpa only [Matrix.mul_assoc] using this
      _ = (Uᴴ * T * U * (Uᴴ * T * U)).trace := by simp only [Matrix.mul_assoc]
  have htr_AT2 : (A * T ^ 2).trace = (diagonal (RCLike.ofReal ∘ hA.eigenvalues) * B ^ 2).trace := by
    conv_lhs => rw [hspec]
    rw [pow_two, pow_two]
    dsimp [B]
    calc (U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * Uᴴ * (T * T)).trace
        = (diagonal (RCLike.ofReal ∘ hA.eigenvalues) * Uᴴ * (T * T) * U).trace := by
            have := Matrix.trace_mul_comm U (diagonal (RCLike.ofReal ∘ hA.eigenvalues) * Uᴴ * (T * T))
            simpa only [Matrix.mul_assoc] using this
      _ = (diagonal (RCLike.ofReal ∘ hA.eigenvalues) * Uᴴ * (T * (U * Uᴴ) * T) * U).trace := by
            rw [hU, mul_one]
      _ = (diagonal (RCLike.ofReal ∘ hA.eigenvalues) * (Uᴴ * T * U * (Uᴴ * T * U))).trace := by
            simp only [Matrix.mul_assoc]
  rw [htr_AT2, htr_T2]
  have hB2_diag : ∀ i : n, ((B ^ 2) i i).re = ∑ j : n, ((B j i).re ^ 2 + (B j i).im ^ 2) := by
    intro i
    rw [pow_two, Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hij : B i j = star (B j i) := by
      simpa [Matrix.conjTranspose_apply] using (congrFun (congrFun hBh.eq i) j).symm
    rw [hij]
    simp [Complex.mul_re]; ring
  have hB2_nonneg : ∀ i : n, 0 ≤ ((B ^ 2) i i).re := fun i => by
    rw [hB2_diag i]; exact Finset.sum_nonneg fun j _ => by positivity
  have hlhs : ((diagonal (RCLike.ofReal ∘ hA.eigenvalues) * B ^ 2).trace).re =
      ∑ i : n, hA.eigenvalues i * ((B ^ 2) i i).re := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul,
      Function.comp_apply, RCLike.ofReal_eq_complex_ofReal, Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hrhs : ((B ^ 2).trace).re = ∑ i : n, ((B ^ 2) i i).re := by
    simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum]
  rw [hlhs, hrhs, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hle i) (hB2_nonneg i)

/-- **Theorem 23(b) — Universal Lower Bound (`d(Q⁺(7,2) \ Q(6,2)) ≥ 252`):**
For EVERY off-quadric pole `w : Pt 4` (`qform w = 1`, all 120 copies of `Q(6,2)` in `Q⁺(7,2)`)
and EVERY `±1` assignment `f`, at least `252` of the `1,260` residual contexts are violated. -/
theorem q62_residual_ge_252 (w : Pt 4) (hw : qform w = 1) (f : Pt 4 → ℝ)
    (hf : ∀ u ∈ realPoints 4, f u = 1 ∨ f u = -1) :
    252 ≤ (q62ResViolatedLines w f).card := by
  set H : Finset (Pt 4) := (realPoints 4).filter fun u => symp w u = 0
  set O : Finset (Pt 4) := (realPoints 4).filter fun u => symp w u = 1
  -- Exact counts: `|H| = 63`, `|O| = 72`.
  have hHcard : H.card = 63 := by
    -- `H` has exact count via `(1 + eps(q u))(1 + eps(symp w u)) / 4` minus `{0}`.
    have h0 : (0 : Pt 4) ∈ univ.filter fun u : Pt 4 => qform u = 0 ∧ symp w u = 0 := by
      simp [qform_zero, symp_zero_right]
    have hHeq : H = (univ.filter fun u : Pt 4 => qform u = 0 ∧ symp w u = 0).erase 0 := by
      ext u; simp [H, realPoints, and_assoc, and_comm, and_left_comm]
    have htot : 4 * (univ.filter fun u : Pt 4 => qform u = 0 ∧ symp w u = 0).card = 256 := by
      have hw0 : w ≠ 0 := fun h => absurd (h ▸ hw) (by rw [qform_zero]; decide)
      have hind : ∀ u : Pt 4, (if qform u = 0 ∧ symp w u = 0 then (1 : ℂ) else 0) =
          (1 + eps (qform u) + eps (symp w u) + eps (qform u + symp w u)) / 4 := by
        intro u
        have h1 : (if qform u = 0 ∧ symp w u = 0 then (1 : ℂ) else 0) =
            (if qform u = 0 then (1 : ℂ) else 0) * (if symp w u = 0 then (1 : ℂ) else 0) := by
          by_cases c1 : qform u = 0 <;> by_cases c2 : symp w u = 0 <;> simp [c1, c2]
        rw [h1, indicator_eq, indicator_eq, eps_add]; ring
      have hC : (((univ.filter fun u : Pt 4 => qform u = 0 ∧ symp w u = 0).card : ℕ) : ℂ) = 64 := by
        rw [Finset.card_filter]; push_cast
        simp_rw [hind, ← Finset.sum_div, Finset.sum_add_distrib, sum_eps_qform, sum_eps_symp hw0,
          sum_eps_qform_add_symp, hw, eps_one, neg_one_mul, Finset.sum_const, Finset.card_univ,
          card_pt, nsmul_eq_mul, mul_one]
        norm_num
      have h2 : ((4 * (univ.filter fun u : Pt 4 => qform u = 0 ∧ symp w u = 0).card : ℕ) : ℂ) = 256 := by
        push_cast; rw [hC]; norm_num
      exact_mod_cast h2
    rw [hHeq, Finset.card_erase_of_mem h0]; omega
  have hOcard : O.card = 72 := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := realPoints 4) (fun u => symp w u = 0)
    have hOeq : (realPoints 4).filter (fun u => ¬ symp w u = 0) = O := by
      ext u; simp only [O, mem_filter]
      refine and_congr_right fun _ => ?_
      rcases zmod2_cases (symp w u) with h | h <;> simp [h]
    have hR : (realPoints 4).card = 135 := by have := card_realPoints (N := 4); norm_num at this; omega
    rw [hOeq, hR] at hsplit
    change H.card + O.card = 135 at hsplit
    omega
  -- `A = opA H f` commutes with antiunitary `J K` (`J = pauli w`), so all eigenvalues have even mult ≤ 21.
  set A := opA H f
  set T := opA O f
  have hAh : A.IsHermitian := opA_isHermitian H f
  have hTh : T.IsHermitian := opA_isHermitian O f
  set J : Matrix (Vec 4) (Vec 4) ℂ := pauli w
  have hJu : Jᴴ * J = 1 := by rw [(pauli_isHermitian w).eq, pauli_mul_self]
  have hJ2 : J * J.map star = -1 := by
    rw [pauli_map_star, hw, eps_one, Matrix.mul_smul, pauli_mul_self, neg_one_smul]
  have hJA : J * A.map star = A * J := by
    unfold A opA
    have hmap : (∑ u ∈ H, ((f u : ℝ) : ℂ) • pauli u).map star =
        ∑ u ∈ H, ((f u : ℝ) : ℂ) • (pauli u).map star := by
      ext x y; simp [Matrix.map_apply, Matrix.sum_apply, Complex.conj_ofReal]
    rw [hmap, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hqu : qform u = 0 := (mem_filter.mp (mem_filter.mp hu).1).2.2
    have hsw : symp w u = 0 := (mem_filter.mp hu).2
    rw [Matrix.mul_smul, Matrix.smul_mul, pauli_map_star, hqu, eps_zero, one_smul,
      pauli_comm u w, symp_comm u w, hsw, eps_zero, one_smul]
  have heven := kramers_even_mult hAh hJu hJ2 hJA
  have hA1 : A.trace = 0 := trace_opA H f (by simp [H, realPoints])
  have hA2 : (A ^ 2).trace = 1008 := by
    rw [trace_opA_sq H f (fun u hu => hf u (mem_filter.mp hu).1), hHcard]; norm_num
  have heig21 : ∀ i : Vec 4, hAh.eigenvalues i ≤ 21 := fun i =>
    eigenvalue_le_21_of_even_mult hAh (by rw [card_vec]; norm_num) heven hA1 hA2 i
  have hpsd := trace_mul_sq_le_of_eigenvalues_le hAh hTh 21 heig21
  have hT2 : ((T ^ 2).trace).re = 1152 := by
    rw [trace_opA_sq O f (fun u hu => hf u (mem_filter.mp hu).1), hOcard, Complex.ofReal_re]; norm_num
  -- Expand `tr(A T²) = 16 · (|Oflags| - 2 · |Oviol|)` where `Oflags` = residual flags with both endpoints in `O`.
  classical
  set OF : Finset (Pt 4 × Pt 4) := q7pFlags.filter fun p => symp w p.1 = 1 ∧ symp w p.2 = 1
  set OV : Finset (Pt 4 × Pt 4) := OF.filter fun p => f p.1 * f p.2 * f (p.1 + p.2) ≠ lineSign p.1 p.2
  -- Exact count `3 * |OF| = |q62ResFlags w|` and `3 * |OV| = |q62ResViolated w f|`.
  have hOF_card : 3 * OF.card = (q62ResFlags w).card := by
    set C11 := (q62ResFlags w).filter fun p => symp w p.1 = 1 ∧ symp w p.2 = 1
    set C01 := (q62ResFlags w).filter fun p => symp w p.1 = 0 ∧ symp w p.2 = 1
    set C10 := (q62ResFlags w).filter fun p => symp w p.1 = 1 ∧ symp w p.2 = 0
    have hC11 : C11 = OF := by
      ext p; simp only [C11, OF, mem_filter, mem_q62ResFlags]
      constructor
      · rintro ⟨⟨hp, _⟩, h1, h2⟩; exact ⟨hp, h1, h2⟩
      · rintro ⟨hp, h1, h2⟩; exact ⟨⟨hp, fun h => absurd (h.1.symm.trans h1) (by decide)⟩, h1, h2⟩
    have hpart : q62ResFlags w = C11 ∪ (C01 ∪ C10) := by
      ext p; simp only [C11, C01, C10, mem_union, mem_filter, mem_q62ResFlags]
      constructor
      · rintro ⟨hp, hnot⟩
        rcases zmod2_cases (symp w p.1) with h1 | h1 <;> rcases zmod2_cases (symp w p.2) with h2 | h2
        · exact (hnot ⟨h1, h2⟩).elim
        · exact Or.inr (Or.inl ⟨⟨hp, hnot⟩, h1, h2⟩)
        · exact Or.inr (Or.inr ⟨⟨hp, hnot⟩, h1, h2⟩)
        · exact Or.inl ⟨⟨hp, hnot⟩, h1, h2⟩
      · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    have hd1 : Disjoint C11 (C01 ∪ C10) := by
      rw [Finset.disjoint_left]; intro p h1 h2
      rcases mem_union.mp h2 with h | h
      · exact absurd ((mem_filter.mp h).2.1.symm.trans (mem_filter.mp h1).2.1) (by decide)
      · exact absurd ((mem_filter.mp h).2.2.symm.trans (mem_filter.mp h1).2.2) (by decide)
    have hd2 : Disjoint C01 C10 := by
      rw [Finset.disjoint_left]; intro p h1 h2
      exact absurd ((mem_filter.mp h1).2.1.symm.trans (mem_filter.mp h2).2.1) (by decide)
    have hrot1 : C11.card = C10.card := by
      refine Finset.card_bij (fun p _ => (p.2, p.1 + p.2)) ?_ ?_ ?_
      · intro p hp
        obtain ⟨hpR, h1, h2⟩ := mem_filter.mp hp
        obtain ⟨hpF, _⟩ := mem_q62ResFlags.mp hpR
        obtain ⟨a1, a2, a3, hs⟩ := mem_q7pFlags.mp hpF
        have h3 : symp w (p.1 + p.2) = 0 := by rw [symp_add_right, h1, h2]; decide
        have hF' : (p.2, p.1 + p.2) ∈ q7pFlags := mem_q7pFlags.mpr ⟨a2, a3,
          by rwa [add_comm p.1 p.2, ← add_assoc, pt_add_self, zero_add],
          by rw [symp_add_right, symp_self, add_zero, symp_comm, hs]⟩
        exact mem_filter.mpr ⟨mem_q62ResFlags.mpr ⟨hF', fun h => absurd (h.1.symm.trans h2) (by decide)⟩, h2, h3⟩
      · intro p _ q _ h
        have h2 : p.2 = q.2 := congrArg Prod.fst h
        have h12 : p.1 + p.2 = q.1 + q.2 := congrArg Prod.snd h
        rw [h2] at h12; exact Prod.ext (add_right_cancel h12) h2
      · intro r hr
        obtain ⟨hrR, h1, h2⟩ := mem_filter.mp hr
        obtain ⟨hrF, _⟩ := mem_q62ResFlags.mp hrR
        obtain ⟨a1, a2, a3, hs⟩ := mem_q7pFlags.mp hrF
        have h3 : symp w (r.1 + r.2) = 1 := by rw [symp_add_right, h1, h2]; decide
        refine ⟨(r.1 + r.2, r.1), ?_, Prod.ext rfl (by rw [add_comm r.1 r.2, add_assoc, pt_add_self, add_zero])⟩
        have hF' : (r.1 + r.2, r.1) ∈ q7pFlags := mem_q7pFlags.mpr ⟨a3, a1,
          by rwa [add_comm r.1 r.2, add_assoc, pt_add_self, add_zero],
          by rw [symp_comm, symp_add_right, symp_self, zero_add, hs]⟩
        exact mem_filter.mpr ⟨mem_q62ResFlags.mpr ⟨hF', fun h => absurd (h.1.symm.trans h3) (by decide)⟩, h3, h1⟩
    have hrot2 : C10.card = C01.card := by
      refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
      · intro p hp
        obtain ⟨hpR, h1, h2⟩ := mem_filter.mp hp
        obtain ⟨hpF, _⟩ := mem_q62ResFlags.mp hpR
        obtain ⟨a1, a2, a3, hs⟩ := mem_q7pFlags.mp hpF
        have hF' : (p.2, p.1) ∈ q7pFlags :=
          mem_q7pFlags.mpr ⟨a2, a1, by rwa [add_comm], by rwa [symp_comm]⟩
        exact mem_filter.mpr ⟨mem_q62ResFlags.mpr ⟨hF', fun h => absurd (h.2.symm.trans h1) (by decide)⟩, h2, h1⟩
      · intro p _ q _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
      · intro r hr
        obtain ⟨hrR, h1, h2⟩ := mem_filter.mp hr
        obtain ⟨hrF, _⟩ := mem_q62ResFlags.mp hrR
        obtain ⟨a1, a2, a3, hs⟩ := mem_q7pFlags.mp hrF
        refine ⟨(r.2, r.1), ?_, rfl⟩
        have hF' : (r.2, r.1) ∈ q7pFlags :=
          mem_q7pFlags.mpr ⟨a2, a1, by rwa [add_comm], by rwa [symp_comm]⟩
        exact mem_filter.mpr ⟨mem_q62ResFlags.mpr ⟨hF', fun h => absurd (h.1.symm.trans h2) (by decide)⟩, h2, h1⟩
    rw [hpart, Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2,
      ← hrot2, ← hrot1, hC11]
    ring
  have hOV_card : 3 * OV.card = (q62ResViolated w f).card := by
    set C11 := (q62ResViolated w f).filter fun p => symp w p.1 = 1 ∧ symp w p.2 = 1
    set C01 := (q62ResViolated w f).filter fun p => symp w p.1 = 0 ∧ symp w p.2 = 1
    set C10 := (q62ResViolated w f).filter fun p => symp w p.1 = 1 ∧ symp w p.2 = 0
    have hC11 : C11 = OV := by
      ext p; simp only [C11, OV, OF, mem_filter, mem_q62ResViolated, mem_q62ResFlags]
      constructor
      · rintro ⟨⟨⟨hp, _⟩, hbad⟩, h1, h2⟩; exact ⟨⟨hp, h1, h2⟩, hbad⟩
      · rintro ⟨⟨hp, h1, h2⟩, hbad⟩
        exact ⟨⟨⟨hp, fun h => absurd (h.1.symm.trans h1) (by decide)⟩, hbad⟩, h1, h2⟩
    have hpart : q62ResViolated w f = C11 ∪ (C01 ∪ C10) := by
      ext p; simp only [C11, C01, C10, mem_union, mem_filter, mem_q62ResViolated, mem_q62ResFlags]
      constructor
      · rintro ⟨⟨hp, hnot⟩, hbad⟩
        rcases zmod2_cases (symp w p.1) with h1 | h1 <;> rcases zmod2_cases (symp w p.2) with h2 | h2
        · exact (hnot ⟨h1, h2⟩).elim
        · exact Or.inr (Or.inl ⟨⟨⟨hp, hnot⟩, hbad⟩, h1, h2⟩)
        · exact Or.inr (Or.inr ⟨⟨⟨hp, hnot⟩, hbad⟩, h1, h2⟩)
        · exact Or.inl ⟨⟨⟨hp, hnot⟩, hbad⟩, h1, h2⟩
      · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    have hd1 : Disjoint C11 (C01 ∪ C10) := by
      rw [Finset.disjoint_left]; intro p h1 h2
      rcases mem_union.mp h2 with h | h
      · exact absurd ((mem_filter.mp h).2.1.symm.trans (mem_filter.mp h1).2.1) (by decide)
      · exact absurd ((mem_filter.mp h).2.2.symm.trans (mem_filter.mp h1).2.2) (by decide)
    have hd2 : Disjoint C01 C10 := by
      rw [Finset.disjoint_left]; intro p h1 h2
      exact absurd ((mem_filter.mp h1).2.1.symm.trans (mem_filter.mp h2).2.1) (by decide)
    have hrot_viol : ∀ {p : Pt 4 × Pt 4}, p ∈ q7pFlags →
        f p.1 * f p.2 * f (p.1 + p.2) ≠ lineSign p.1 p.2 →
        (p.2, p.1 + p.2) ∈ q7pFlags ∧
          f p.2 * f (p.1 + p.2) * f (p.2 + (p.1 + p.2)) ≠ lineSign p.2 (p.1 + p.2) := by
      intro p hpF hbad
      obtain ⟨a1, a2, a3, hs⟩ := mem_q7pFlags.mp hpF
      have hrotF : (p.2, p.1 + p.2) ∈ q7pFlags := mem_q7pFlags.mpr ⟨a2, a3,
        by rwa [add_comm p.1 p.2, ← add_assoc, pt_add_self, zero_add],
        by rw [symp_add_right, symp_self, add_zero, symp_comm, hs]⟩
      refine ⟨hrotF, ?_⟩
      have hls : lineSign p.2 (p.1 + p.2) = lineSign p.1 p.2 := by
        have hC : tau p.2 (p.1 + p.2) = tau p.1 p.2 := by
          have hmul : pauli p.2 * pauli (p.1 + p.2) = tau p.2 (p.1 + p.2) • pauli p.1 := by
            rw [pauli_mul, add_comm p.1 p.2, ← add_assoc, pt_add_self, zero_add]
          have hmul2 : pauli p.2 * pauli (p.1 + p.2) = tau p.1 p.2 • pauli p.1 := by
            have hcp := context_product (u := p.1) (v := p.2)
            have hsq : pauli p.1 * (pauli p.1 * pauli p.2 * pauli (p.1 + p.2)) =
                pauli p.1 * (tau p.1 p.2 • (1 : Matrix (Vec 4) (Vec 4) ℂ)) := congrArg (pauli p.1 * ·) hcp
            simp only [Matrix.mul_smul, Matrix.mul_one] at hsq
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, pauli_mul_self, Matrix.one_mul] at hsq
            exact hsq
          have htr := congrArg (fun M => (M * pauli p.1).trace) (hmul.symm.trans hmul2)
          simp only [Matrix.smul_mul, Matrix.trace_smul, trace_pauli_mul, ↓reduceIte, smul_eq_mul] at htr
          exact mul_right_cancel₀ (pow_ne_zero 4 (by norm_num)) htr
        simpa [lineSign] using congrArg Complex.re hC
      rw [hls, show p.2 + (p.1 + p.2) = p.1 by rw [add_comm p.1 p.2, ← add_assoc, pt_add_self, zero_add]]
      intro heq; apply hbad; linarith [show f p.1 * f p.2 * f (p.1 + p.2) = f p.2 * f (p.1 + p.2) * f p.1 by ring]
    have hswap_viol : ∀ {p : Pt 4 × Pt 4}, p ∈ q7pFlags →
        f p.1 * f p.2 * f (p.1 + p.2) ≠ lineSign p.1 p.2 →
        (p.2, p.1) ∈ q7pFlags ∧ f p.2 * f p.1 * f (p.2 + p.1) ≠ lineSign p.2 p.1 := by
      intro p hpF hbad
      obtain ⟨a1, a2, a3, hs⟩ := mem_q7pFlags.mp hpF
      refine ⟨mem_q7pFlags.mpr ⟨a2, a1, by rwa [add_comm], by rwa [symp_comm]⟩, ?_⟩
      have hls : lineSign p.2 p.1 = lineSign p.1 p.2 := by
        simp only [lineSign, tau_swap p.1 p.2, hs, eps_zero, one_mul]
      rw [hls, add_comm p.2 p.1, mul_comm (f p.2) (f p.1)]
      exact hbad
    have hrot1 : C11.card = C10.card := by
      refine Finset.card_bij (fun p _ => (p.2, p.1 + p.2)) ?_ ?_ ?_
      · intro p hp
        obtain ⟨hpV, h1, h2⟩ := mem_filter.mp hp
        obtain ⟨hpR, hbad⟩ := mem_q62ResViolated.mp hpV
        obtain ⟨hrotF, hrotB⟩ := hrot_viol (mem_q62ResFlags.mp hpR).1 hbad
        have h3 : symp w (p.1 + p.2) = 0 := by rw [symp_add_right, h1, h2]; decide
        exact mem_filter.mpr ⟨mem_q62ResViolated.mpr ⟨mem_q62ResFlags.mpr ⟨hrotF,
          fun h => absurd (h.1.symm.trans h2) (by decide)⟩, hrotB⟩, h2, h3⟩
      · intro p _ q _ h
        have h2 : p.2 = q.2 := congrArg Prod.fst h
        have h12 : p.1 + p.2 = q.1 + q.2 := congrArg Prod.snd h
        rw [h2] at h12; exact Prod.ext (add_right_cancel h12) h2
      · intro r hr
        obtain ⟨hrV, h1, h2⟩ := mem_filter.mp hr
        obtain ⟨hrR, hbad⟩ := mem_q62ResViolated.mp hrV
        obtain ⟨h1F, h1B⟩ := hrot_viol (mem_q62ResFlags.mp hrR).1 hbad
        obtain ⟨h2F, h2B⟩ := hrot_viol h1F h1B
        have hsimp : r.2 + (r.1 + r.2) = r.1 := by rw [add_comm r.1 r.2, ← add_assoc, pt_add_self, zero_add]
        rw [hsimp] at h2F h2B
        have h3 : symp w (r.1 + r.2) = 1 := by rw [symp_add_right, h1, h2]; decide
        refine ⟨(r.1 + r.2, r.1), ?_, Prod.ext rfl (by rw [add_comm r.1 r.2, add_assoc, pt_add_self, add_zero])⟩
        exact mem_filter.mpr ⟨mem_q62ResViolated.mpr ⟨mem_q62ResFlags.mpr ⟨h2F,
          fun h => absurd (h.1.symm.trans h3) (by decide)⟩, h2B⟩, h3, h1⟩
    have hrot2 : C10.card = C01.card := by
      refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
      · intro p hp
        obtain ⟨hpV, h1, h2⟩ := mem_filter.mp hp
        obtain ⟨hpR, hbad⟩ := mem_q62ResViolated.mp hpV
        obtain ⟨hswF, hswB⟩ := hswap_viol (mem_q62ResFlags.mp hpR).1 hbad
        exact mem_filter.mpr ⟨mem_q62ResViolated.mpr ⟨mem_q62ResFlags.mpr ⟨hswF,
          fun h => absurd (h.2.symm.trans h1) (by decide)⟩, hswB⟩, h2, h1⟩
      · intro p _ q _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
      · intro r hr
        obtain ⟨hrV, h1, h2⟩ := mem_filter.mp hr
        obtain ⟨hrR, hbad⟩ := mem_q62ResViolated.mp hrV
        obtain ⟨hswF, hswB⟩ := hswap_viol (mem_q62ResFlags.mp hrR).1 hbad
        refine ⟨(r.2, r.1), ?_, rfl⟩
        exact mem_filter.mpr ⟨mem_q62ResViolated.mpr ⟨mem_q62ResFlags.mpr ⟨hswF,
          fun h => absurd (h.1.symm.trans h2) (by decide)⟩, hswB⟩, h2, h1⟩
    rw [hpart, Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2,
      ← hrot2, ← hrot1, hC11]
    ring
  -- Exact count `|flags H| = 1890`, so `|q62ResFlags w| = 9450 - 1890 = 7560`, hence `|OF| = 2520`!
  have hHF : (flags H).card = 1890 := by
    have h4 : 4 * (flags H).card = 4 * 1890 := by
      -- For every `u ∈ H`, `u` has 30 neighbors in `H` (from `card_flags_all` on `W(5,2)` or character sum!).
      -- Directly count `#{v ∈ H : u + v ∈ H ∧ symp u v = 0} = 30` for every `u ∈ H`!
      rw [card_flags, Finset.mul_sum]
      have hdeg : ∀ u ∈ H, 4 * (H.filter fun v => u + v ∈ H ∧ symp u v = 0).card = 120 := by
        intro u hu
        have huR := (mem_filter.mp hu).1
        obtain ⟨hu0, hqu⟩ := (mem_filter.mp huR).2
        have hswu : symp w u = 0 := (mem_filter.mp hu).2
        have hwu_ne : w + u ≠ 0 := fun h => by
          have : qform (w + u) = 0 := by rw [h, qform_zero]
          rw [qform_add, hw, hqu, hswu] at this; exact absurd this (by decide)
        have hqwu : qform (w + u) = 1 := by rw [qform_add, hw, hqu, hswu]; simp
        have hw0 : w ≠ 0 := fun h => absurd (h ▸ hw) (by rw [qform_zero]; decide)
        have hfilt : H.filter (fun v => u + v ∈ H ∧ symp u v = 0) =
            ((univ.filter fun v : Pt 4 => qform v = 0 ∧ symp w v = 0 ∧ symp u v = 0).erase 0).erase u := by
          ext v
          simp only [H, realPoints, mem_filter, mem_erase, mem_univ, true_and]
          constructor
          · rintro ⟨⟨⟨hv0, hqv⟩, hswv⟩, ⟨⟨huv0, _⟩, _⟩, hsuv⟩
            exact ⟨fun h => huv0 (by rw [h, pt_add_self]), hv0, hqv, hswv, hsuv⟩
          · rintro ⟨hvu, hv0, hqv, hswv, hsuv⟩
            refine ⟨⟨⟨hv0, hqv⟩, hswv⟩, ⟨⟨fun h => hvu (pt_eq_of_add_eq_zero h).symm, ?_⟩, ?_⟩, hsuv⟩
            · rw [qform_add, hqu, hqv, hsuv]; simp
            · rw [symp_add_right, hswu, hswv, add_zero]
        have h8 : 8 * (univ.filter fun v : Pt 4 => qform v = 0 ∧ symp w v = 0 ∧ symp u v = 0).card = 256 := by
          have hind : ∀ v : Pt 4, (if qform v = 0 ∧ symp w v = 0 ∧ symp u v = 0 then (1 : ℂ) else 0) =
              ((1 + eps (qform v)) * (1 + eps (symp w v)) * (1 + eps (symp u v))) / 8 := by
            intro v
            have hmul : (if qform v = 0 ∧ symp w v = 0 ∧ symp u v = 0 then (1 : ℂ) else 0) =
                (if qform v = 0 then (1 : ℂ) else 0) * (if symp w v = 0 then (1 : ℂ) else 0) *
                (if symp u v = 0 then (1 : ℂ) else 0) := by
              by_cases c1 : qform v = 0 <;> by_cases c2 : symp w v = 0 <;>
                by_cases c3 : symp u v = 0 <;> simp [c1, c2, c3]
            rw [hmul, indicator_eq, indicator_eq, indicator_eq]; ring
          have hC : (((univ.filter fun v : Pt 4 => qform v = 0 ∧ symp w v = 0 ∧ symp u v = 0).card : ℕ) : ℂ) = 32 := by
            rw [Finset.card_filter]; push_cast
            simp_rw [hind, ← Finset.sum_div]
            have hexp : ∀ v : Pt 4,
                (1 + eps (qform v)) * (1 + eps (symp w v)) * (1 + eps (symp u v)) =
                1 + eps (symp w v) + eps (symp u v) + eps (symp (w + u) v) +
                  eps (qform v) + eps (qform v + symp w v) + eps (qform v + symp u v) +
                  eps (qform v + symp (w + u) v) := by
              intro v; simp only [ExactDegreesN4N5.symp_add_left, eps_add]; ring
            simp_rw [hexp, Finset.sum_add_distrib, sum_eps_symp hw0, sum_eps_symp hu0,
              sum_eps_symp hwu_ne, sum_eps_qform, sum_eps_qform_add_symp, hw, hqu, hqwu,
              eps_zero, eps_one, Finset.sum_const, Finset.card_univ, card_pt, nsmul_eq_mul, mul_one]
            norm_num
          have h2 : ((8 * (univ.filter fun v : Pt 4 => qform v = 0 ∧ symp w v = 0 ∧ symp u v = 0).card : ℕ) : ℂ) = 256 := by
            push_cast; rw [hC]; norm_num
          exact_mod_cast h2
        rw [hfilt]
        have h0in : (0 : Pt 4) ∈ univ.filter fun v : Pt 4 => qform v = 0 ∧ symp w v = 0 ∧ symp u v = 0 := by
          simp [qform_zero, symp_zero_right]
        have huin : u ∈ (univ.filter fun v : Pt 4 => qform v = 0 ∧ symp w v = 0 ∧ symp u v = 0).erase 0 :=
          mem_erase.mpr ⟨hu0, mem_filter.mpr ⟨mem_univ _, hqu, hswu, symp_self u⟩⟩
        rw [Finset.card_erase_of_mem huin, Finset.card_erase_of_mem h0in]
        omega
      rw [Finset.sum_congr rfl hdeg, Finset.sum_const, hHcard]; norm_num
    omega
  have hOF_2520 : OF.card = 2520 := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := q7pFlags)
      (fun p => symp w p.1 = 0 ∧ symp w p.2 = 0)
    have hHeq : q7pFlags.filter (fun p => symp w p.1 = 0 ∧ symp w p.2 = 0) = flags H := by
      ext p; simp only [H, mem_filter, mem_q7pFlags, mem_flags]
      constructor
      · rintro ⟨⟨h1, h2, h3, hs⟩, s1, s2⟩
        exact ⟨⟨h1, s1⟩, ⟨h2, s2⟩, ⟨h3, by rw [symp_add_right, s1, s2, add_zero]⟩, hs⟩
      · rintro ⟨⟨h1, s1⟩, ⟨h2, s2⟩, ⟨h3, _⟩, hs⟩
        exact ⟨⟨h1, h2, h3, hs⟩, s1, s2⟩
    have hres_eq : q7pFlags.filter (fun p => ¬ (symp w p.1 = 0 ∧ symp w p.2 = 0)) =
        q62ResFlags w := by
      ext p; simp only [mem_q62ResFlags, mem_filter]
    rw [hHeq, hres_eq, hHF, card_q7pFlags] at hsplit
    omega
  -- Expand `((A * T^2).trace).re = 16 * (OF.card - 2 * OV.card)`.
  have htr_AT2 : ((A * T ^ 2).trace).re = 16 * ((OF.card : ℝ) - 2 * (OV.card : ℝ)) := by
    set G : Pt 4 × Pt 4 → ℂ := fun p =>
      ((f p.1 : ℝ) : ℂ) * ((f p.2 : ℝ) : ℂ) * ((f (p.1 + p.2) : ℝ) : ℂ) * tau p.1 p.2
    have hstep1 : (A * T ^ 2).trace =
        (2 : ℂ) ^ 4 * ∑ p ∈ (O ×ˢ O).filter (fun p => p.1 + p.2 ∈ H), G p := by
      rw [pow_two, Matrix.trace_mul_comm A (T * T), opA_mul_opA, Finset.sum_mul, Matrix.trace_sum,
        Finset.mul_sum]
      conv_rhs => rw [Finset.sum_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_mul, Matrix.trace_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Matrix.smul_mul, Matrix.trace_smul, trace_pauli_mul_opA, smul_eq_mul]
      by_cases hmem : u + v ∈ H
      · simp only [hmem, ↓reduceIte, G]; ring
      · simp [hmem]
    have hstep2 : ∑ p ∈ ((O ×ˢ O).filter (fun p => p.1 + p.2 ∈ H)).filter
        (fun p => ¬ symp p.1 p.2 = 0), G p = 0 := by
      refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
      · intro p hp
        have hs : symp p.1 p.2 = 1 := (zmod2_cases _).resolve_left (mem_filter.mp hp).2
        simp only [G]; rw [tau_swap p.1 p.2, hs, eps_one, add_comm p.2 p.1]; ring
      · intro p hp _ hfix
        have h21 : p.2 = p.1 := congrArg Prod.fst hfix
        apply (mem_filter.mp hp).2; rw [h21]; exact symp_self _
      · intro p hp
        rcases mem_filter.mp hp with ⟨hp1, hs⟩
        rcases mem_filter.mp hp1 with ⟨hp2, hsum⟩
        rcases mem_product.mp hp2 with ⟨h1, h2⟩
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨h2, h1⟩,
          by simpa [add_comm] using hsum⟩, by simpa [symp_comm] using hs⟩
      · intro p _; rfl
    have hfilt : ((O ×ˢ O).filter (fun p => p.1 + p.2 ∈ H)).filter (fun p => symp p.1 p.2 = 0) = OF := by
      ext p
      simp only [OF, O, H, mem_filter, mem_product, mem_q7pFlags]
      constructor
      · rintro ⟨⟨⟨⟨h1, s1⟩, ⟨h2, s2⟩⟩, h3, _⟩, hs⟩; exact ⟨⟨h1, h2, h3, hs⟩, s1, s2⟩
      · rintro ⟨⟨h1, h2, h3, hs⟩, s1, s2⟩
        exact ⟨⟨⟨⟨h1, s1⟩, ⟨h2, s2⟩⟩, h3, by rw [symp_add_right, s1, s2]; decide⟩, hs⟩
    rw [hstep1, ← Finset.sum_filter_add_sum_filter_not _ (fun p : Pt 4 × Pt 4 => symp p.1 p.2 = 0),
      hstep2, add_zero, hfilt]
    have hsum_real : ∑ p ∈ OF, G p = (((OF.card : ℝ) - 2 * (OV.card : ℝ) : ℝ) : ℂ) := by
      have hterm : ∀ p ∈ OF, G p =
          ((if f p.1 * f p.2 * f (p.1 + p.2) ≠ lineSign p.1 p.2 then (-1 : ℝ) else 1 : ℝ) : ℂ) := by
        intro p hp
        have hpF := (mem_filter.mp hp).1
        obtain ⟨h1, h2, h3, hs⟩ := mem_q7pFlags.mp hpF
        simp only [G, tau_eq_lineSign hs]
        rcases hf p.1 h1 with h1' | h1' <;> rcases hf p.2 h2 with h2' | h2' <;>
          rcases hf (p.1 + p.2) h3 with h3' | h3' <;>
          rcases lineSign_eq_one_or_neg_one hs with hl | hl <;>
          (simp [h1', h2', h3', hl]; try norm_num)
      rw [Finset.sum_congr rfl hterm, ← Complex.ofReal_sum]
      congr 1
      rw [Finset.sum_ite]; simp only [Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one]
      have hv : OF.filter (fun p => f p.1 * f p.2 * f (p.1 + p.2) ≠ lineSign p.1 p.2) = OV := rfl
      have hsp := Finset.card_filter_add_card_filter_not (s := OF)
        (fun p => f p.1 * f p.2 * f (p.1 + p.2) ≠ lineSign p.1 p.2)
      rw [hv] at hsp ⊢
      have hspR : (OV.card : ℝ) +
          ((OF.filter fun p => ¬ f p.1 * f p.2 * f (p.1 + p.2) ≠ lineSign p.1 p.2).card : ℝ) =
          (OF.card : ℝ) := by exact_mod_cast hsp
      linarith
    rw [hsum_real]
    have hC : (2 : ℂ) ^ 4 * (((OF.card : ℝ) - 2 * (OV.card : ℝ) : ℝ) : ℂ) =
        (((16 * ((OF.card : ℝ) - 2 * (OV.card : ℝ)) : ℝ) : ℂ)) := by push_cast; ring
    rw [hC, Complex.ofReal_re]
  rw [htr_AT2, hT2, hOF_2520] at hpsd
  have hOV_ge : (504 : ℝ) ≤ (OV.card : ℝ) := by push_cast at hpsd; linarith
  have hOV_nat : 504 ≤ OV.card := by exact_mod_cast hOV_ge
  have h6 : (q62ResViolated w f).card ≤ 6 * (q62ResViolatedLines w f).card := by
    have h0 : (0 : Pt 4) ∉ realPoints 4 := by simp [realPoints]
    refine Finset.card_le_mul_card_image (q62ResViolated w f) 6 ?_
    intro L hL
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hL
    have hsub : ((q62ResViolated w f).filter fun p => lineOf p = lineOf q) ⊆ (lineOf q).offDiag := by
      intro p hp
      obtain ⟨hpv, hpl⟩ := mem_filter.mp hp
      have hpf : p ∈ q7pFlags := (mem_q62ResFlags.mp (mem_q62ResViolated.mp hpv).1).1
      obtain ⟨_, _, h3, _⟩ := mem_q7pFlags.mp hpf
      have hne : p.1 ≠ p.2 := fun h => h0 (by rwa [h, pt_add_self] at h3)
      rw [mem_offDiag, ← hpl]; exact ⟨by simp [lineOf], by simp [lineOf], hne⟩
    calc ((q62ResViolated w f).filter fun p => lineOf p = lineOf q).card
        ≤ (lineOf q).offDiag.card := Finset.card_le_card hsub
      _ = (lineOf q).card * (lineOf q).card - (lineOf q).card := Finset.offDiag_card _
      _ ≤ 6 := by
          have h3 : (lineOf q).card ≤ 3 := by
            unfold lineOf
            exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ (by simp))))
          set k := (lineOf q).card; interval_cases k <;> norm_num
  omega

/-! ### Part 4. Theorem 23(a*) — Multiplicity-4 Kramers on Embedded `Q⁻(5,2)` & Ovoid Residual `252` -/

/-- The embedded `Q⁻(5,2)` section `Q⁺(7,2) ∩ u⊥ ∩ v⊥` of an anisotropic 2-plane `(u, v)`. -/
def anisoSection (u v : Pt 4) : Finset (Pt 4) :=
  (realPoints 4).filter fun z => symp u z = 0 ∧ symp v z = 0

/-- **Multiplicity-4 Kramers theorem:** if a Hermitian matrix `A` on `Vec 4` (`16×16`) is real
(`A.map star = A`) and commutes with two anticommuting imaginary Paulis `P_u, P_v`, then every
eigenvalue of `A` has multiplicity divisible by `4`. -/
private lemma four_dvd_eig_mult_of_aniso {u v : Pt 4}
    (hu : qform u = 1) (hv : qform v = 1) (huv : symp u v = 1)
    {A : Matrix (Vec 4) (Vec 4) ℂ} (hA : A.IsHermitian)
    (hAreal : A.map star = A)
    (hAu : pauli u * A = A * pauli u) (hAv : pauli v * A = A * pauli v)
    (r : ℝ) : 4 ∣ (univ.filter fun i : Vec 4 => hA.eigenvalues i = r).card := by
  classical
  set E : Submodule ℂ (EuclideanSpace ℂ (Vec 4)) :=
    LinearMap.ker (Matrix.toEuclideanLin A - (r : ℂ) • LinearMap.id)
  have hmemE : ∀ x : EuclideanSpace ℂ (Vec 4), x ∈ E ↔ A *ᵥ x.ofLp = (r : ℂ) • x.ofLp := by
    intro x
    simp only [E, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero, Matrix.toLpLin_apply]
    exact ⟨fun h => congrArg WithLp.ofLp h, fun h => WithLp.ofLp_injective _ h⟩
  set Ep : Submodule ℂ (EuclideanSpace ℂ (Vec 4)) :=
    E ⊓ LinearMap.ker (Matrix.toEuclideanLin (pauli u) - LinearMap.id)
  set Em : Submodule ℂ (EuclideanSpace ℂ (Vec 4)) :=
    E ⊓ LinearMap.ker (Matrix.toEuclideanLin (pauli u) + LinearMap.id)
  have hmemEp : ∀ x : EuclideanSpace ℂ (Vec 4), x ∈ Ep ↔ x ∈ E ∧ pauli u *ᵥ x.ofLp = x.ofLp := by
    intro x
    simp only [Ep, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero, Matrix.toLpLin_apply]
    exact and_congr_right fun _ => ⟨fun h => congrArg WithLp.ofLp h, fun h => WithLp.ofLp_injective _ h⟩
  have hmemEm : ∀ x : EuclideanSpace ℂ (Vec 4), x ∈ Em ↔ x ∈ E ∧ pauli u *ᵥ x.ofLp = -x.ofLp := by
    intro x
    simp only [Em, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply,
      add_eq_zero_iff_eq_neg, Matrix.toLpLin_apply]
    exact and_congr_right fun _ => ⟨fun h => congrArg WithLp.ofLp h, fun h => WithLp.ofLp_injective _ h⟩
  -- `Ep ⊔ Em = E` and `Disjoint Ep Em`.
  have hdisj : Disjoint Ep Em := by
    rw [Submodule.disjoint_def]
    intro x h1 h2
    have hp := (hmemEp x).mp h1 |>.2
    have hm := (hmemEm x).mp h2 |>.2
    have h2x : (2 : ℂ) • x.ofLp = 0 := by
      ext i
      have hpi := congrFun hp i
      have hmi := congrFun hm i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Pi.neg_apply] at hmi ⊢
      linear_combination hmi - hpi
    apply WithLp.ofLp_injective
    ext i
    have hi := congrFun h2x i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
    exact (mul_eq_zero.mp hi).resolve_left (by norm_num)
  have hsup : Ep ⊔ Em = E := by
    apply le_antisymm (sup_le inf_le_left inf_le_left)
    intro x hx
    let xp : EuclideanSpace ℂ (Vec 4) := WithLp.toLp 2 ((1 / 2 : ℂ) • (x.ofLp + pauli u *ᵥ x.ofLp))
    let xm : EuclideanSpace ℂ (Vec 4) := WithLp.toLp 2 ((1 / 2 : ℂ) • (x.ofLp - pauli u *ᵥ x.ofLp))
    have hAx := (hmemE x).mp hx
    have hPu2 : pauli u *ᵥ (pauli u *ᵥ x.ofLp) = x.ofLp := by
      rw [mulVec_mulVec, pauli_mul_self, one_mulVec]
    have hAPux : A *ᵥ (pauli u *ᵥ x.ofLp) = (r : ℂ) • (pauli u *ᵥ x.ofLp) := by
      rw [mulVec_mulVec, ← hAu, ← mulVec_mulVec, hAx, mulVec_smul]
    have hxp : xp ∈ Ep := by
      rw [hmemEp, hmemE]
      refine ⟨?_, ?_⟩
      · dsimp [xp]; rw [mulVec_smul, mulVec_add, hAx, hAPux]
        ext i; simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]; ring
      · dsimp [xp]; rw [mulVec_smul, mulVec_add, hPu2, add_comm]
    have hxm : xm ∈ Em := by
      rw [hmemEm, hmemE]
      refine ⟨?_, ?_⟩
      · dsimp [xm]; rw [mulVec_smul, mulVec_sub, hAx, hAPux]
        ext i; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Complex.real_smul]; ring
      · dsimp [xm]; rw [mulVec_smul, mulVec_sub, hPu2, ← smul_neg, neg_sub]
    have hsum : x = xp + xm := by
      apply WithLp.ofLp_injective; ext i
      simp only [xp, xm, WithLp.ofLp_add, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    rw [hsum]
    exact Submodule.add_mem_sup hxp hxm
  -- `P_v` gives a linear isomorphism `Ep ≃ₗ[ℂ] Em`, so `finrank E = 2 * finrank Ep`.
  have hanti : pauli u * pauli v = -(pauli v * pauli u) := by
    rw [pauli_comm v u, symp_comm v u, huv, eps_one, neg_one_smul]
  have hdim_eq : Module.finrank ℂ Ep = Module.finrank ℂ Em := by
    let f_pm : Ep →ₗ[ℂ] Em :=
      { toFun := fun x => ⟨Matrix.toEuclideanLin (pauli v) x.1, by
          obtain ⟨hxE, hxu⟩ := (hmemEp x.1).mp x.2
          rw [hmemEm, hmemE]
          refine ⟨?_, ?_⟩
          · change A *ᵥ (pauli v *ᵥ x.1.ofLp) = (r : ℂ) • (pauli v *ᵥ x.1.ofLp)
            rw [mulVec_mulVec, ← hAv, ← mulVec_mulVec, (hmemE x.1).mp hxE, mulVec_smul]
          · change pauli u *ᵥ (pauli v *ᵥ x.1.ofLp) = -(pauli v *ᵥ x.1.ofLp)
            rw [mulVec_mulVec, hanti, neg_mulVec, ← mulVec_mulVec, hxu]⟩
        map_add' := fun x y => Subtype.ext (map_add _ x.1 y.1)
        map_smul' := fun c x => Subtype.ext (map_smul _ c x.1) }
    let f_mp : Em →ₗ[ℂ] Ep :=
      { toFun := fun x => ⟨Matrix.toEuclideanLin (pauli v) x.1, by
          obtain ⟨hxE, hxu⟩ := (hmemEm x.1).mp x.2
          rw [hmemEp, hmemE]
          refine ⟨?_, ?_⟩
          · change A *ᵥ (pauli v *ᵥ x.1.ofLp) = (r : ℂ) • (pauli v *ᵥ x.1.ofLp)
            rw [mulVec_mulVec, ← hAv, ← mulVec_mulVec, (hmemE x.1).mp hxE, mulVec_smul]
          · change pauli u *ᵥ (pauli v *ᵥ x.1.ofLp) = pauli v *ᵥ x.1.ofLp
            rw [mulVec_mulVec, hanti, neg_mulVec, ← mulVec_mulVec, hxu, mulVec_neg, neg_neg]⟩
        map_add' := fun x y => Subtype.ext (map_add _ x.1 y.1)
        map_smul' := fun c x => Subtype.ext (map_smul _ c x.1) }
    exact LinearEquiv.finrank_eq (LinearEquiv.ofLinearMap f_pm f_mp
      (by ext x; change (pauli v *ᵥ (pauli v *ᵥ x.1.ofLp)) _ = x.1.ofLp _; rw [mulVec_mulVec, pauli_mul_self, one_mulVec])
      (by ext x; change (pauli v *ᵥ (pauli v *ᵥ x.1.ofLp)) _ = x.1.ofLp _; rw [mulVec_mulVec, pauli_mul_self, one_mulVec]))
  -- `Ep` is invariant under antiunitary `θ = P_v K` (`θ² = -I`), so `Even (finrank ℂ Ep)`!
  have hJu : (pauli v)ᴴ * pauli v = 1 := by rw [(pauli_isHermitian v).eq, pauli_mul_self]
  have hJ2 : pauli v * (pauli v).map star = -1 := by
    rw [pauli_map_star, hv, eps_one, Matrix.mul_smul, pauli_mul_self, neg_one_smul]
  have hEp_inv : ∀ x ∈ Ep, antiunitary (pauli v) x ∈ Ep := by
    intro x hx
    obtain ⟨hxE, hxu⟩ := (hmemEp x).mp hx
    rw [hmemEp, hmemE]
    have hstarM : ∀ (M : Matrix (Vec 4) (Vec 4) ℂ) (w : Vec 4 → ℂ),
        star (M *ᵥ w) = (M.map star) *ᵥ star w := by
      intro M w; ext i
      simp only [Pi.star_apply, mulVec, dotProduct, Matrix.map_apply, star_sum, star_mul']
    refine ⟨?_, ?_⟩
    · change A *ᵥ (pauli v *ᵥ star x.ofLp) = (r : ℂ) • (pauli v *ᵥ star x.ofLp)
      have hstarR : star ((r : ℂ) • x.ofLp) = (r : ℂ) • star x.ofLp := by
        ext i; simp
      calc A *ᵥ (pauli v *ᵥ star x.ofLp)
          = (A * pauli v) *ᵥ star x.ofLp := by rw [mulVec_mulVec]
        _ = (pauli v * A.map star) *ᵥ star x.ofLp := by rw [hAreal, hAv]
        _ = pauli v *ᵥ star (A *ᵥ x.ofLp) := by rw [← mulVec_mulVec, ← hstarM]
        _ = (r : ℂ) • (pauli v *ᵥ star x.ofLp) := by rw [(hmemE x).mp hxE, hstarR, mulVec_smul]
    · change pauli u *ᵥ (pauli v *ᵥ star x.ofLp) = pauli v *ᵥ star x.ofLp
      have hPustar : (pauli u).map star = -pauli u := by rw [pauli_map_star, hu, eps_one, neg_one_smul]
      calc pauli u *ᵥ (pauli v *ᵥ star x.ofLp)
          = (pauli u * pauli v) *ᵥ star x.ofLp := by rw [mulVec_mulVec]
        _ = (-(pauli v * pauli u)) *ᵥ star x.ofLp := by rw [hanti]
        _ = pauli v *ᵥ ((-(pauli u)) *ᵥ star x.ofLp) := by
              rw [neg_mulVec, ← mulVec_mulVec, neg_mulVec, mulVec_neg]
        _ = pauli v *ᵥ ((pauli u).map star *ᵥ star x.ofLp) := by rw [hPustar]
        _ = pauli v *ᵥ star (pauli u *ᵥ x.ofLp) := by rw [← hstarM]
        _ = pauli v *ᵥ star x.ofLp := by rw [hxu]
  have heven_p : Even (Module.finrank ℂ Ep) :=
    even_finrank_of_antiunitary_neg_one (pauli v) hJu hJ2 _ Ep rfl hEp_inv
  -- Connect `finrank ℂ E` to `(univ.filter fun i => hA.eigenvalues i = r).card`.
  set S : Finset (Vec 4) := univ.filter fun i : Vec 4 => hA.eigenvalues i = r
  have hEeq : E = Submodule.span ℂ (Set.range fun i : S => hA.eigenvectorBasis i.1) := by
    apply le_antisymm
    · intro x hx
      rw [hmemE] at hx
      have hrepr := hA.eigenvectorBasis.sum_repr' x
      have hcoeff : ∀ i : Vec 4, hA.eigenvectorBasis.repr x i ≠ 0 → hA.eigenvalues i = r := by
        intro i hne
        have h1 : ⟪hA.eigenvectorBasis i, Matrix.toEuclideanLin A x⟫_ℂ =
            (r : ℂ) * ⟪hA.eigenvectorBasis i, x⟫_ℂ := by
          have hAx' : Matrix.toEuclideanLin A x = (r : ℂ) • x := WithLp.ofLp_injective _ hx
          rw [hAx', inner_smul_right]
        have h2 : ⟪hA.eigenvectorBasis i, Matrix.toEuclideanLin A x⟫_ℂ =
            (hA.eigenvalues i : ℂ) * ⟪hA.eigenvectorBasis i, x⟫_ℂ := by
          rw [← (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) (hA.eigenvectorBasis i) x]
          have hbi : Matrix.toEuclideanLin A (hA.eigenvectorBasis i) =
              (hA.eigenvalues i : ℂ) • hA.eigenvectorBasis i :=
            WithLp.ofLp_injective _ (by simpa [RCLike.real_smul_eq_coe_smul] using hA.mulVec_eigenvectorBasis i)
          rw [hbi, inner_smul_left]; simp
        have hinner : ⟪hA.eigenvectorBasis i, x⟫_ℂ = hA.eigenvectorBasis.repr x i := by
          simpa using (hA.eigenvectorBasis.repr_apply_apply x i).symm
        rw [h2, hinner] at h1
        have heqC : ((hA.eigenvalues i : ℂ) - (r : ℂ)) * hA.eigenvectorBasis.repr x i = 0 := by
          linear_combination h1
        exact Complex.ofReal_injective (sub_eq_zero.mp ((mul_eq_zero.mp heqC).resolve_right hne))
      rw [← hrepr]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [← hA.eigenvectorBasis.repr_apply_apply x i]
      by_cases hc : hA.eigenvectorBasis.repr x i = 0
      · rw [hc, zero_smul]; exact Submodule.zero_mem _
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, mem_filter.mpr ⟨mem_univ _, hcoeff i hc⟩⟩, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨⟨i, hiS⟩, rfl⟩
      rw [SetLike.mem_coe, hmemE]
      have hir : hA.eigenvalues i = r := (mem_filter.mp hiS).2
      simpa [hir, RCLike.real_smul_eq_coe_smul] using hA.mulVec_eigenvectorBasis i
  have hli : LinearIndependent ℂ (fun i : S => hA.eigenvectorBasis i.1) :=
    hA.eigenvectorBasis.toBasis.linearIndependent.comp (fun i : S => i.1) Subtype.val_injective
  have hdimE : Module.finrank ℂ E = S.card := by
    rw [hEeq, finrank_span_eq_card hli, Fintype.card_coe]
  have hadd := Submodule.finrank_sup_add_finrank_inf_eq Ep Em
  rw [hsup, hdisj.eq_bot, finrank_bot, add_zero, ← hdim_eq, hdimE] at hadd
  obtain ⟨k, hk⟩ := heven_p
  exact ⟨k, by omega⟩

/-- **Embedded `Q⁻(5,2)` bound (`9` violated contexts):** for every anisotropic 2-plane `(u, v)`
(`qform u = qform v = 1`, `symp u v = 1`), the 27-point section `anisoSection u v` violates
at least `9` of its `45` contexts under every `±1` assignment. -/
theorem aniso_plane_q5minus_ge_9 {u v : Pt 4}
    (hu : qform u = 1) (hv : qform v = 1) (huv : symp u v = 1)
    (f : Pt 4 → ℝ) (hf : ∀ z ∈ anisoSection u v, f z = 1 ∨ f z = -1) :
    9 ≤ (violatedLines (anisoSection u v) f).card := by
  classical
  set S := anisoSection u v
  have h0 : (0 : Pt 4) ∉ S := by simp [S, anisoSection, realPoints]
  have hu0 : u ≠ 0 := fun h => absurd (h ▸ hu) (by rw [qform_zero]; decide)
  have hv0 : v ≠ 0 := fun h => absurd (h ▸ hv) (by rw [qform_zero]; decide)
  have huv_q : qform (u + v) = 1 := by rw [qform_add, hu, hv, huv]; decide
  have huv0 : u + v ≠ 0 := fun h => absurd (h ▸ huv_q) (by rw [qform_zero]; decide)
  -- Character-sum count `|S| = 27`.
  have hScard : S.card = 27 := by
    have h0in : (0 : Pt 4) ∈ univ.filter fun z : Pt 4 => qform z = 0 ∧ symp u z = 0 ∧ symp v z = 0 := by
      simp [qform_zero, symp_zero_right]
    have hSeq : S = (univ.filter fun z : Pt 4 => qform z = 0 ∧ symp u z = 0 ∧ symp v z = 0).erase 0 := by
      ext z; simp [S, anisoSection, realPoints, and_assoc, and_comm, and_left_comm]
    have h8 : 8 * (univ.filter fun z : Pt 4 => qform z = 0 ∧ symp u z = 0 ∧ symp v z = 0).card = 224 := by
      have hind : ∀ z : Pt 4, (if qform z = 0 ∧ symp u z = 0 ∧ symp v z = 0 then (1 : ℂ) else 0) =
          ((1 + eps (qform z)) * (1 + eps (symp u z)) * (1 + eps (symp v z))) / 8 := by
        intro z
        have hmul : (if qform z = 0 ∧ symp u z = 0 ∧ symp v z = 0 then (1 : ℂ) else 0) =
            (if qform z = 0 then (1 : ℂ) else 0) * (if symp u z = 0 then (1 : ℂ) else 0) *
            (if symp v z = 0 then (1 : ℂ) else 0) := by
          by_cases c1 : qform z = 0 <;> by_cases c2 : symp u z = 0 <;>
            by_cases c3 : symp v z = 0 <;> simp [c1, c2, c3]
        rw [hmul, indicator_eq, indicator_eq, indicator_eq]; ring
      have hC : (((univ.filter fun z : Pt 4 => qform z = 0 ∧ symp u z = 0 ∧ symp v z = 0).card : ℕ) : ℂ) = 28 := by
        rw [Finset.card_filter]; push_cast
        simp_rw [hind, ← Finset.sum_div]
        have hexp : ∀ z : Pt 4,
            (1 + eps (qform z)) * (1 + eps (symp u z)) * (1 + eps (symp v z)) =
            1 + eps (symp u z) + eps (symp v z) + eps (symp (u + v) z) +
              eps (qform z) + eps (qform z + symp u z) + eps (qform z + symp v z) +
              eps (qform z + symp (u + v) z) := by
          intro z; simp only [ExactDegreesN4N5.symp_add_left, eps_add]; ring
        simp only [hexp, Finset.sum_add_distrib, sum_eps_symp hu0, sum_eps_symp hv0,
          sum_eps_symp huv0, sum_eps_qform, sum_eps_qform_add_symp, hu, hv, huv_q,
          eps_one, Finset.sum_const, Finset.card_univ, card_pt, nsmul_eq_mul, mul_one]
        norm_num
      have h2 : ((8 * (univ.filter fun z : Pt 4 => qform z = 0 ∧ symp u z = 0 ∧ symp v z = 0).card : ℕ) : ℂ) = 224 := by
        push_cast; rw [hC]; norm_num
      exact_mod_cast h2
    rw [hSeq, Finset.card_erase_of_mem h0in]; omega
  -- Character-sum count `|flags S| = 270` (`10` neighbors per point in `S`).
  have hFcard : (flags S).card = 270 := by
    rw [card_flags]
    have hdeg : ∀ a ∈ S, (S.filter fun b => a + b ∈ S ∧ symp a b = 0).card = 10 := by
      intro a ha
      have haR := (mem_filter.mp ha).1
      obtain ⟨ha0, hqa⟩ := (mem_filter.mp haR).2
      obtain ⟨hsua, hsva⟩ := (mem_filter.mp ha).2
      have hfilt : S.filter (fun b => a + b ∈ S ∧ symp a b = 0) =
          ((univ.filter fun b : Pt 4 => qform b = 0 ∧ symp u b = 0 ∧ symp v b = 0 ∧ symp a b = 0).erase 0).erase a := by
        ext b
        simp only [S, anisoSection, realPoints, mem_filter, mem_erase, mem_univ, true_and]
        constructor
        · rintro ⟨⟨⟨hb0, hqb⟩, hsub, hsvb⟩, ⟨⟨hab0, _⟩, _⟩, hsab⟩
          exact ⟨fun h => hab0 (by rw [h, pt_add_self]), hb0, hqb, hsub, hsvb, hsab⟩
        · rintro ⟨hba, hb0, hqb, hsub, hsvb, hsab⟩
          refine ⟨⟨⟨hb0, hqb⟩, hsub, hsvb⟩, ⟨⟨fun h => hba (pt_eq_of_add_eq_zero h).symm, ?_⟩, ?_, ?_⟩, hsab⟩
          · rw [qform_add, hqa, hqb, hsab]; simp
          · rw [symp_add_right, hsua, hsub, add_zero]
          · rw [symp_add_right, hsva, hsvb, add_zero]
      have hqua : qform (u + a) = 1 := by rw [qform_add, hu, hqa, hsua]; simp
      have hqva : qform (v + a) = 1 := by rw [qform_add, hv, hqa, hsva]; simp
      have hquva : qform (u + v + a) = 1 := by
        rw [qform_add, huv_q, hqa, ExactDegreesN4N5.symp_add_left, hsua, hsva]; simp
      have hua0 : u + a ≠ 0 := fun h => absurd (h ▸ hqua) (by rw [qform_zero]; decide)
      have hva0 : v + a ≠ 0 := fun h => absurd (h ▸ hqva) (by rw [qform_zero]; decide)
      have huva0 : u + v + a ≠ 0 := fun h => absurd (h ▸ hquva) (by rw [qform_zero]; decide)
      have h16 : 16 * (univ.filter fun b : Pt 4 => qform b = 0 ∧ symp u b = 0 ∧ symp v b = 0 ∧ symp a b = 0).card = 192 := by
        have hind : ∀ b : Pt 4, (if qform b = 0 ∧ symp u b = 0 ∧ symp v b = 0 ∧ symp a b = 0 then (1 : ℂ) else 0) =
            ((1 + eps (qform b)) * (1 + eps (symp u b)) * (1 + eps (symp v b)) * (1 + eps (symp a b))) / 16 := by
          intro b
          have hmul : (if qform b = 0 ∧ symp u b = 0 ∧ symp v b = 0 ∧ symp a b = 0 then (1 : ℂ) else 0) =
              (if qform b = 0 then (1 : ℂ) else 0) * (if symp u b = 0 then (1 : ℂ) else 0) *
              (if symp v b = 0 then (1 : ℂ) else 0) * (if symp a b = 0 then (1 : ℂ) else 0) := by
            by_cases c0 : qform b = 0 <;> by_cases c1 : symp u b = 0 <;>
              by_cases c2 : symp v b = 0 <;> by_cases c3 : symp a b = 0 <;> simp [c0, c1, c2, c3]
          rw [hmul, indicator_eq, indicator_eq, indicator_eq, indicator_eq]; ring
        have hC : (((univ.filter fun b : Pt 4 => qform b = 0 ∧ symp u b = 0 ∧ symp v b = 0 ∧ symp a b = 0).card : ℕ) : ℂ) = 12 := by
          rw [Finset.card_filter]; push_cast
          simp_rw [hind, ← Finset.sum_div]
          have hexp : ∀ b : Pt 4,
              (1 + eps (qform b)) * (1 + eps (symp u b)) * (1 + eps (symp v b)) * (1 + eps (symp a b)) =
              1 + eps (symp u b) + eps (symp v b) + eps (symp a b) +
                eps (symp (u + v) b) + eps (symp (u + a) b) + eps (symp (v + a) b) +
                eps (symp (u + v + a) b) +
                eps (qform b) + eps (qform b + symp u b) + eps (qform b + symp v b) +
                eps (qform b + symp a b) + eps (qform b + symp (u + v) b) +
                eps (qform b + symp (u + a) b) + eps (qform b + symp (v + a) b) +
                eps (qform b + symp (u + v + a) b) := by
            intro b; simp only [ExactDegreesN4N5.symp_add_left, eps_add]; ring
          simp_rw [hexp, Finset.sum_add_distrib, sum_eps_symp hu0, sum_eps_symp hv0, sum_eps_symp ha0,
            sum_eps_symp huv0, sum_eps_symp hua0, sum_eps_symp hva0, sum_eps_symp huva0,
            sum_eps_qform, sum_eps_qform_add_symp, hu, hv, hqa, huv_q, hqua, hqva, hquva,
            eps_zero, eps_one, Finset.sum_const, Finset.card_univ, card_pt, nsmul_eq_mul, mul_one]
          norm_num
        have h2 : ((16 * (univ.filter fun b : Pt 4 => qform b = 0 ∧ symp u b = 0 ∧ symp v b = 0 ∧ symp a b = 0).card : ℕ) : ℂ) = 192 := by
          push_cast; rw [hC]; norm_num
        exact_mod_cast h2
      rw [hfilt]
      have h0in : (0 : Pt 4) ∈ univ.filter fun b : Pt 4 => qform b = 0 ∧ symp u b = 0 ∧ symp v b = 0 ∧ symp a b = 0 := by
        simp [qform_zero, symp_zero_right]
      have hain : a ∈ (univ.filter fun b : Pt 4 => qform b = 0 ∧ symp u b = 0 ∧ symp v b = 0 ∧ symp a b = 0).erase 0 :=
        mem_erase.mpr ⟨ha0, mem_filter.mpr ⟨mem_univ _, hqa, hsua, hsva, symp_self a⟩⟩
      rw [Finset.card_erase_of_mem hain, Finset.card_erase_of_mem h0in]
      omega
    rw [Finset.sum_congr rfl hdeg, Finset.sum_const, hScard]; norm_num
  -- Apply multiplicity-4 Kramers (`4 ∣ mult`) and `sum_cube_le` with `|κ| = 4`, `m = 27`, `a = 9`.
  set A := opA S f
  have hAh : A.IsHermitian := opA_isHermitian S f
  have hAreal : A.map star = A := by
    unfold A opA
    have hmap : (∑ z ∈ S, ((f z : ℝ) : ℂ) • pauli z).map star =
        ∑ z ∈ S, ((f z : ℝ) : ℂ) • (pauli z).map star := by
      ext x y; simp [Matrix.map_apply, Matrix.sum_apply, Complex.conj_ofReal]
    rw [hmap]
    refine Finset.sum_congr rfl fun z hz => ?_
    have hqz : qform z = 0 := (mem_filter.mp (mem_filter.mp hz).1).2.2
    rw [pauli_map_star, hqz, eps_zero, one_smul]
  have hAu : pauli u * A = A * pauli u := by
    unfold A opA; rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, pauli_comm z u, symp_comm z u, (mem_filter.mp hz).2.1,
      eps_zero, one_smul]
  have hAv : pauli v * A = A * pauli v := by
    unfold A opA; rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, pauli_comm z v, symp_comm z v, (mem_filter.mp hz).2.2,
      eps_zero, one_smul]
  have h4 := four_dvd_eig_mult_of_aniso hu hv huv hAh hAreal hAu hAv
  let R : Finset ℝ := univ.image hAh.eigenvalues
  let mult : ℝ → ℕ := fun r => (univ.filter fun i : Vec 4 => hAh.eigenvalues i = r).card
  let qtr : ℝ → ℕ := fun r => mult r / 4
  have h4qtr : ∀ r, 4 * qtr r = mult r := fun r => by obtain ⟨k, hk⟩ := h4 r; dsimp [qtr, mult]; omega
  let κ := Σ r : R, Fin (qtr r.1)
  let y : κ → ℝ := fun p => p.1.1
  have hsum_eq : ∀ g : ℝ → ℝ, ∑ i : Vec 4, g (hAh.eigenvalues i) = 4 * ∑ p : κ, g (y p) := by
    intro g
    rw [← Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_image_of_mem hAh.eigenvalues (mem_univ i))]
    have hterm : ∀ r ∈ R, ∑ i ∈ univ.filter (fun i : Vec 4 => hAh.eigenvalues i = r), g (hAh.eigenvalues i) =
        (4 : ℝ) * ((qtr r : ℕ) : ℝ) * g r := by
      intro r _
      rw [Finset.sum_congr rfl (fun i hi => by rw [(mem_filter.mp hi).2]), Finset.sum_const, nsmul_eq_mul]
      have hcast : ((mult r : ℕ) : ℝ) = 4 * ((qtr r : ℕ) : ℝ) := by exact_mod_cast (h4qtr r).symm
      exact congrArg (· * g r) hcast
    rw [Finset.sum_congr rfl hterm]
    have hκsum : ∑ p : κ, g (y p) = ∑ r : R, ((qtr r.1 : ℕ) : ℝ) * g r.1 := by
      rw [Fintype.sum_sigma]; refine Finset.sum_congr rfl fun r _ => by simp [y]
    rw [hκsum, ← Finset.sum_attach R, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  have hcardκ : Fintype.card κ = 4 := by
    set cκ : ℕ := Fintype.card κ
    have h1 : (16 : ℝ) = 4 * (cκ : ℝ) := by
      have hsum1 := hsum_eq (fun _ => (1 : ℝ))
      rw [Finset.sum_const, Finset.card_univ, card_vec, Finset.sum_const, Finset.card_univ] at hsum1
      change (2 ^ 4 : ℕ) • (1 : ℝ) = 4 * (cκ • (1 : ℝ)) at hsum1
      simp only [nsmul_eq_mul, mul_one] at hsum1
      push_cast at hsum1
      linarith
    have h2 : (cκ : ℝ) = 4 := by linarith
    exact_mod_cast h2
  have e1 : ∑ i : Vec 4, hAh.eigenvalues i = 0 := by
    have h := hAh.trace_eq_sum_eigenvalues
    rw [trace_opA S f h0] at h
    exact RCLike.ofReal_eq_zero.mp (by exact_mod_cast h.symm)
  have e2 : ∑ i : Vec 4, hAh.eigenvalues i ^ 2 = 432 := by
    have h := trace_pow_eq_sum_eigenvalues_pow hAh 2
    rw [trace_opA_sq S f hf, hScard] at h
    have hR : (∑ i : Vec 4, hAh.eigenvalues i ^ 2 : ℝ) = (2 : ℝ) ^ 4 * 27 := by exact_mod_cast h.symm
    linarith
  have e3 : ((A ^ 3).trace).re = ∑ i : Vec 4, hAh.eigenvalues i ^ 3 := by
    rw [trace_pow_eq_sum_eigenvalues_pow hAh 3]
    have : (∑ i : Vec 4, ((hAh.eigenvalues i : ℝ) : ℂ) ^ 3) = ((∑ i, hAh.eigenvalues i ^ 3 : ℝ) : ℂ) := by
      push_cast; rfl
    rw [this, Complex.ofReal_re]
  have hy1 : ∑ p : κ, y p = 0 := by have := hsum_eq id; dsimp at this; linarith
  have hy2 : ∑ p : κ, y p ^ 2 = Fintype.card κ * 27 := by
    have := hsum_eq (fun t => t ^ 2); rw [e2] at this; rw [hcardκ]; norm_num; linarith
  have hcube := sum_cube_le y 27 9 (by omega) hy1 hy2 (by norm_num) (by rw [hcardκ]; norm_num)
  rw [hcardκ] at hcube
  have hy3 := hsum_eq (fun t => t ^ 3)
  rw [← e3, trace_opA_cube, Complex.ofReal_re, beta6_eq_card S f hf, hFcard] at hy3
  norm_num at hcube hy3
  have hV_ge : (54 : ℝ) ≤ ((violated S f).card : ℝ) := by linarith
  have hV_nat : 54 ≤ (violated S f).card := by exact_mod_cast hV_ge
  have h6 := card_violated_le S h0 f
  omega

/-! ### Part 5. Concrete Masks, Exact Witnesses & All Four Headline Exact Degrees (`0`, `210`, `252`, `252`) -/

/-- Bitmask of `Q⁺(7,2)` (`135` observables). -/
def q7plusMask : ℕ := 0x96693cc35aa5f00f6699cc33aa5500ff6969c3c3a5a50f0f999933335555fffe

/-- The 9 solid bitmasks of the canonical `M1` spread of `Q⁺(7,2)`. -/
def m1SolidMask : Fin 9 → ℕ
  | ⟨0, _⟩ => 0x0001000100010001000100010001000100010001000100010001000100010000
  | ⟨1, _⟩ => 0x000000000000000000000000000000000000000000000000000000000000fffe
  | ⟨2, _⟩ => 0x8000200040001000008000200040001008000200040001000008000200040000
  | ⟨3, _⟩ => 0x0008008008008000040040000004004000200002200002001000010000100000
  | ⟨4, _⟩ => 0x0400100000800002020080000010000401004000002000080800200000400000
  | ⟨5, _⟩ => 0x0200000200202000000808008000008040000040000404000010100001000000
  | ⟨6, _⟩ => 0x1000004002000008400000100800000220000080010000048000002004000000
  | ⟨7, _⟩ => 0x0040040000044000200000020200002000088000008008000100001010000000
  | ⟨8, _⟩ => 0x0020080010000004001004002000000800400100800000020080020040000000

/-- Negative-sign mask attaining `315` on `Q⁺(7,2)` and `210` on `Q⁺(7,2) \ M1`. -/
def m1OptNeg : ℕ := 0x922824c152a020052009c421a00100e5490082438005070a199020125015a55a

/-- Bitmask of `Q⁺(7,2) \ O` (`126` observables, `1,260` contexts, 9-point ovoid deleted). -/
def ovoidRemovedMask : ℕ := 0x96493cc352a5f00f6499cc332a5500ff4969c3c3a5250f0f999133335554fffc

/-- Bitmask of `Q(6,2) = Q⁺(7,2) ∩ (Y0 4)⊥` (`63` observables, `315` contexts). -/
def q62Mask : ℕ := 0x822814410aa0500522884411aa00005528284141a0a005058888111100005554

/-- Negative-sign mask attaining `315` on `Q⁺(7,2)` and `252` on both `Q⁺(7,2) \ O` and `Q⁺(7,2) \ Q(6,2)`. -/
def ovoidOptNeg : ℕ := 0x100824815000600560184421a05000656108824200a5060a1881221250050ff2

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private def allUpTo (p : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => allUpTo p n && p n

private lemma allUpTo_spec (p : ℕ → Bool) (n : ℕ) (h : allUpTo p n = true) {z : ℕ} (hz : z < n) :
    p z = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [allUpTo, Bool.and_eq_true] at h
    by_cases hzn : z < n
    · exact ih h.1 hzn
    · have : z = n := by omega
      subst this; exact h.2

private def q7pCodeOk (z : ℕ) : Bool :=
  !q7plusMask.testBit z || (decide (z ≠ 0) && decide (common z 0 z 4 4 % 2 = 0))

private lemma q7p_codes_ok : allUpTo q7pCodeOk 256 = true := by decide +kernel
private lemma q7p_card_cfg : (cfg 4 q7plusMask).card = 135 := by
  rw [card_cfg_fast (b := 10) (N := 4) (by norm_num) (by norm_num)]; decide +kernel

lemma cfg_q7plus_eq : cfg 4 q7plusMask = realPoints 4 := by
  have hsub : cfg 4 q7plusMask ⊆ realPoints 4 := by
    intro u hu
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hu
    obtain ⟨hzlt, hzbit⟩ := mem_codes.mp hz
    have hok := allUpTo_spec q7pCodeOk 256 q7p_codes_ok hzlt
    simp only [q7pCodeOk, hzbit, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hok
    simp only [realPoints, mem_filter, mem_univ, true_and]
    refine ⟨fun h0 => hok.1 (ptOfCode_inj hzlt (by norm_num) (h0.trans (ptOfCode_zero 4).symm)), ?_⟩
    rw [qform, dot_eq_ycount, ycount_ptOfCode, ZMod.natCast_eq_zero_iff_even, Nat.even_iff]
    exact hok.2
  have hcardR : (realPoints 4).card = 135 := by have := card_realPoints (N := 4); norm_num at this; omega
  exact Finset.eq_of_subset_of_card_le hsub (by rw [q7p_card_cfg, hcardR])

private def q62CodeOk (z : ℕ) : Bool :=
  !q62Mask.testBit z || (q7plusMask.testBit z && decide ((if z.testBit 0 then 1 else 0) = (if z.testBit 4 then 1 else 0)))

private lemma q62_codes_ok : allUpTo q62CodeOk 256 = true := by decide +kernel
private lemma q62_card_cfg : (cfg 4 q62Mask).card = 63 := by
  rw [card_cfg_fast (b := 10) (N := 4) (by norm_num) (by norm_num)]; decide +kernel

lemma cfg_q62_eq : cfg 4 q62Mask = (realPoints 4).filter fun u => symp (ExactDegreesN4N5.Y0 4 (by norm_num)) u = 0 := by
  have hsub : cfg 4 q62Mask ⊆ (realPoints 4).filter fun u => symp (ExactDegreesN4N5.Y0 4 (by norm_num)) u = 0 := by
    intro u hu
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hu
    obtain ⟨hzlt, hzbit⟩ := mem_codes.mp hz
    have hok := allUpTo_spec q62CodeOk 256 q62_codes_ok hzlt
    simp only [q62CodeOk, hzbit, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hok
    refine mem_filter.mpr ⟨?_, ?_⟩
    · rw [← cfg_q7plus_eq]; exact (ptOfCode_mem_cfg hzlt).mpr hok.1
    · rw [ExactDegreesN4N5.symp_Y0_ptOfCode]
      unfold bitZ
      cases h0 : z.testBit 0 <;> cases h4 : z.testBit 4 <;> simp [h0, h4] at hok ⊢
      decide
  have hcardH : ((realPoints 4).filter fun u => symp (ExactDegreesN4N5.Y0 4 (by norm_num)) u = 0).card = 63 := by
    -- Reuse `q62Mask` exact count via `card_qshift` / `card_realPoints`.
    have hw := ExactDegreesN4N5.qform_Y0 4 (by norm_num)
    have h0in : (0 : Pt 4) ∈ univ.filter fun u : Pt 4 => qform u = 0 ∧ symp (ExactDegreesN4N5.Y0 4 (by norm_num)) u = 0 := by
      simp [qform_zero, symp_zero_right]
    have hHeq : (realPoints 4).filter (fun u => symp (ExactDegreesN4N5.Y0 4 (by norm_num)) u = 0) =
        (univ.filter fun u : Pt 4 => qform u = 0 ∧ symp (ExactDegreesN4N5.Y0 4 (by norm_num)) u = 0).erase 0 := by
      ext u; simp [realPoints, and_assoc, and_comm, and_left_comm]
    have hw0 : ExactDegreesN4N5.Y0 4 (by norm_num) ≠ 0 := fun h =>
      absurd (h ▸ hw) (by rw [qform_zero]; decide)
    have h4 : 4 * (univ.filter fun u : Pt 4 => qform u = 0 ∧ symp (ExactDegreesN4N5.Y0 4 (by norm_num)) u = 0).card = 256 := by
      have hind : ∀ u : Pt 4, (if qform u = 0 ∧ symp (ExactDegreesN4N5.Y0 4 (by norm_num)) u = 0 then (1 : ℂ) else 0) =
          (1 + eps (qform u) + eps (symp (ExactDegreesN4N5.Y0 4 (by norm_num)) u) +
            eps (qform u + symp (ExactDegreesN4N5.Y0 4 (by norm_num)) u)) / 4 := by
        intro u
        have h1 : (if qform u = 0 ∧ symp (ExactDegreesN4N5.Y0 4 (by norm_num)) u = 0 then (1 : ℂ) else 0) =
            (if qform u = 0 then (1 : ℂ) else 0) * (if symp (ExactDegreesN4N5.Y0 4 (by norm_num)) u = 0 then (1 : ℂ) else 0) := by
          by_cases c1 : qform u = 0 <;> by_cases c2 : symp (ExactDegreesN4N5.Y0 4 (by norm_num)) u = 0 <;> simp [c1, c2]
        rw [h1, indicator_eq, indicator_eq, eps_add]; ring
      have hC : (((univ.filter fun u : Pt 4 => qform u = 0 ∧ symp (ExactDegreesN4N5.Y0 4 (by norm_num)) u = 0).card : ℕ) : ℂ) = 64 := by
        rw [Finset.card_filter]; push_cast
        simp_rw [hind, ← Finset.sum_div, Finset.sum_add_distrib, sum_eps_qform, sum_eps_symp hw0,
          sum_eps_qform_add_symp, hw, eps_one, neg_one_mul, Finset.sum_const, Finset.card_univ,
          card_pt, nsmul_eq_mul, mul_one]
        norm_num
      have h2 : ((4 * (univ.filter fun u : Pt 4 => qform u = 0 ∧ symp (ExactDegreesN4N5.Y0 4 (by norm_num)) u = 0).card : ℕ) : ℂ) = 256 := by
        push_cast; rw [hC]; norm_num
      exact_mod_cast h2
    rw [hHeq, Finset.card_erase_of_mem h0in]; omega
  exact Finset.eq_of_subset_of_card_le hsub (by rw [q62_card_cfg, hcardH])

-- Verify `m1SolidMask` forms a valid `SolidSpread`.
private def solidMaskOk (m : ℕ) : Bool :=
  (m &&& q7plusMask == m) &&
  allUpTo (fun z => !m.testBit z ||
    allUpTo (fun w => !m.testBit w || (commB 4 z w && (decide (z = w) || m.testBit (z ^^^ w)))) 256) 256

private lemma m1_solids_valid :
    (∀ i : Fin 9, solidMaskOk (m1SolidMask i) = true) ∧
    (∀ i : Fin 9, loop (fun z => if (m1SolidMask i).testBit z then 1 else 0) 256 = 15) ∧
    (∀ i j : Fin 9, i ≠ j → (m1SolidMask i &&& m1SolidMask j) = 0) := by
  decide +kernel

/-- The explicit canonical `M1` spread of 9 solids of `Q⁺(7,2)`. -/
def m1Spread : SolidSpread where
  solid i := cfg 4 (m1SolidMask i)
  sub_real i := by
    intro u hu
    rw [← cfg_q7plus_eq]
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hu
    obtain ⟨hzlt, hzbit⟩ := mem_codes.mp hz
    have hok := (Bool.and_eq_true _ _).mp (m1_solids_valid.1 i)
    have hand : (m1SolidMask i &&& q7plusMask) = m1SolidMask i := by simpa using hok.1
    have hbit : (m1SolidMask i &&& q7plusMask).testBit z = true := by rwa [hand]
    rw [Nat.testBit_and, Bool.and_eq_true] at hbit
    exact (ptOfCode_mem_cfg hzlt).mpr hbit.2
  card_eq i := by
    rw [card_cfg, card_codes]
    exact m1_solids_valid.2.1 i
  closed i u hu v hv huv := by
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hu
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hv
    obtain ⟨hzlt, hzbit⟩ := mem_codes.mp hz
    obtain ⟨hwlt, hwbit⟩ := mem_codes.mp hw
    have hok := ((Bool.and_eq_true _ _).mp (m1_solids_valid.1 i)).2
    have h1 := allUpTo_spec _ 256 hok hzlt
    simp only [hzbit, Bool.not_true, Bool.false_or] at h1
    have h2 := allUpTo_spec _ 256 h1 hwlt
    simp only [hwbit, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at h2
    have hzw : z ≠ w := fun h => huv (by rw [h])
    have hbit : (m1SolidMask i).testBit (z ^^^ w) = true := h2.2.resolve_left hzw
    rw [← ptOfCode_xor]
    exact (ptOfCode_mem_cfg (Nat.xor_lt_two_pow hzlt hwlt)).mpr hbit
  comm i u hu v hv := by
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hu
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hv
    obtain ⟨hzlt, hzbit⟩ := mem_codes.mp hz
    obtain ⟨hwlt, hwbit⟩ := mem_codes.mp hw
    have hok := ((Bool.and_eq_true _ _).mp (m1_solids_valid.1 i)).2
    have h1 := allUpTo_spec _ 256 hok hzlt
    simp only [hzbit, Bool.not_true, Bool.false_or] at h1
    have h2 := allUpTo_spec _ 256 h1 hwlt
    simp only [hwbit, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h2
    exact (symp_ptOfCode_eq_zero 4 z w).mpr h2.1
  disj i j hij := by
    rw [Finset.disjoint_left]
    intro u hui huj
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hui
    obtain ⟨hzlt, hzbit⟩ := mem_codes.mp hz
    have hwbit : (m1SolidMask j).testBit z = true := (ptOfCode_mem_cfg hzlt).mp huj
    have h0 := m1_solids_valid.2.2 i j hij
    have hb : (m1SolidMask i &&& m1SolidMask j).testBit z = false := by rw [h0]; exact Nat.zero_testBit z
    rw [Nat.testBit_and, hzbit, hwbit] at hb
    exact absurd hb (by decide)

-- Kernel evaluations of witness violation counts (using `fastViolRow`, zero `native_decide`).
private lemma q7p_m1opt_vb :
    block (fastViolRow 10 4 q7plusMask m1OptNeg) 16 0 = 210 ∧
    block (fastViolRow 10 4 q7plusMask m1OptNeg) 16 1 = 112 ∧
    block (fastViolRow 10 4 q7plusMask m1OptNeg) 16 2 = 112 ∧
    block (fastViolRow 10 4 q7plusMask m1OptNeg) 16 3 = 112 ∧
    block (fastViolRow 10 4 q7plusMask m1OptNeg) 16 4 = 112 ∧
    block (fastViolRow 10 4 q7plusMask m1OptNeg) 16 5 = 112 ∧
    block (fastViolRow 10 4 q7plusMask m1OptNeg) 16 6 = 112 ∧
    block (fastViolRow 10 4 q7plusMask m1OptNeg) 16 7 = 112 ∧
    block (fastViolRow 10 4 q7plusMask m1OptNeg) 16 8 = 112 ∧
    block (fastViolRow 10 4 q7plusMask m1OptNeg) 16 9 = 112 ∧
    block (fastViolRow 10 4 q7plusMask m1OptNeg) 16 10 = 112 ∧
    block (fastViolRow 10 4 q7plusMask m1OptNeg) 16 11 = 112 ∧
    block (fastViolRow 10 4 q7plusMask m1OptNeg) 16 12 = 112 ∧
    block (fastViolRow 10 4 q7plusMask m1OptNeg) 16 13 = 112 ∧
    block (fastViolRow 10 4 q7plusMask m1OptNeg) 16 14 = 112 ∧
    block (fastViolRow 10 4 q7plusMask m1OptNeg) 16 15 = 112 := by decide +kernel

private lemma m1_solids_m1opt_viol :
    loop (fastViolRow 10 4 (m1SolidMask 0) m1OptNeg) 256 = 90 ∧
    loop (fastViolRow 10 4 (m1SolidMask 1) m1OptNeg) 256 = 0 ∧
    loop (fastViolRow 10 4 (m1SolidMask 2) m1OptNeg) 256 = 90 ∧
    loop (fastViolRow 10 4 (m1SolidMask 3) m1OptNeg) 256 = 0 ∧
    loop (fastViolRow 10 4 (m1SolidMask 4) m1OptNeg) 256 = 90 ∧
    loop (fastViolRow 10 4 (m1SolidMask 5) m1OptNeg) 256 = 90 ∧
    loop (fastViolRow 10 4 (m1SolidMask 6) m1OptNeg) 256 = 90 ∧
    loop (fastViolRow 10 4 (m1SolidMask 7) m1OptNeg) 256 = 90 ∧
    loop (fastViolRow 10 4 (m1SolidMask 8) m1OptNeg) 256 = 90 := by decide +kernel

private lemma q7p_ovopt_vb :
    block (fastViolRow 10 4 q7plusMask ovoidOptNeg) 16 0 = 210 ∧
    block (fastViolRow 10 4 q7plusMask ovoidOptNeg) 16 1 = 112 ∧
    block (fastViolRow 10 4 q7plusMask ovoidOptNeg) 16 2 = 112 ∧
    block (fastViolRow 10 4 q7plusMask ovoidOptNeg) 16 3 = 112 ∧
    block (fastViolRow 10 4 q7plusMask ovoidOptNeg) 16 4 = 112 ∧
    block (fastViolRow 10 4 q7plusMask ovoidOptNeg) 16 5 = 112 ∧
    block (fastViolRow 10 4 q7plusMask ovoidOptNeg) 16 6 = 112 ∧
    block (fastViolRow 10 4 q7plusMask ovoidOptNeg) 16 7 = 112 ∧
    block (fastViolRow 10 4 q7plusMask ovoidOptNeg) 16 8 = 112 ∧
    block (fastViolRow 10 4 q7plusMask ovoidOptNeg) 16 9 = 112 ∧
    block (fastViolRow 10 4 q7plusMask ovoidOptNeg) 16 10 = 112 ∧
    block (fastViolRow 10 4 q7plusMask ovoidOptNeg) 16 11 = 112 ∧
    block (fastViolRow 10 4 q7plusMask ovoidOptNeg) 16 12 = 112 ∧
    block (fastViolRow 10 4 q7plusMask ovoidOptNeg) 16 13 = 112 ∧
    block (fastViolRow 10 4 q7plusMask ovoidOptNeg) 16 14 = 112 ∧
    block (fastViolRow 10 4 q7plusMask ovoidOptNeg) 16 15 = 112 := by decide +kernel

private lemma q62_ovopt_vb :
    block (fastViolRow 10 4 q62Mask ovoidOptNeg) 16 0 = 42 ∧
    block (fastViolRow 10 4 q62Mask ovoidOptNeg) 16 1 = 0 ∧
    block (fastViolRow 10 4 q62Mask ovoidOptNeg) 16 2 = 24 ∧
    block (fastViolRow 10 4 q62Mask ovoidOptNeg) 16 3 = 24 ∧
    block (fastViolRow 10 4 q62Mask ovoidOptNeg) 16 4 = 24 ∧
    block (fastViolRow 10 4 q62Mask ovoidOptNeg) 16 5 = 24 ∧
    block (fastViolRow 10 4 q62Mask ovoidOptNeg) 16 6 = 24 ∧
    block (fastViolRow 10 4 q62Mask ovoidOptNeg) 16 7 = 24 ∧
    block (fastViolRow 10 4 q62Mask ovoidOptNeg) 16 8 = 24 ∧
    block (fastViolRow 10 4 q62Mask ovoidOptNeg) 16 9 = 24 ∧
    block (fastViolRow 10 4 q62Mask ovoidOptNeg) 16 10 = 24 ∧
    block (fastViolRow 10 4 q62Mask ovoidOptNeg) 16 11 = 24 ∧
    block (fastViolRow 10 4 q62Mask ovoidOptNeg) 16 12 = 24 ∧
    block (fastViolRow 10 4 q62Mask ovoidOptNeg) 16 13 = 24 ∧
    block (fastViolRow 10 4 q62Mask ovoidOptNeg) 16 14 = 24 ∧
    block (fastViolRow 10 4 q62Mask ovoidOptNeg) 16 15 = 24 := by decide +kernel

private lemma ovrem_ovopt_vb :
    block (fastViolRow 10 4 ovoidRemovedMask ovoidOptNeg) 16 0 = 168 ∧
    block (fastViolRow 10 4 ovoidRemovedMask ovoidOptNeg) 16 1 = 84 ∧
    block (fastViolRow 10 4 ovoidRemovedMask ovoidOptNeg) 16 2 = 96 ∧
    block (fastViolRow 10 4 ovoidRemovedMask ovoidOptNeg) 16 3 = 84 ∧
    block (fastViolRow 10 4 ovoidRemovedMask ovoidOptNeg) 16 4 = 96 ∧
    block (fastViolRow 10 4 ovoidRemovedMask ovoidOptNeg) 16 5 = 84 ∧
    block (fastViolRow 10 4 ovoidRemovedMask ovoidOptNeg) 16 6 = 96 ∧
    block (fastViolRow 10 4 ovoidRemovedMask ovoidOptNeg) 16 7 = 84 ∧
    block (fastViolRow 10 4 ovoidRemovedMask ovoidOptNeg) 16 8 = 96 ∧
    block (fastViolRow 10 4 ovoidRemovedMask ovoidOptNeg) 16 9 = 84 ∧
    block (fastViolRow 10 4 ovoidRemovedMask ovoidOptNeg) 16 10 = 96 ∧
    block (fastViolRow 10 4 ovoidRemovedMask ovoidOptNeg) 16 11 = 84 ∧
    block (fastViolRow 10 4 ovoidRemovedMask ovoidOptNeg) 16 12 = 96 ∧
    block (fastViolRow 10 4 ovoidRemovedMask ovoidOptNeg) 16 13 = 84 ∧
    block (fastViolRow 10 4 ovoidRemovedMask ovoidOptNeg) 16 14 = 96 ∧
    block (fastViolRow 10 4 ovoidRemovedMask ovoidOptNeg) 16 15 = 84 := by decide +kernel

/-- Polymorphic helper: any subset `V ⊆ flags R` (`0 ∉ R`) closed under permuting ordered pairs of
the same line has `V.card = 6 * (V.image lineOf).card` (never unfolds concrete `flags (realPoints 4)`). -/
private lemma card_eq_six_image_lineOf {N : ℕ} {R : Finset (Pt N)} (h0 : (0 : Pt N) ∉ R)
    (V : Finset (Pt N × Pt N)) (hsub : ∀ q ∈ V, q ∈ flags R)
    (hclosed : ∀ q ∈ V, ∀ p ∈ (lineOf q).offDiag, p ∈ V) :
    V.card = 6 * (V.image lineOf).card := by
  rw [Finset.card_eq_sum_card_image lineOf V]
  have hfib : ∀ L ∈ V.image lineOf, (V.filter fun p => lineOf p = L).card = 6 := by
    intro L hL
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hL
    have hqF : q ∈ flags R := hsub q hq
    have hfeq : V.filter (fun p => lineOf p = lineOf q) = (lineOf q).offDiag := by
      ext p; constructor
      · intro hp
        obtain ⟨hpv, hpl⟩ := mem_filter.mp hp
        obtain ⟨_, _, h3, _⟩ := mem_flags.mp (hsub p hpv)
        rw [mem_offDiag, ← hpl]
        exact ⟨by simp [lineOf], by simp [lineOf], fun h => h0 (by rwa [h, pt_add_self] at h3)⟩
      · intro hp
        exact mem_filter.mpr ⟨hclosed q hq p hp, lineOf_of_mem_offDiag hp⟩
    rw [hfeq, Finset.offDiag_card, card_lineOf_of_flag h0 hqF]
  rw [Finset.sum_congr rfl hfib]; simp [Nat.mul_comm]

set_option maxHeartbeats 200000

/-- **Theorem 23(0) — `Q⁺(7,2) \ DW(5,2)` has exact degree `0`:**
The `m1OptNeg` witness violates exactly `315` contexts of `Q⁺(7,2)` (a `DW(5,2)`), so removing
those `315` contexts leaves `1,260` residual contexts with `0` violations. -/
theorem dw52_residual_exact_zero :
    ∃ f : Pt 4 → ℝ, (∀ u, f u = 1 ∨ f u = -1) ∧
      (violatedLines (realPoints 4) f).card = 315 ∧
      ((contexts (realPoints 4)) \ (violatedLines (realPoints 4) f)).card = 1260 := by
  let f : Pt 4 → ℝ := fun u => ((sgnOf 4 m1OptNeg u : ℤ) : ℝ)
  have hf : ∀ u, f u = 1 ∨ f u = -1 := sgnOf_values 4 m1OptNeg
  have hv : (violated (realPoints 4) f).card = 6 * 315 := by
    rw [← cfg_q7plus_eq]
    have h := loop_blocks (fastViolRow 10 4 q7plusMask m1OptNeg) 16 16
    rcases q7p_m1opt_vb with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
    rw [loop_sixteen, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15] at h
    have e : (2 : ℕ) ^ (2 * 4) = 16 * 16 := by norm_num
    rw [card_violated_cfg_fast (b := 10) (N := 4) (by norm_num) (by norm_num), e]
    exact h.trans (by norm_num)
  have h0 : (0 : Pt 4) ∉ realPoints 4 := by simp [realPoints]
  have h6v := card_violated_eq_six (realPoints 4) h0 f
  have hv315 : (violatedLines (realPoints 4) f).card = 315 := by omega
  have hFreal : (flags (realPoints 4)).card = 9450 := by
    have hS : (realPoints 4).card = 135 := by have := card_realPoints (N := 4); norm_num at this; omega
    have hF := card_flags_real (N := 4); rw [hS] at hF; norm_num at hF; omega
  have h6c := card_flags_eq_six_contexts (realPoints 4) h0
  have hc1575 : (contexts (realPoints 4)).card = 1575 := by omega
  have hsub : violatedLines (realPoints 4) f ⊆ contexts (realPoints 4) :=
    Finset.image_subset_image (Finset.filter_subset _ _)
  refine ⟨f, hf, hv315, ?_⟩
  rw [Finset.card_sdiff_of_subset hsub, hc1575, hv315]

/-- **Theorem 23(a) — Exact Degree `210` on `Q⁺(7,2) \ M1` (`135` pts, `1,260` residual contexts):**
Universal lower bound `210` + exact attaining witness `m1OptNeg`. -/
theorem m1_spread_residual_exact_210 :
    (∀ f : Pt 4 → ℝ, (∀ u ∈ realPoints 4, f u = 1 ∨ f u = -1) →
      210 ≤ (m1Spread.resViolatedLines f).card) ∧
    (∃ f : Pt 4 → ℝ, (∀ u, f u = 1 ∨ f u = -1) ∧
      (m1Spread.resViolatedLines f).card = 210) := by
  refine ⟨fun f hf => m1Spread.spread_residual_ge_210 f hf, ?_⟩
  let f : Pt 4 → ℝ := fun u => ((sgnOf 4 m1OptNeg u : ℤ) : ℝ)
  refine ⟨f, sgnOf_values 4 m1OptNeg, ?_⟩
  have hge := m1Spread.spread_residual_ge_210 f (fun u _ => sgnOf_values 4 m1OptNeg u)
  have htot : (violated (realPoints 4) f).card = 1890 := by
    rw [← cfg_q7plus_eq]
    have h := loop_blocks (fastViolRow 10 4 q7plusMask m1OptNeg) 16 16
    rcases q7p_m1opt_vb with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
    rw [loop_sixteen, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15] at h
    have e : (2 : ℕ) ^ (2 * 4) = 16 * 16 := by norm_num
    rw [card_violated_cfg_fast (b := 10) (N := 4) (by norm_num) (by norm_num), e]
    exact h.trans (by norm_num)
  have hsol : ∀ i : Fin 9, (violated (m1Spread.solid i) f).card =
      loop (fastViolRow 10 4 (m1SolidMask i) m1OptNeg) 256 := fun i =>
    card_violated_cfg_fast (b := 10) (N := 4) (by norm_num) (by norm_num) (m1SolidMask i) m1OptNeg
  have hsum_sol : ∑ i : Fin 9, (violated (m1Spread.solid i) f).card = 630 := by
    simp_rw [hsol]
    rcases m1_solids_m1opt_viol with ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change loop (fastViolRow 10 4 (m1SolidMask 0) m1OptNeg) 256 +
      (loop (fastViolRow 10 4 (m1SolidMask 1) m1OptNeg) 256 +
      (loop (fastViolRow 10 4 (m1SolidMask 2) m1OptNeg) 256 +
      (loop (fastViolRow 10 4 (m1SolidMask 3) m1OptNeg) 256 +
      (loop (fastViolRow 10 4 (m1SolidMask 4) m1OptNeg) 256 +
      (loop (fastViolRow 10 4 (m1SolidMask 5) m1OptNeg) 256 +
      (loop (fastViolRow 10 4 (m1SolidMask 6) m1OptNeg) 256 +
      (loop (fastViolRow 10 4 (m1SolidMask 7) m1OptNeg) 256 +
       loop (fastViolRow 10 4 (m1SolidMask 8) m1OptNeg) 256))))))) = 630
    omega
  have hres_card : (m1Spread.resViolated f).card = 1260 := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := violated (realPoints 4) f)
      (fun p => ∀ i : Fin 9, ¬ (p.1 ∈ m1Spread.solid i ∧ p.2 ∈ m1Spread.solid i))
    have h1 : (violated (realPoints 4) f).filter
        (fun p => ∀ i : Fin 9, ¬ (p.1 ∈ m1Spread.solid i ∧ p.2 ∈ m1Spread.solid i)) =
        m1Spread.resViolated f := by
      ext p
      simp only [SolidSpread.mem_resViolated, SolidSpread.mem_resFlags, mem_q7pFlags, violated, mem_filter, mem_flags]
      exact ⟨fun ⟨⟨hf, hbad⟩, hnot⟩ => ⟨⟨hf, hnot⟩, hbad⟩, fun ⟨⟨hf, hnot⟩, hbad⟩ => ⟨⟨hf, hbad⟩, hnot⟩⟩
    have h2 : (violated (realPoints 4) f).filter
        (fun p => ¬ ∀ i : Fin 9, ¬ (p.1 ∈ m1Spread.solid i ∧ p.2 ∈ m1Spread.solid i)) =
        (univ : Finset (Fin 9)).biUnion fun i => violated (m1Spread.solid i) f := by
      ext p
      simp only [violated, mem_filter, mem_biUnion, mem_univ, true_and, mem_flags]
      constructor
      · rintro ⟨⟨⟨_, _, h3, hs⟩, hbad⟩, hnot⟩
        push Not at hnot
        obtain ⟨i, ha, hb⟩ := hnot
        have hne : p.1 ≠ p.2 := fun h => (mem_filter.mp h3).2.1 (by rw [h, pt_add_self])
        exact ⟨i, ⟨ha, hb, m1Spread.closed i p.1 ha p.2 hb hne, hs⟩, hbad⟩
      · rintro ⟨i, ⟨ha, hb, hc, hs⟩, hbad⟩
        exact ⟨⟨⟨m1Spread.sub_real i ha, m1Spread.sub_real i hb, m1Spread.sub_real i hc, hs⟩, hbad⟩,
          fun hall => hall i ⟨ha, hb⟩⟩
    have hdisj : Set.PairwiseDisjoint (↑(univ : Finset (Fin 9))) fun i => violated (m1Spread.solid i) f := by
      intro i _ j _ hij
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      exact Finset.disjoint_left.mp (m1Spread.disj i j hij)
        (mem_flags.mp (mem_filter.mp hp1).1).1 (mem_flags.mp (mem_filter.mp hp2).1).1
    rw [h1, h2, Finset.card_biUnion hdisj, hsum_sol, htot] at hsplit
    omega
  have h6eq : (m1Spread.resViolated f).card = 6 * (m1Spread.resViolatedLines f).card := by
    have h0 : (0 : Pt 4) ∉ realPoints 4 := by simp [realPoints]
    refine card_eq_six_image_lineOf h0 (m1Spread.resViolated f)
      (fun q hq => mem_flags.mpr (mem_q7pFlags.mp (SolidSpread.mem_resFlags.mp (SolidSpread.mem_resViolated.mp hq).1).1))
      (fun q hq p hp => ?_)
    obtain ⟨hqR, hqbad⟩ := SolidSpread.mem_resViolated.mp hq
    obtain ⟨hqF, hq_not⟩ := SolidSpread.mem_resFlags.mp hqR
    have hqV : q ∈ violated (realPoints 4) f := by
      rw [violated, mem_filter]
      exact ⟨mem_flags.mpr (mem_q7pFlags.mp hqF), hqbad⟩
    have hpV := mem_violated_of_mem_offDiag hqV hp
    rw [violated, mem_filter] at hpV
    have hpl := lineOf_of_mem_offDiag hp
    have hp_not : ∀ i : Fin 9, ¬ (p.1 ∈ m1Spread.solid i ∧ p.2 ∈ m1Spread.solid i) := by
      intro i ⟨h1, h2⟩
      have hne : p.1 ≠ p.2 := (mem_offDiag.mp hp).2.2
      have h3 : p.1 + p.2 ∈ m1Spread.solid i := m1Spread.closed i p.1 h1 p.2 h2 hne
      have hall : ∀ z ∈ lineOf p, z ∈ m1Spread.solid i := by
        intro z hz; simp only [lineOf, mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl | rfl <;> assumption
      rw [hpl] at hall
      exact hq_not i ⟨hall q.1 (by simp [lineOf]), hall q.2 (by simp [lineOf])⟩
    exact SolidSpread.mem_resViolated.mpr ⟨SolidSpread.mem_resFlags.mpr ⟨mem_q7pFlags.mpr (mem_flags.mp hpV.1), hp_not⟩, hpV.2⟩
  omega

/-- **Theorem 23(b) — Exact Degree `252` on `Q⁺(7,2) \ Q(6,2)` (`135` pts, `1,260` residual contexts):**
Universal lower bound `252` + exact attaining witness `ovoidOptNeg`. -/
theorem q62_residual_exact_252 :
    (∀ f : Pt 4 → ℝ, (∀ u ∈ realPoints 4, f u = 1 ∨ f u = -1) →
      252 ≤ (q62ResViolatedLines (ExactDegreesN4N5.Y0 4 (by norm_num)) f).card) ∧
    (∃ f : Pt 4 → ℝ, (∀ u, f u = 1 ∨ f u = -1) ∧
      (q62ResViolatedLines (ExactDegreesN4N5.Y0 4 (by norm_num)) f).card = 252) := by
  let w := ExactDegreesN4N5.Y0 4 (by norm_num)
  have hw : qform w = 1 := ExactDegreesN4N5.qform_Y0 4 (by norm_num)
  refine ⟨fun f hf => q62_residual_ge_252 w hw f hf, ?_⟩
  let f : Pt 4 → ℝ := fun u => ((sgnOf 4 ovoidOptNeg u : ℤ) : ℝ)
  refine ⟨f, sgnOf_values 4 ovoidOptNeg, ?_⟩
  have hge := q62_residual_ge_252 w hw f (fun u _ => sgnOf_values 4 ovoidOptNeg u)
  have htot : (violated (realPoints 4) f).card = 1890 := by
    rw [← cfg_q7plus_eq]
    have h := loop_blocks (fastViolRow 10 4 q7plusMask ovoidOptNeg) 16 16
    rcases q7p_ovopt_vb with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
    rw [loop_sixteen, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15] at h
    have e : (2 : ℕ) ^ (2 * 4) = 16 * 16 := by norm_num
    rw [card_violated_cfg_fast (b := 10) (N := 4) (by norm_num) (by norm_num), e]
    exact h.trans (by norm_num)
  have hq62v : (violated (cfg 4 q62Mask) f).card = 378 := by
    have h := loop_blocks (fastViolRow 10 4 q62Mask ovoidOptNeg) 16 16
    rcases q62_ovopt_vb with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
    rw [loop_sixteen, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15] at h
    have e : (2 : ℕ) ^ (2 * 4) = 16 * 16 := by norm_num
    rw [card_violated_cfg_fast (b := 10) (N := 4) (by norm_num) (by norm_num), e]
    exact h.trans (by norm_num)
  have hres_card : (q62ResViolated w f).card = 1512 := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := violated (realPoints 4) f)
      (fun p => symp w p.1 = 0 ∧ symp w p.2 = 0)
    have h1 : (violated (realPoints 4) f).filter (fun p => symp w p.1 = 0 ∧ symp w p.2 = 0) =
        violated (cfg 4 q62Mask) f := by
      rw [cfg_q62_eq]; ext p; simp only [violated, mem_filter, mem_flags]
      constructor
      · rintro ⟨⟨⟨h1, h2, h3, hs⟩, hbad⟩, s1, s2⟩
        exact ⟨⟨⟨h1, s1⟩, ⟨h2, s2⟩, ⟨h3, by rw [symp_add_right, s1, s2, add_zero]⟩, hs⟩, hbad⟩
      · rintro ⟨⟨⟨h1, s1⟩, ⟨h2, s2⟩, ⟨h3, _⟩, hs⟩, hbad⟩
        exact ⟨⟨⟨h1, h2, h3, hs⟩, hbad⟩, s1, s2⟩
    have h2 : (violated (realPoints 4) f).filter (fun p => ¬ (symp w p.1 = 0 ∧ symp w p.2 = 0)) =
        q62ResViolated w f := by
      ext p
      simp only [mem_q62ResViolated, mem_q62ResFlags, mem_q7pFlags, violated, mem_filter, mem_flags]
      exact ⟨fun ⟨⟨hf, hbad⟩, hnot⟩ => ⟨⟨hf, hnot⟩, hbad⟩, fun ⟨⟨hf, hnot⟩, hbad⟩ => ⟨⟨hf, hbad⟩, hnot⟩⟩
    rw [h1, h2, hq62v, htot] at hsplit; omega
  have h6eq : (q62ResViolated w f).card = 6 * (q62ResViolatedLines w f).card := by
    have h0 : (0 : Pt 4) ∉ realPoints 4 := by simp [realPoints]
    refine card_eq_six_image_lineOf h0 (q62ResViolated w f)
      (fun q hq => mem_flags.mpr (mem_q7pFlags.mp (mem_q62ResFlags.mp (mem_q62ResViolated.mp hq).1).1))
      (fun q hq p hp => ?_)
    obtain ⟨hqR, hqbad⟩ := mem_q62ResViolated.mp hq
    obtain ⟨hqF, hq_not⟩ := mem_q62ResFlags.mp hqR
    have hqV : q ∈ violated (realPoints 4) f := by
      rw [violated, mem_filter]
      exact ⟨mem_flags.mpr (mem_q7pFlags.mp hqF), hqbad⟩
    have hpV := mem_violated_of_mem_offDiag hqV hp
    rw [violated, mem_filter] at hpV
    have hpl := lineOf_of_mem_offDiag hp
    have hp_not : ¬ (symp w p.1 = 0 ∧ symp w p.2 = 0) := by
      rintro ⟨s1, s2⟩
      have s3 : symp w (p.1 + p.2) = 0 := by rw [symp_add_right, s1, s2, add_zero]
      have hall : ∀ z ∈ lineOf p, symp w z = 0 := by
        intro z hz; simp only [lineOf, mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl | rfl <;> assumption
      rw [hpl] at hall
      exact hq_not ⟨hall q.1 (by simp [lineOf]), hall q.2 (by simp [lineOf])⟩
    exact mem_q62ResViolated.mpr ⟨mem_q62ResFlags.mpr ⟨mem_q7pFlags.mpr (mem_flags.mp hpV.1), hp_not⟩, hpV.2⟩
  change (q62ResViolatedLines w f).card = 252
  omega

-- Part 5b: Exact Degree `252` on `Q⁺(7,2) \ O` (`cfg 4 ovoidRemovedMask`, `126` pts, `1,260` lines).
private def ovoidCodes : List ℕ := [1, 16, 51, 87, 125, 159, 185, 219, 245]

private def oddCode (u : ℕ) : Bool := decide (common u 0 u 4 4 % 2 = 1)

private def anisoOvoidOk (u v : ℕ) : Bool :=
  decide (u < 256) && decide (v < 256) && oddCode u && oddCode v && !commB 4 u v &&
  ovoidCodes.all fun o => !commB 4 u o || !commB 4 v o

/-- Canonical representatives `(u, v)` (`u < v < u ^^^ v`) of all `280` ovoid-disjoint anisotropic 2-planes. -/
private def anisoOvoid280 : List (ℕ × ℕ) := [
  (19, 34), (19, 77), (19, 79), (19, 108), (19, 137), (19, 139), (19, 168), (19, 197), (19, 199), (19, 228),
  (21, 43), (21, 47), (21, 70), (21, 108), (21, 137), (21, 141), (21, 163), (21, 167), (21, 202), (21, 228),
  (23, 34), (23, 70), (23, 99), (23, 101), (23, 139), (23, 141), (23, 168), (23, 202), (23, 233), (23, 239),
  (25, 39), (25, 47), (25, 69), (25, 77), (25, 99), (25, 107), (25, 142), (25, 168), (25, 202), (25, 228),
  (27, 34), (27, 69), (27, 79), (27, 108), (27, 142), (27, 167), (27, 173), (27, 202), (27, 227), (27, 233),
  (29, 39), (29, 43), (29, 70), (29, 108), (29, 142), (29, 168), (29, 197), (29, 201), (29, 227), (29, 239),
  (31, 34), (31, 70), (31, 101), (31, 107), (31, 142), (31, 163), (31, 173), (31, 199), (31, 201), (31, 228),
  (34, 83), (34, 91), (34, 147), (34, 151), (34, 211), (34, 223), (39, 83), (39, 94), (39, 145), (39, 149),
  (39, 152), (39, 156), (39, 214), (39, 223), (43, 81), (43, 84), (43, 89), (43, 92), (43, 151), (43, 154),
  (43, 211), (43, 214), (47, 91), (47, 94), (47, 147), (47, 154), (47, 209), (47, 212), (47, 216), (47, 221),
  (49, 69), (49, 70), (49, 84), (49, 141), (49, 142), (49, 156), (49, 201), (49, 202), (49, 216), (53, 79),
  (53, 89), (53, 94), (53, 137), (53, 142), (53, 152), (53, 199), (53, 209), (53, 214), (54, 79), (54, 83),
  (54, 137), (54, 141), (54, 145), (54, 149), (54, 199), (54, 223), (57, 70), (57, 77), (57, 92), (57, 139),
  (57, 145), (57, 154), (57, 199), (57, 214), (57, 221), (58, 69), (58, 77), (58, 81), (58, 89), (58, 139),
  (58, 151), (58, 199), (58, 211), (61, 79), (61, 81), (61, 94), (61, 139), (61, 149), (61, 154), (61, 197),
  (61, 202), (61, 212), (62, 79), (62, 91), (62, 139), (62, 147), (62, 197), (62, 201), (62, 209), (62, 221),
  (69, 145), (69, 147), (69, 152), (69, 154), (69, 178), (69, 187), (70, 149), (70, 151), (70, 177), (70, 187),
  (77, 149), (77, 156), (77, 181), (77, 182), (77, 188), (77, 191), (79, 151), (79, 156), (79, 177), (79, 178),
  (81, 137), (81, 142), (81, 152), (81, 163), (81, 178), (81, 181), (83, 139), (83, 142), (83, 154), (83, 168),
  (83, 173), (83, 188), (84, 137), (84, 139), (84, 145), (84, 147), (84, 163), (84, 187), (89, 141), (89, 147),
  (89, 156), (89, 167), (89, 168), (89, 182), (91, 141), (91, 145), (91, 156), (91, 163), (91, 178), (91, 191),
  (92, 141), (92, 149), (92, 167), (92, 173), (92, 181), (92, 191), (94, 141), (94, 151), (94, 163), (94, 177),
  (99, 145), (99, 152), (99, 178), (99, 181), (99, 187), (99, 188), (101, 151), (101, 152), (101, 177), (101, 182),
  (107, 147), (107, 149), (107, 154), (107, 156), (107, 182), (107, 191), (108, 145), (108, 151), (108, 177), (108, 191),
  (113, 137), (113, 149), (113, 152), (113, 167), (113, 182), (113, 187), (114, 137), (114, 145), (114, 163), (114, 173),
  (114, 181), (114, 187), (116, 137), (116, 151), (116, 167), (116, 177), (119, 137), (119, 147), (119, 152), (119, 163),
  (119, 168), (119, 178), (121, 139), (121, 142), (121, 154), (121, 168), (121, 173), (121, 188), (122, 139), (122, 141),
  (122, 147), (122, 149), (122, 167), (122, 191), (127, 141), (127, 142), (127, 156), (127, 167), (127, 181), (127, 182)
]

private def bitMask4 (k : Fin 8) : ℕ :=
  match k with
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
  | 6 => 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
  | 7 => 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000

private def all256Mask : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

private def commMask4 (u : ℕ) : ℕ :=
  all256Mask ^^^
  (if u.testBit 0 then bitMask4 4 else 0) ^^^
  (if u.testBit 1 then bitMask4 5 else 0) ^^^
  (if u.testBit 2 then bitMask4 6 else 0) ^^^
  (if u.testBit 3 then bitMask4 7 else 0) ^^^
  (if u.testBit 4 then bitMask4 0 else 0) ^^^
  (if u.testBit 5 then bitMask4 1 else 0) ^^^
  (if u.testBit 6 then bitMask4 2 else 0) ^^^
  (if u.testBit 7 then bitMask4 3 else 0)

set_option maxHeartbeats 0

private lemma bitMask4_testBit (k : Fin 8) {w : ℕ} (hw : w < 256) :
    (bitMask4 k).testBit w = w.testBit k.val := by
  have h : allUpTo (fun w =>
      ((bitMask4 0).testBit w == w.testBit 0) && ((bitMask4 1).testBit w == w.testBit 1) &&
      ((bitMask4 2).testBit w == w.testBit 2) && ((bitMask4 3).testBit w == w.testBit 3) &&
      ((bitMask4 4).testBit w == w.testBit 4) && ((bitMask4 5).testBit w == w.testBit 5) &&
      ((bitMask4 6).testBit w == w.testBit 6) && ((bitMask4 7).testBit w == w.testBit 7)) 256 = true := by
    decide +kernel
  have hw' := allUpTo_spec _ 256 h hw
  simp only [Bool.and_eq_true, beq_iff_eq] at hw'
  fin_cases k <;> tauto

private lemma all256Mask_testBit {w : ℕ} (hw : w < 256) : all256Mask.testBit w = true := by
  have h : allUpTo (fun w => all256Mask.testBit w) 256 = true := by decide +kernel
  exact allUpTo_spec _ 256 h hw

private lemma commMask4_testBit (u : ℕ) {w : ℕ} (hw : w < 256) :
    (commMask4 u).testBit w = commB 4 u w := by
  have hite : ∀ (b : Bool) (m : ℕ), (if b then m else 0).testBit w = (b && m.testBit w) := by
    intro b m; cases b <;> simp
  unfold commMask4 commB
  simp only [Nat.testBit_xor, all256Mask_testBit hw, hite, bitMask4_testBit _ hw, common,
    show (0 : Fin 8).val = 0 from rfl, show (1 : Fin 8).val = 1 from rfl,
    show (2 : Fin 8).val = 2 from rfl, show (3 : Fin 8).val = 3 from rfl,
    show (4 : Fin 8).val = 4 from rfl, show (5 : Fin 8).val = 5 from rfl,
    show (6 : Fin 8).val = 6 from rfl, show (7 : Fin 8).val = 7 from rfl,
    Nat.zero_add, Bool.and_comm (w.testBit _)]
  generalize (u.testBit 0 && w.testBit 4) = x0; generalize (u.testBit 1 && w.testBit 5) = x1
  generalize (u.testBit 2 && w.testBit 6) = x2; generalize (u.testBit 3 && w.testBit 7) = x3
  generalize (u.testBit 4 && w.testBit 0) = y0; generalize (u.testBit 5 && w.testBit 1) = y1
  generalize (u.testBit 6 && w.testBit 2) = y2; generalize (u.testBit 7 && w.testBit 3) = y3
  cases x0 <;> cases x1 <;> cases x2 <;> cases x3 <;> cases y0 <;> cases y1 <;> cases y2 <;> cases y3 <;> rfl

private def all10Lit : ℕ :=
  0x40100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401

private def ov10Lit : ℕ :=
  0x40000001000010040000001000000040000001000000040100401000000040100000000000040100001000010000000400004000040000001000010040100401000000000000000000000040100401000010040000001000000040000001004000000100401000000040100000000000040100000004010000000400004000040000001000010000100001000000000000000000000040100401004010040100001000000040000001000010040000400000010040100000000000040100401000000000000401004000040000001000010000000400000010000100000000000040100401000000000000401004010040000001004000000100400000010000000001000000040100000004010000000401000000040100001000010000100001000010000100001000000040100401004010040100401004010040100000

private def st10Lit : ℕ → ℕ
  | 0 => 0x40000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400004000040000400
  | 1 => 0x40100000004010000000401000000040100000004010000000401000000040100000004010000000401000000040100000004010000000401000000040100000004010000000401000000040100000004010000000401000000040100000004010000000401000000040100000004010000000401000000040100000004010000000401000000040100000004010000000401000000040100000004010000000401000000040100000004010000000401000000040100000004010000000401000000040100000004010000000401000000040100000004010000000401000000040100000004010000000401000000040100000004010000000401000000040100000004010000000401000000040100000004010000000401000000040100000004010000000401000000040100000004010000000401000000040100000
  | 2 => 0x40100401000000000000401004010000000000004010040100000000000040100401000000000000401004010000000000004010040100000000000040100401000000000000401004010000000000004010040100000000000040100401000000000000401004010000000000004010040100000000000040100401000000000000401004010000000000004010040100000000000040100401000000000000401004010000000000004010040100000000000040100401000000000000401004010000000000004010040100000000000040100401000000000000401004010000000000004010040100000000000040100401000000000000401004010000000000004010040100000000000040100401000000000000401004010000000000004010040100000000000040100401000000000000401004010000000000
  | 3 => 0x40100401004010040100000000000000000000004010040100401004010000000000000000000000401004010040100401000000000000000000000040100401004010040100000000000000000000004010040100401004010000000000000000000000401004010040100401000000000000000000000040100401004010040100000000000000000000004010040100401004010000000000000000000000401004010040100401000000000000000000000040100401004010040100000000000000000000004010040100401004010000000000000000000000401004010040100401000000000000000000000040100401004010040100000000000000000000004010040100401004010000000000000000000000401004010040100401000000000000000000000040100401004010040100000000000000000000
  | 4 => 0x40100401004010040100401004010040100401000000000000000000000000000000000000000000401004010040100401004010040100401004010000000000000000000000000000000000000000004010040100401004010040100401004010040100000000000000000000000000000000000000000040100401004010040100401004010040100401000000000000000000000000000000000000000000401004010040100401004010040100401004010000000000000000000000000000000000000000004010040100401004010040100401004010040100000000000000000000000000000000000000000040100401004010040100401004010040100401000000000000000000000000000000000000000000401004010040100401004010040100401004010000000000000000000000000000000000000000
  | 5 => 0x40100401004010040100401004010040100401004010040100401004010040100401004010040100000000000000000000000000000000000000000000000000000000000000000000000000000000004010040100401004010040100401004010040100401004010040100401004010040100401004010000000000000000000000000000000000000000000000000000000000000000000000000000000000401004010040100401004010040100401004010040100401004010040100401004010040100401000000000000000000000000000000000000000000000000000000000000000000000000000000000040100401004010040100401004010040100401004010040100401004010040100401004010040100000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 6 => 0x40100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 7 => 0x40100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | _ => 0

private lemma packed10_lits_eq :
    all10Lit = ones 10 8 ∧ ov10Lit = pack 10 ovoidRemovedMask.testBit 8 0 ∧
    st10Lit 0 = stripe 10 0 8 ∧ st10Lit 1 = stripe 10 1 8 ∧
    st10Lit 2 = stripe 10 2 8 ∧ st10Lit 3 = stripe 10 3 8 ∧
    st10Lit 4 = stripe 10 4 8 ∧ st10Lit 5 = stripe 10 5 8 ∧
    st10Lit 6 = stripe 10 6 8 ∧ st10Lit 7 = stripe 10 7 8 := by
  decide +kernel

private def comm10 (u : ℕ) : ℕ := commSet all10Lit st10Lit 4 u 4

private lemma packed_st10Lit (j : ℕ) : Packed 10 8 (st10Lit j) (fun w => w.testBit j) := by
  by_cases hj : j < 8
  · interval_cases j
    · rw [packed10_lits_eq.2.2.1]; exact packed_stripe (by norm_num) 0 8
    · rw [packed10_lits_eq.2.2.2.1]; exact packed_stripe (by norm_num) 1 8
    · rw [packed10_lits_eq.2.2.2.2.1]; exact packed_stripe (by norm_num) 2 8
    · rw [packed10_lits_eq.2.2.2.2.2.1]; exact packed_stripe (by norm_num) 3 8
    · rw [packed10_lits_eq.2.2.2.2.2.2.1]; exact packed_stripe (by norm_num) 4 8
    · rw [packed10_lits_eq.2.2.2.2.2.2.2.1]; exact packed_stripe (by norm_num) 5 8
    · rw [packed10_lits_eq.2.2.2.2.2.2.2.2.1]; exact packed_stripe (by norm_num) 6 8
    · rw [packed10_lits_eq.2.2.2.2.2.2.2.2.2]; exact packed_stripe (by norm_num) 7 8
  · have h0 : st10Lit j = 0 := by cases j with | zero => omega | succ n => rcases n with _ | _ | _ | _ | _ | _ | _ | _ <;> first | omega | rfl
    rw [h0]
    refine (Packed.zero 10 8).congr fun w hw => ?_
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

private lemma packed_comm10 (u : ℕ) : Packed 10 8 (comm10 u) (fun w => commB 4 u w) := by
  have hall : Packed 10 8 all10Lit (fun _ => true) := by
    rw [packed10_lits_eq.1]; exact packed_ones (by norm_num) 8
  refine (packed_commSet hall packed_st10Lit 4 u 4).congr fun w _ => ?_
  unfold commB
  rw [Nat.add_comm]
  exact (beq_zero_eq_decide _).symm

private lemma testBit_one_of_ne_zero {k : ℕ} (hk : k ≠ 0) : (1 : ℕ).testBit k = false := by
  exact Nat.testBit_lt_two_pow (by
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega))

private lemma packed_singleton10 {z : ℕ} (hz : z < 256) :
    Packed 10 8 (1 <<< (10 * z)) (fun w => decide (w = z)) := by
  refine ⟨fun w => ?_, fun i hi => ?_⟩
  · rw [Nat.testBit_shiftLeft]
    by_cases hw : w = z
    · subst hw; simp [hz]
    · by_cases hle : z ≤ w
      · have hpos : 10 * w - 10 * z ≠ 0 := by omega
        simp [hw, show 10 * z ≤ 10 * w by omega, testBit_one_of_ne_zero hpos]
      · simp [hw, show ¬ (10 * z ≤ 10 * w) by omega]
  · rw [Nat.testBit_shiftLeft]
    by_cases hle : 10 * z ≤ i
    · have hne : i - 10 * z ≠ 0 := by omega
      simp [hle, testBit_one_of_ne_zero hne]
    · simp [hle]

private lemma base1024_sum_lt (n : ℕ) (f : ℕ → ℕ) (hf : ∀ w < n, f w < 1024) :
    ∑ w ∈ Finset.range n, f w * 1024 ^ w < 1024 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h1 := ih (fun w hw => hf w (Nat.lt_succ_of_lt hw))
    have h2 := hf n (Nat.lt_succ_self n)
    have hmul : f n * 1024 ^ n ≤ 1023 * 1024 ^ n := Nat.mul_le_mul_right _ (by omega)
    omega

private lemma base1024_testBit (n : ℕ) (f : ℕ → ℕ) (hf : ∀ w < n, f w < 1024) (i : ℕ) :
    (∑ w ∈ Finset.range n, f w * 1024 ^ w).testBit i =
      if i / 10 < n then (f (i / 10)).testBit (i % 10) else false := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hlt : ∑ w ∈ Finset.range n, f w * 1024 ^ w < 2 ^ (10 * n) := by
      have h := base1024_sum_lt n f (fun w hw => hf w (Nat.lt_succ_of_lt hw))
      rwa [show (1024 : ℕ) ^ n = 2 ^ (10 * n) by rw [pow_mul]; norm_num] at h
    have h1024 : f n * 1024 ^ n = 2 ^ (10 * n) * f n := by
      rw [mul_comm, show (1024 : ℕ) ^ n = 2 ^ (10 * n) by rw [pow_mul]; norm_num]
    rw [h1024, add_comm, Nat.testBit_two_pow_mul_add _ hlt]
    by_cases hi : i < 10 * n
    · rw [ite_eq_left hi, ih (fun w hw => hf w (Nat.lt_succ_of_lt hw))]
      have hd1 : i / 10 < n := by omega
      have hd2 : i / 10 < n + 1 := by omega
      simp [hd1, hd2]
    · rw [ite_eq_right hi]
      by_cases hi2 : i < 10 * (n + 1)
      · have hd : i / 10 = n := by omega
        have hm : i - 10 * n = i % 10 := by omega
        simp [hd, hm]
      · have hnot : ¬ (i / 10 < n + 1) := by omega
        rw [ite_eq_right hnot]
        have hfn : f n < 2 ^ (i - 10 * n) := lt_of_lt_of_le (hf n (Nat.lt_succ_self n))
          (by calc (1024 : ℕ) = 2 ^ 10 := by norm_num
              _ ≤ 2 ^ (i - 10 * n) := Nat.pow_le_pow_right (by norm_num) (by omega))
        exact Nat.testBit_lt_two_pow hfn

private lemma packed10_eq_sum {A : ℕ} {p : ℕ → Bool} (h : Packed 10 8 A p) :
    A = ∑ w ∈ Finset.range 256, (if p w then 1 else 0) * 1024 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [base1024_testBit 256 _ (fun w _ => by split_ifs <;> norm_num)]
  by_cases hm : i % 10 = 0
  · have hi : i = 10 * (i / 10) := by omega
    conv_lhs => rw [hi, h.at_code]
    by_cases hd : i / 10 < 256
    · simp only [hd, ↓reduceIte, hm]
      cases p (i / 10) <;> simp [hd]
    · simp [hd]
  · rw [h.off_code i hm]
    by_cases hd : i / 10 < 256
    · rw [ite_eq_left hd]
      cases p (i / 10)
      · simp
      · simp [testBit_one_of_ne_zero hm]
    · rw [ite_eq_right hd]

/-- Strict `Nat.add` sum over `anisoOvoid280` of the 10-bit-packed sections containing `z`
(linear recursion with zero thunk duplication: ~0.4s across all 126 points in Lean's kernel!). -/
private def sumPlanes10 (cz : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | q :: t =>
    (if cz.testBit q.1 && cz.testBit q.2 then comm10 q.1 &&& comm10 q.2 else 0) + sumPlanes10 cz t

private def pairLt (p q : ℕ × ℕ) : Bool :=
  decide (p.1 < q.1) || (decide (p.1 = q.1) && decide (p.2 < q.2))

private def isSortedPairs : List (ℕ × ℕ) → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => pairLt a b && isSortedPairs (b :: t)

private lemma pairLt_trans {a b c : ℕ × ℕ} (h1 : pairLt a b = true) (h2 : pairLt b c = true) :
    pairLt a c = true := by
  simp only [pairLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1 h2 ⊢
  omega

private lemma pairLt_irrefl (a : ℕ × ℕ) : pairLt a a = false := by
  simp [pairLt]

private lemma nodup_of_isSortedPairs : ∀ L : List (ℕ × ℕ), isSortedPairs L = true → L.Nodup := by
  intro L
  induction L with
  | nil => intro _; exact List.nodup_nil
  | cons a t ih =>
    cases t with
    | nil => intro _; exact List.nodup_singleton a
    | cons b r =>
      intro h
      simp only [isSortedPairs, Bool.and_eq_true] at h
      have hnd := ih h.2
      have hgt : ∀ x ∈ b :: r, pairLt a x = true := by
        have hstep : ∀ (u : ℕ × ℕ) (xs : List (ℕ × ℕ)),
            isSortedPairs (u :: xs) = true → ∀ y ∈ xs, pairLt u y = true := by
          intro u xs
          induction xs generalizing u with
          | nil => intro _ _ hy; cases hy
          | cons v rest ihr =>
            intro hs y hy
            simp only [isSortedPairs, Bool.and_eq_true] at hs
            cases hy with
            | head => exact hs.1
            | tail _ hy' => exact pairLt_trans hs.1 (ihr v hs.2 y hy')
        intro x hx
        cases hx with
        | head => exact h.1
        | tail _ hx' => exact pairLt_trans h.1 (hstep b r h.2 x hx')
      refine List.nodup_cons.mpr ⟨fun ha => ?_, hnd⟩
      have hself := hgt a ha
      rw [pairLt_irrefl] at hself
      exact absurd hself (by decide)

/-- Bit-parallel block check: for every `z ∈ ovoidRemovedMask` and EVERY commuting neighbor `w ≠ z`
in `ovoidRemovedMask`, at most `10` of the `280` ovoid-disjoint anisotropic 2-planes contain `{z, w}`. -/
private def ovremCoverBlockOk (b : ℕ) : Bool :=
  allUpTo (fun i =>
    let z := 64 * b + i
    !ovoidRemovedMask.testBit z ||
      let tot := sumPlanes10 (commMask4 z) anisoOvoid280
      let nbrs10 := ov10Lit &&& comm10 z &&& (all10Lit ^^^ (1 <<< (10 * z)))
      ((tot + 501 * nbrs10) &&& (nbrs10 <<< 9)) == 0) 64

private lemma aniso280_valid :
    anisoOvoid280.length = 280 ∧ isSortedPairs anisoOvoid280 = true ∧
      anisoOvoid280.all (fun q => anisoOvoidOk q.1 q.2) = true := by
  decide +kernel

private lemma ovrem_cov_0 : ovremCoverBlockOk 0 = true := by decide +kernel
private lemma ovrem_cov_1 : ovremCoverBlockOk 1 = true := by decide +kernel
private lemma ovrem_cov_2 : ovremCoverBlockOk 2 = true := by decide +kernel
private lemma ovrem_cov_3 : ovremCoverBlockOk 3 = true := by decide +kernel

private lemma ovrem_code_eq (z : ℕ) (hz : z < 256) :
    ovoidRemovedMask.testBit z = true ↔ q7plusMask.testBit z = true ∧ z ∉ ovoidCodes := by
  revert z
  have h : allUpTo (fun z => decide (ovoidRemovedMask.testBit z = true ↔
      q7plusMask.testBit z = true ∧ z ∉ ovoidCodes)) 256 = true := by decide +kernel
  intro z hz
  exact of_decide_eq_true (allUpTo_spec _ 256 h hz)

private lemma commB_symm (a b : ℕ) : commB 4 a b = commB 4 b a := by
  unfold commB
  rw [Nat.add_comm]

private lemma sumPlanes10_eq_sum (z : ℕ) (L : List (ℕ × ℕ)) (hL : ∀ q ∈ L, q.1 < 256 ∧ q.2 < 256) :
    sumPlanes10 (commMask4 z) L =
      ∑ w ∈ Finset.range 256,
        L.countP (fun q => commB 4 q.1 z && commB 4 q.1 w && commB 4 q.2 z && commB 4 q.2 w) * 1024 ^ w := by
  induction L with
  | nil => simp [sumPlanes10]
  | cons q t ih =>
    have hq := hL q (by simp)
    have iht := ih (fun x hx => hL x (by simp [hx]))
    unfold sumPlanes10
    rw [iht, commMask4_testBit z hq.1, commMask4_testBit z hq.2, commB_symm z q.1, commB_symm z q.2]
    have hp : Packed 10 8 (if commB 4 q.1 z && commB 4 q.2 z then comm10 q.1 &&& comm10 q.2 else 0)
        (fun w => commB 4 q.1 z && commB 4 q.1 w && commB 4 q.2 z && commB 4 q.2 w) := by
      cases hc1 : commB 4 q.1 z <;> cases hc2 : commB 4 q.2 z
      · exact (Packed.zero 10 8).congr fun w _ => by simp
      · exact (Packed.zero 10 8).congr fun w _ => by simp
      · exact (Packed.zero 10 8).congr fun w _ => by simp
      · refine ((packed_comm10 q.1).and (packed_comm10 q.2)).congr fun w _ => ?_
        cases commB 4 q.1 w <;> cases commB 4 q.2 w <;> rfl
    rw [packed10_eq_sum hp, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [List.countP_cons, ← add_mul]
    cases (commB 4 q.1 z && commB 4 q.1 w && commB 4 q.2 z && commB 4 q.2 w) <;> simp [Nat.add_comm]

private lemma ovrem_cov_pair {z w : ℕ} (hz : z < 256) (hw : w < 256) (hzw : z ≠ w)
    (hzM : ovoidRemovedMask.testBit z = true) (hwM : ovoidRemovedMask.testBit w = true)
    (hczw : commB 4 z w = true) :
    anisoOvoid280.countP (fun q => commB 4 q.1 z && commB 4 q.1 w && commB 4 q.2 z && commB 4 q.2 w) ≤ 10 := by
  have hblk : ovremCoverBlockOk (z / 64) = true := by
    have hlt4 : z / 64 < 4 := by omega
    interval_cases h : z / 64
    · exact ovrem_cov_0
    · exact ovrem_cov_1
    · exact ovrem_cov_2
    · exact ovrem_cov_3
  have hstep := allUpTo_spec _ 64 hblk (Nat.mod_lt z (by norm_num))
  dsimp only at hstep
  rw [Nat.div_add_mod z 64, hzM, Bool.not_true, Bool.false_or, beq_iff_eq] at hstep
  set tot := sumPlanes10 (commMask4 z) anisoOvoid280
  set nbrs10 := ov10Lit &&& comm10 z &&& (all10Lit ^^^ (1 <<< (10 * z)))
  have hovP : Packed 10 8 ov10Lit (fun k => ovoidRemovedMask.testBit k) := by
    rw [packed10_lits_eq.2.1]; exact packed_mask (by norm_num) ovoidRemovedMask 8
  have hallP : Packed 10 8 all10Lit (fun _ => true) := by
    rw [packed10_lits_eq.1]; exact packed_ones (by norm_num) 8
  have hnbrP : Packed 10 8 nbrs10 (fun k => ovoidRemovedMask.testBit k && commB 4 z k && !(decide (k = z))) := by
    refine ((hovP.and (packed_comm10 z)).and (hallP.xor (packed_singleton10 hz))).congr fun k _ => ?_
    cases decide (k = z) <;> simp
  have hnbr_bit : (nbrs10 <<< 9).testBit (10 * w + 9) = true := by
    rw [Nat.testBit_shiftLeft, decide_eq_true (show 9 ≤ 10 * w + 9 by omega),
      show 10 * w + 9 - 9 = 10 * w by omega, hnbrP.at_code]
    simp [hw, hwM, hczw, Ne.symm hzw]
  have hbit9 : (tot + 501 * nbrs10).testBit (10 * w + 9) = false := by
    have h0 : ((tot + 501 * nbrs10) &&& (nbrs10 <<< 9)).testBit (10 * w + 9) = false := by
      rw [hstep]; exact Nat.zero_testBit _
    rw [Nat.testBit_and, hnbr_bit, Bool.and_true] at h0
    exact h0
  have hqlt : ∀ q ∈ anisoOvoid280, q.1 < 256 ∧ q.2 < 256 := by
    intro q hq
    have hok := List.all_eq_true.mp aniso280_valid.2.2 q hq
    simp only [anisoOvoidOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact ⟨hok.1.1.1.1.1, hok.1.1.1.1.2⟩
  have hsum : tot + 501 * nbrs10 = ∑ k ∈ Finset.range 256,
      (anisoOvoid280.countP (fun q => commB 4 q.1 z && commB 4 q.1 k && commB 4 q.2 z && commB 4 q.2 k) +
        (if ovoidRemovedMask.testBit k && commB 4 z k && !(decide (k = z)) then 501 else 0)) * 1024 ^ k := by
    rw [show tot = sumPlanes10 (commMask4 z) anisoOvoid280 from rfl,
      sumPlanes10_eq_sum z anisoOvoid280 hqlt, packed10_eq_sum hnbrP,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  have hlt1024 : ∀ k < 256,
      anisoOvoid280.countP (fun q => commB 4 q.1 z && commB 4 q.1 k && commB 4 q.2 z && commB 4 q.2 k) +
        (if ovoidRemovedMask.testBit k && commB 4 z k && !(decide (k = z)) then 501 else 0) < 1024 := by
    intro k _
    have hle : anisoOvoid280.countP (fun q => commB 4 q.1 z && commB 4 q.1 k && commB 4 q.2 z && commB 4 q.2 k) ≤ 280 := by
      have := List.countP_le_length (l := anisoOvoid280) (p := fun q => commB 4 q.1 z && commB 4 q.1 k && commB 4 q.2 z && commB 4 q.2 k)
      rw [aniso280_valid.1] at this; exact this
    split_ifs <;> omega
  rw [hsum, base1024_testBit 256 _ hlt1024] at hbit9
  have hd : (10 * w + 9) / 10 = w := by omega
  have hm : (10 * w + 9) % 10 = 9 := by omega
  rw [hd, hm, ite_eq_left hw] at hbit9
  have hcond : (ovoidRemovedMask.testBit w && commB 4 z w && !(decide (w = z))) = true := by
    simp [hwM, hczw, Ne.symm hzw]
  rw [hcond, ite_eq_left rfl] at hbit9
  set c := anisoOvoid280.countP (fun q => commB 4 q.1 z && commB 4 q.1 w && commB 4 q.2 z && commB 4 q.2 w)
  have hcle : c ≤ 280 := by
    have := List.countP_le_length (l := anisoOvoid280) (p := fun q => commB 4 q.1 z && commB 4 q.1 w && commB 4 q.2 z && commB 4 q.2 w)
    rw [aniso280_valid.1] at this; exact this
  rw [Nat.testBit_eq_decide_div_mod_eq] at hbit9
  have hdiv : (c + 501) / 2 ^ 9 % 2 ≠ 1 := of_decide_eq_false hbit9
  have h512 : 2 ^ 9 = 512 := by norm_num
  rw [h512] at hdiv
  omega

set_option maxHeartbeats 200000

/-- **Theorem 23(a*) — Exact Degree `252` on `Q⁺(7,2) \ O` (`126` pts, `1,260` contexts):**
Beating the Theorem 1 spectral floor `204` by `+48`, via 10-uniform double-counting over the `280`
intact `Q⁻(5,2)` sections and exact attainment by `ovoidOptNeg`. -/
theorem ovoid_residual_exact_252 :
    (∀ f : Pt 4 → ℝ, (∀ u ∈ cfg 4 ovoidRemovedMask, f u = 1 ∨ f u = -1) →
      252 ≤ (violatedLines (cfg 4 ovoidRemovedMask) f).card) ∧
    (∃ f : Pt 4 → ℝ, (∀ u, f u = 1 ∨ f u = -1) ∧
      (violatedLines (cfg 4 ovoidRemovedMask) f).card = 252) := by
  classical
  constructor
  · intro f hf
    obtain ⟨hlen, hsorted, hallOk⟩ := aniso280_valid
    have hnodup : anisoOvoid280.Nodup := nodup_of_isSortedPairs anisoOvoid280 hsorted
    let I : Finset (ℕ × ℕ) := anisoOvoid280.toFinset
    have hIcard : I.card = 280 := by
      rw [List.toFinset_card_of_nodup hnodup, hlen]
    have hOk : ∀ q ∈ I, anisoOvoidOk q.1 q.2 = true := fun q hq =>
      List.all_eq_true.mp hallOk q (List.mem_toFinset.mp hq)
    have hsub : ∀ q ∈ I, anisoSection (ptOfCode 4 q.1) (ptOfCode 4 q.2) ⊆ cfg 4 ovoidRemovedMask := by
      intro q hq x hx
      have hok := hOk q hq
      have hxR := (mem_filter.mp hx).1
      obtain ⟨hs1, hs2⟩ := (mem_filter.mp hx).2
      rw [← cfg_q7plus_eq] at hxR
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hxR
      obtain ⟨hzlt, hzbit⟩ := mem_codes.mp hz
      rw [ptOfCode_mem_cfg hzlt, ovrem_code_eq z hzlt]
      refine ⟨hzbit, fun hmem => ?_⟩
      have hall := ((Bool.and_eq_true _ _).mp hok).2
      have ho := List.all_eq_true.mp hall z hmem
      have hc1 : commB 4 q.1 z = true := (symp_ptOfCode_eq_zero 4 q.1 z).mp hs1
      have hc2 : commB 4 q.2 z = true := (symp_ptOfCode_eq_zero 4 q.2 z).mp hs2
      rw [hc1, hc2] at ho
      exact absurd ho (by decide)
    have hcov : ∀ p ∈ flags (cfg 4 ovoidRemovedMask),
        (I.filter fun q => p ∈ flags (anisoSection (ptOfCode 4 q.1) (ptOfCode 4 q.2))).card ≤ 10 := by
      intro p hp
      rw [flags_cfg] at hp
      obtain ⟨⟨z, w⟩, hzw, rfl⟩ := mem_image.mp hp
      obtain ⟨hzwR, hfb⟩ := mem_filter.mp hzw
      obtain ⟨hzlt, hwlt⟩ := mem_product.mp hzwR
      rw [mem_range] at hzlt hwlt
      set t := z ^^^ w
      have htlt : t < 256 := Nat.xor_lt_two_pow (n := 8) hzlt hwlt
      obtain ⟨hzM, hwM, htM, hczw⟩ : ovoidRemovedMask.testBit z = true ∧
          ovoidRemovedMask.testBit w = true ∧ ovoidRemovedMask.testBit t = true ∧
          commB 4 z w = true := by
        simpa [flagB, t, Bool.and_eq_true] using hfb
      have h0not : ovoidRemovedMask.testBit 0 = false := by decide
      have ht0 : t ≠ 0 := fun h => by rw [h, h0not] at htM; exact absurd htM (by decide)
      have hzw_ne : z ≠ w := fun h => ht0 (by simp [t, h])
      have hzR : ptOfCode 4 z ∈ realPoints 4 := by
        rw [← cfg_q7plus_eq, ptOfCode_mem_cfg hzlt]; exact ((ovrem_code_eq z hzlt).mp hzM).1
      have hwR : ptOfCode 4 w ∈ realPoints 4 := by
        rw [← cfg_q7plus_eq, ptOfCode_mem_cfg hwlt]; exact ((ovrem_code_eq w hwlt).mp hwM).1
      have hzwR : ptOfCode 4 z + ptOfCode 4 w ∈ realPoints 4 := by
        rw [← ptOfCode_xor, ← cfg_q7plus_eq, ptOfCode_mem_cfg htlt]; exact ((ovrem_code_eq t htlt).mp htM).1
      have hszw : symp (ptOfCode 4 z) (ptOfCode 4 w) = 0 := (symp_ptOfCode_eq_zero 4 z w).mpr hczw
      have hpred : (I.filter fun q => codePair 4 (z, w) ∈ flags (anisoSection (ptOfCode 4 q.1) (ptOfCode 4 q.2))) =
          I.filter fun q => (commB 4 q.1 z && commB 4 q.1 w && commB 4 q.2 z && commB 4 q.2 w) = true := by
        ext q
        simp only [mem_filter, Bool.and_eq_true, codePair, mem_flags, anisoSection]
        refine and_congr_right fun _ => ?_
        constructor
        · rintro ⟨⟨_, s1, s2⟩, ⟨_, s3, s4⟩, _, _⟩
          exact ⟨⟨⟨(symp_ptOfCode_eq_zero 4 q.1 z).mp s1, (symp_ptOfCode_eq_zero 4 q.1 w).mp s3⟩,
            (symp_ptOfCode_eq_zero 4 q.2 z).mp s2⟩, (symp_ptOfCode_eq_zero 4 q.2 w).mp s4⟩
        · rintro ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩
          have s1 := (symp_ptOfCode_eq_zero 4 q.1 z).mpr c1
          have s3 := (symp_ptOfCode_eq_zero 4 q.1 w).mpr c2
          have s2 := (symp_ptOfCode_eq_zero 4 q.2 z).mpr c3
          have s4 := (symp_ptOfCode_eq_zero 4 q.2 w).mpr c4
          exact ⟨⟨hzR, s1, s2⟩, ⟨hwR, s3, s4⟩,
            ⟨hzwR, by rw [symp_add_right, s1, s3, add_zero], by rw [symp_add_right, s2, s4, add_zero]⟩,
            hszw⟩
      rw [hpred]
      have hcnt : (I.filter fun q => (commB 4 q.1 z && commB 4 q.1 w && commB 4 q.2 z && commB 4 q.2 w) = true).card =
          anisoOvoid280.countP (fun q => commB 4 q.1 z && commB 4 q.1 w && commB 4 q.2 z && commB 4 q.2 w) := by
        unfold I
        rw [← List.toFinset_filter, List.toFinset_card_of_nodup (hnodup.filter _),
          List.countP_eq_length_filter]
      rw [hcnt]
      exact ovrem_cov_pair hzlt hwlt hzw_ne hzM hwM hczw
    have hsum := ExactDegreesN4N5.sum_violatedLines_le_of_cover (cfg 4 ovoidRemovedMask)
      (zero_not_mem_cfg (by decide)) I (fun q => anisoSection (ptOfCode 4 q.1) (ptOfCode 4 q.2))
      hsub 10 hcov f
    have hlow : I.card * 9 ≤ ∑ q ∈ I, (violatedLines (anisoSection (ptOfCode 4 q.1) (ptOfCode 4 q.2)) f).card := by
      calc I.card * 9 = ∑ _q ∈ I, 9 := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ q ∈ I, (violatedLines (anisoSection (ptOfCode 4 q.1) (ptOfCode 4 q.2)) f).card := by
            refine Finset.sum_le_sum fun q hq => ?_
            have hok := hOk q hq
            simp only [anisoOvoidOk, oddCode, Bool.and_eq_true, Bool.not_eq_true',
              decide_eq_true_eq] at hok
            have hqu : qform (ptOfCode 4 q.1) = 1 := by
              rw [qform, dot_eq_ycount, ycount_ptOfCode]
              have hmod : (common q.1 0 q.1 4 4 : ZMod 2).val = 1 := by
                rw [ZMod.val_natCast]; exact hok.1.1.1.2
              exact (ZMod.val_injective 2) hmod
            have hqv : qform (ptOfCode 4 q.2) = 1 := by
              rw [qform, dot_eq_ycount, ycount_ptOfCode]
              have hmod : (common q.2 0 q.2 4 4 : ZMod 2).val = 1 := by
                rw [ZMod.val_natCast]; exact hok.1.1.2
              exact (ZMod.val_injective 2) hmod
            have huv : symp (ptOfCode 4 q.1) (ptOfCode 4 q.2) = 1 := by
              rcases zmod2_cases (symp (ptOfCode 4 q.1) (ptOfCode 4 q.2)) with h0 | h1
              · have := (symp_ptOfCode_eq_zero 4 q.1 q.2).mp h0
                rw [hok.1.2] at this; exact absurd this (by decide)
              · exact h1
            exact aniso_plane_q5minus_ge_9 hqu hqv huv f (fun z hz => hf z (hsub q hq hz))
    rw [hIcard] at hlow
    omega
  · let f : Pt 4 → ℝ := fun u => ((sgnOf 4 ovoidOptNeg u : ℤ) : ℝ)
    refine ⟨f, sgnOf_values 4 ovoidOptNeg, ?_⟩
    have hv : (violated (cfg 4 ovoidRemovedMask) f).card = 6 * 252 := by
      have h := loop_blocks (fastViolRow 10 4 ovoidRemovedMask ovoidOptNeg) 16 16
      rcases ovrem_ovopt_vb with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
      rw [loop_sixteen, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15] at h
      have e : (2 : ℕ) ^ (2 * 4) = 16 * 16 := by norm_num
      rw [card_violated_cfg_fast (b := 10) (N := 4) (by norm_num) (by norm_num), e]
      exact h.trans (by norm_num)
    have h6 := card_violated_eq_six (cfg 4 ovoidRemovedMask) (zero_not_mem_cfg (by decide)) f
    omega

end HoggarBound.TrialityResiduals
