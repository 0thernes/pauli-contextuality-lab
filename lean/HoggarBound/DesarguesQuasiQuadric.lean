/-
Hoggar Bound Lab — Theorem 25 (Desargues `(10_3)`, Universal `[DHOP]` Fiber-Flip Family `S_ε`,
Ovoid Context Parabola, Decoupling of `red_8(XIXX)`, and Sharp Brackets on `K_95`, `K_103`,
`S_B^(4)`, and Metod Saniga's Augmented Quasi-Quadric `S_B^+`).

Motivated by Metod Saniga's 27 Nov 2026 email discovering the Desargues `(10_3)` configuration
in the `X`-solid of `S_B ∩ Q⁺(7,2)` and asking whether the augmented 143-point configuration
`S_B^+ = S_B ∪ red_8(XIXX)` plays a special role.

Main results (zero `sorry`, zero `admit`, zero `native_decide`, strictly
`[propext, Classical.choice, Quot.sound]`):
* `fiberFlip_hyperplane_card`  : **All-`N` (`N ≥ 2`) Universal `[DHOP]` Fiber-Flip Theorem**:
  for EVERY function `ε : Vec N → ZMod 2` (all `2^(2^N - 1)` fiber-flip sets; `32,768` at `N = 4`)
  and EVERY `u ∈ allPoints N`,
  `4 · |fiberFlipSet N ε ∩ u⊥| + 4 = 4^N + (if u ∈ fiberFlipSet N ε then 2·2^N else 0)`
  (yielding exact `71/63` hyperplane invariance at `N = 4` for all `32,768` sets).
* `desargues_five_frame_and_10_3` : Exact verification of the 5-frame
  `E = {IXII, XXII, XIXI, XIIX, XIXX}` (XOR `0`, every 4-subset a basis of `𝔽₂⁴`) and the
  10-point, 10-line 3-regular Desargues `(10_3)` configuration in `S_B ∩ Q⁺(7,2)`.
* `ovoid_context_parabola`     : Exact parabola `L(S_T) = 1575 - 256k + 32k²` across all 32 subsets
  `T ⊆ E`, with unique minimum `1,063` at `k = 4` (`S_B^(4)`) and collinear 3-flip negative control
  (`967 ≠ 1,095`).
* `sb_aug_structural_properties` : Exact decoupling of `red_8(XIXX)` from `S_B \ Q⁺(7,2)`
  (`124 = 28 + 96` new contexts, `0` cross-contexts to `S_B \ Q⁺`), full `71/71` containment of
  the tangent hyperplane `Q⁺(7,2) ∩ IZZZ⊥` in `K_103`, exact 256-extension minimum `+52`
  (attained uniquely up to global flip on `red_8`), constant external hyperplane count
  `HP_out(S_B^+) = 67` across all `112` external points, and Theorem 4 non-squareness
  `15 · 143 = 2,145 ≠ k²`.
* `disjoint_mp_grids_lower_bound` & sharp brackets (combining pairwise-line-disjoint Mermin–Peres
  grid packings with exact attaining sign witnesses):
  - `k95_bounds_53_55`      : `53 ≤ d(K_95) ≤ 55` (floor `39`, gap `2`)
  - `k103_bounds_87_107`    : `87 ≤ d(K_103) ≤ 107` (floor `65`)
  - `sb4flip_bounds_112_123`: `112 ≤ d(S_B^(4)) ≤ 123` (floor `59`, strictly breaking saturation!)
  - `sb_aug_bounds_121_127` : `121 ≤ d(S_B^+) ≤ 127` (floor `95`, gap `6`).
-/
import HoggarBound.TrialityResiduals

open Finset Matrix HoggarBound

namespace HoggarBound.DesarguesQuasiQuadric

/-! ### Part 1. All-`N` (`N ≥ 2`) Universal `[DHOP]` Fiber-Flip Two-Character Theorem -/

/-- The `[DHOP]` fiber-flip configuration `S_ε` on `N` qubits for an arbitrary parity function
`ε : Vec N → ZMod 2`: all pure-`Z` observables (`a = 0, c ≠ 0`) together with the affine hyperplane
`{c : c · a = ε a}` in every nonzero `X`-fiber `a ≠ 0`. -/
def fiberFlipSet (N : ℕ) (ε : Vec N → ZMod 2) : Finset (Pt N) :=
  (allPoints N).filter fun u => u.1 = 0 ∨ u.2 ⬝ᵥ u.1 = ε u.1

private lemma sum_chi_vec_comm {N : ℕ} (v : Vec N) :
    ∑ c : Vec N, chi c v = if v = 0 then (2 : ℂ) ^ N else 0 := by
  have : ∀ c : Vec N, chi c v = chi v c := fun c => by unfold chi; rw [dotProduct_comm]
  simp_rw [this]
  exact sum_chi v

private lemma card_vec_dot_eq {N : ℕ} {a : Vec N} (ha : a ≠ 0) (t : ZMod 2) :
    2 * (univ.filter fun c : Vec N => c ⬝ᵥ a = t).card = 2 ^ N := by
  have hind : ∀ c : Vec N, (if c ⬝ᵥ a = t then (1 : ℂ) else 0) = (1 + eps t * chi c a) / 2 := by
    intro c
    have h1 : (if c ⬝ᵥ a = t then (1 : ℂ) else 0) = (if c ⬝ᵥ a + t = 0 then (1 : ℂ) else 0) := by
      congr 1; apply propext
      constructor
      · rintro rfl; exact zmod2_add_self _
      · intro h; rcases zmod2_cases (c ⬝ᵥ a) with h1 | h1 <;> rcases zmod2_cases t with h2 | h2 <;>
          simp_all
    rw [h1, indicator_eq, eps_add]; unfold chi; ring
  have hC : (((univ.filter fun c : Vec N => c ⬝ᵥ a = t).card : ℕ) : ℂ) = (2 : ℂ) ^ N / 2 := by
    rw [Finset.card_filter]; push_cast
    simp_rw [hind, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_chi_vec_comm a, ite_eq_right ha, mul_zero, add_zero, Finset.sum_const, Finset.card_univ,
      card_vec, nsmul_eq_mul, mul_one]
    push_cast; rfl
  have h2 : ((2 * (univ.filter fun c : Vec N => c ⬝ᵥ a = t).card : ℕ) : ℂ) = ((2 ^ N : ℕ) : ℂ) := by
    push_cast; rw [hC]; ring
  exact_mod_cast h2

private lemma card_vec_dot_pair_eq {N : ℕ} {a x : Vec N} (ha : a ≠ 0) (hx : x ≠ 0) (hax : a ≠ x)
    (t1 t2 : ZMod 2) :
    4 * (univ.filter fun c : Vec N => c ⬝ᵥ a = t1 ∧ c ⬝ᵥ x = t2).card = 2 ^ N := by
  have hax0 : a + x ≠ 0 := fun h => hax (by
    calc a = a + (x + x) := by rw [vec_add_self, add_zero]
      _ = (a + x) + x := by abel
      _ = x := by rw [h, zero_add])
  have hind1 : ∀ (v : Vec N) (t : ZMod 2) (c : Vec N),
      (if c ⬝ᵥ v = t then (1 : ℂ) else 0) = (1 + eps t * chi c v) / 2 := by
    intro v t c
    have h1 : (if c ⬝ᵥ v = t then (1 : ℂ) else 0) = (if c ⬝ᵥ v + t = 0 then (1 : ℂ) else 0) := by
      congr 1; apply propext
      constructor
      · rintro rfl; exact zmod2_add_self _
      · intro h; rcases zmod2_cases (c ⬝ᵥ v) with h1 | h1 <;> rcases zmod2_cases t with h2 | h2 <;>
          simp_all
    rw [h1, indicator_eq, eps_add]; unfold chi; ring
  have hind : ∀ c : Vec N, (if c ⬝ᵥ a = t1 ∧ c ⬝ᵥ x = t2 then (1 : ℂ) else 0) =
      (1 + eps t1 * chi c a + eps t2 * chi c x + eps t1 * eps t2 * chi c (a + x)) / 4 := by
    intro c
    have hm : (if c ⬝ᵥ a = t1 ∧ c ⬝ᵥ x = t2 then (1 : ℂ) else 0) =
        (if c ⬝ᵥ a = t1 then (1 : ℂ) else 0) * (if c ⬝ᵥ x = t2 then (1 : ℂ) else 0) := by
      by_cases c1 : c ⬝ᵥ a = t1 <;> by_cases c2 : c ⬝ᵥ x = t2 <;> simp [c1, c2]
    rw [hm, hind1 a t1 c, hind1 x t2 c, chi_add_right]; ring
  have hC : (((univ.filter fun c : Vec N => c ⬝ᵥ a = t1 ∧ c ⬝ᵥ x = t2).card : ℕ) : ℂ) = (2 : ℂ) ^ N / 4 := by
    rw [Finset.card_filter]; push_cast
    simp_rw [hind, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_chi_vec_comm a, sum_chi_vec_comm x, sum_chi_vec_comm (a + x),
      ite_eq_right ha, ite_eq_right hx, ite_eq_right hax0, mul_zero, add_zero,
      Finset.sum_const, Finset.card_univ, card_vec, nsmul_eq_mul, mul_one]
    push_cast; rfl
  have h4 : ((4 * (univ.filter fun c : Vec N => c ⬝ᵥ a = t1 ∧ c ⬝ᵥ x = t2).card : ℕ) : ℂ) = ((2 ^ N : ℕ) : ℂ) := by
    push_cast; rw [hC]; ring
  exact_mod_cast h4

/-- Exact cardinality of every fiber-flip set `S_ε`: `2 · |S_ε| + 2 = 4^N + 2^N` (`135` at `N = 4`). -/
theorem fiberFlip_card (N : ℕ) (ε : Vec N → ZMod 2) :
    2 * (fiberFlipSet N ε).card + 2 = 4 ^ N + 2 ^ N := by
  have hfib : (fiberFlipSet N ε).card =
      ∑ a : Vec N, (univ.filter fun c : Vec N => (a, c) ≠ 0 ∧ (a = 0 ∨ c ⬝ᵥ a = ε a)).card := by
    rw [fiberFlipSet, allPoints]
    have heq : ((univ.erase (0 : Pt N)).filter fun u => u.1 = 0 ∨ u.2 ⬝ᵥ u.1 = ε u.1) =
        univ.filter fun u : Pt N => u ≠ 0 ∧ (u.1 = 0 ∨ u.2 ⬝ᵥ u.1 = ε u.1) := by
      ext u; simp
    rw [heq, Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.card_filter]
  rw [hfib, Finset.mul_sum, ← Finset.add_sum_erase _ _ (mem_univ (0 : Vec N))]
  have h0 : 2 * (univ.filter fun c : Vec N => ((0 : Vec N), c) ≠ 0 ∧ ((0 : Vec N) = 0 ∨ c ⬝ᵥ 0 = ε 0)).card =
      2 * (2 ^ N - 1) := by
    have heq : (univ.filter fun c : Vec N => ((0 : Vec N), c) ≠ 0 ∧ ((0 : Vec N) = 0 ∨ c ⬝ᵥ 0 = ε 0)) =
        univ.erase (0 : Vec N) := by
      ext c; simp [Prod.ext_iff]
    rw [heq, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, card_vec]
  have hrest : ∀ a ∈ univ.erase (0 : Vec N),
      2 * (univ.filter fun c : Vec N => (a, c) ≠ 0 ∧ (a = 0 ∨ c ⬝ᵥ a = ε a)).card = 2 ^ N := by
    intro a ha
    have ha0 : a ≠ 0 := Finset.ne_of_mem_erase ha
    have heq : (univ.filter fun c : Vec N => (a, c) ≠ 0 ∧ (a = 0 ∨ c ⬝ᵥ a = ε a)) =
        univ.filter fun c : Vec N => c ⬝ᵥ a = ε a := by
      ext c; simp [Prod.ext_iff, ha0]
    rw [heq]; exact card_vec_dot_eq ha0 (ε a)
  rw [h0, Finset.sum_congr rfl hrest, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, card_vec]
  have h4 : 4 ^ N = 2 ^ N * 2 ^ N := by rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
  have hpos : 1 ≤ 2 ^ N := Nat.one_le_two_pow
  rw [h4]
  zify [hpos]
  ring

/-- **All-`N` (`N ≥ 2`) Universal `[DHOP]` Fiber-Flip Two-Character Theorem:**
For EVERY `ε : Vec N → ZMod 2` and EVERY `u ∈ allPoints N`,
`4 · |fiberFlipSet N ε ∩ u⊥| + 4 = 4^N + (if u ∈ fiberFlipSet N ε then 2 · 2^N else 0)`. -/
theorem fiberFlip_hyperplane_card {N : ℕ} (hN : 2 ≤ N) (ε : Vec N → ZMod 2)
    {u : Pt N} (hu : u ∈ allPoints N) :
    4 * ((fiberFlipSet N ε).filter fun v => symp u v = 0).card + 4 =
      4 ^ N + if u ∈ fiberFlipSet N ε then 2 * 2 ^ N else 0 := by
  rcases u with ⟨x, z⟩
  have hu0 : (x, z) ≠ 0 := (mem_erase.mp hu).1
  have hfib : ((fiberFlipSet N ε).filter fun v => symp (x, z) v = 0).card =
      ∑ a : Vec N, (univ.filter fun c : Vec N =>
        (a, c) ≠ 0 ∧ (a = 0 ∨ c ⬝ᵥ a = ε a) ∧ z ⬝ᵥ a + c ⬝ᵥ x = 0).card := by
    have heq : ((fiberFlipSet N ε).filter fun v => symp (x, z) v = 0) =
        univ.filter fun v : Pt N => v ≠ 0 ∧ (v.1 = 0 ∨ v.2 ⬝ᵥ v.1 = ε v.1) ∧ z ⬝ᵥ v.1 + v.2 ⬝ᵥ x = 0 := by
      ext v
      rw [Finset.mem_filter, Finset.mem_filter, fiberFlipSet, Finset.mem_filter, allPoints,
        Finset.mem_erase]
      simp only [Finset.mem_univ, true_and, symp]
      tauto
    rw [heq, Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.card_filter]
  have h2N_ge4 : 4 ≤ 2 ^ N := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN
  have h4eq : 4 ^ N = 2 ^ N * 2 ^ N := by rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
  rw [hfib, Finset.mul_sum, ← Finset.add_sum_erase _ _ (mem_univ (0 : Vec N))]
  by_cases hx : x = 0
  · subst hx
    have hz0 : z ≠ 0 := fun h => hu0 (Prod.ext rfl h)
    have hmem : ((0 : Vec N), z) ∈ fiberFlipSet N ε :=
      mem_filter.mpr ⟨hu, Or.inl rfl⟩
    rw [ite_eq_left hmem]
    -- `a = 0` contributes all `2^N - 1` pure-`Z` points.
    have ha0 : 4 * (univ.filter fun c : Vec N =>
        ((0 : Vec N), c) ≠ 0 ∧ ((0 : Vec N) = 0 ∨ c ⬝ᵥ 0 = ε 0) ∧ z ⬝ᵥ 0 + c ⬝ᵥ 0 = 0).card =
        4 * (2 ^ N - 1) := by
      have heq : (univ.filter fun c : Vec N =>
          ((0 : Vec N), c) ≠ 0 ∧ ((0 : Vec N) = 0 ∨ c ⬝ᵥ 0 = ε 0) ∧ z ⬝ᵥ 0 + c ⬝ᵥ 0 = 0) =
          univ.erase (0 : Vec N) := by ext c; simp [Prod.ext_iff]
      rw [heq, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, card_vec]
    -- Each `a ≠ 0` contributes `2^(N-1)` if `z · a = 0`, else `0`.
    have hrest : ∀ a ∈ univ.erase (0 : Vec N),
        4 * (univ.filter fun c : Vec N => (a, c) ≠ 0 ∧ (a = 0 ∨ c ⬝ᵥ a = ε a) ∧ z ⬝ᵥ a + c ⬝ᵥ 0 = 0).card =
        if a ⬝ᵥ z = 0 then 2 * 2 ^ N else 0 := by
      intro a ha
      have ha_ne : a ≠ 0 := Finset.ne_of_mem_erase ha
      by_cases hza : a ⬝ᵥ z = 0
      · rw [ite_eq_left hza]
        have hza' : z ⬝ᵥ a = 0 := by rw [dotProduct_comm]; exact hza
        have heq : (univ.filter fun c : Vec N => (a, c) ≠ 0 ∧ (a = 0 ∨ c ⬝ᵥ a = ε a) ∧ z ⬝ᵥ a + c ⬝ᵥ 0 = 0) =
            univ.filter fun c : Vec N => c ⬝ᵥ a = ε a := by
          ext c; simp [Prod.ext_iff, ha_ne, hza']
        rw [heq]
        have := card_vec_dot_eq ha_ne (ε a); omega
      · rw [ite_eq_right hza]
        have hza' : z ⬝ᵥ a ≠ 0 := by rw [dotProduct_comm]; exact hza
        have heq : (univ.filter fun c : Vec N => (a, c) ≠ 0 ∧ (a = 0 ∨ c ⬝ᵥ a = ε a) ∧ z ⬝ᵥ a + c ⬝ᵥ 0 = 0) = ∅ := by
          ext c; simp [hza']
        rw [heq]; simp
    rw [ha0, Finset.sum_congr rfl hrest, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, smul_eq_mul]
    have hcnt : ((univ.erase (0 : Vec N)).filter fun a : Vec N => a ⬝ᵥ z = 0).card * 2 + 2 = 2 ^ N := by
      have heq : (univ.erase (0 : Vec N)).filter (fun a : Vec N => a ⬝ᵥ z = 0) =
          (univ.filter fun a : Vec N => a ⬝ᵥ z = 0).erase 0 := by ext a; simp [and_comm]
      rw [heq, Finset.card_erase_of_mem (by simp)]
      have h := card_vec_dot_eq hz0 0
      omega
    rw [h4eq]
    have h1 : 1 ≤ 2 ^ N := Nat.one_le_two_pow
    zify [h1, h2N_ge4] at hcnt ⊢
    nlinarith
  · -- Case `x ≠ 0`: split off `a = x` from `univ.erase 0`.
    -- `a = 0`: `c ≠ 0 ∧ c · x = 0`, count = `2^(N-1) - 1`.
    have ha0 : 4 * (univ.filter fun c : Vec N =>
        ((0 : Vec N), c) ≠ 0 ∧ ((0 : Vec N) = 0 ∨ c ⬝ᵥ 0 = ε 0) ∧ z ⬝ᵥ 0 + c ⬝ᵥ x = 0).card =
        2 * 2 ^ N - 4 := by
      have heq : (univ.filter fun c : Vec N =>
          ((0 : Vec N), c) ≠ 0 ∧ ((0 : Vec N) = 0 ∨ c ⬝ᵥ 0 = ε 0) ∧ z ⬝ᵥ 0 + c ⬝ᵥ x = 0) =
          (univ.filter fun c : Vec N => c ⬝ᵥ x = 0).erase 0 := by
        ext c; simp [Prod.ext_iff, and_comm]
      rw [heq, Finset.card_erase_of_mem (by simp)]
      have := card_vec_dot_eq hx 0; omega
    have hx_mem : x ∈ univ.erase (0 : Vec N) := mem_erase.mpr ⟨hx, mem_univ x⟩
    rw [ha0, ← Finset.add_sum_erase _ _ hx_mem]
    -- Fiber `a = x`: contributes `2 * 2^N` if `(x, z) ∈ fiberFlipSet N ε` (i.e. `z · x = ε x`), else `0`!
    have hxc0 : ∀ c : Vec N, (x, c) ≠ 0 := fun c h => hx (congrArg Prod.fst h)
    have hax : 4 * (univ.filter fun c : Vec N =>
        (x, c) ≠ 0 ∧ (x = 0 ∨ c ⬝ᵥ x = ε x) ∧ z ⬝ᵥ x + c ⬝ᵥ x = 0).card =
        if (x, z) ∈ fiberFlipSet N ε then 2 * 2 ^ N else 0 := by
      have hiff : (x, z) ∈ fiberFlipSet N ε ↔ z ⬝ᵥ x = ε x := by
        simp [fiberFlipSet, hu, hx]
      by_cases hm : (x, z) ∈ fiberFlipSet N ε
      · rw [ite_eq_left hm]
        have hzx : z ⬝ᵥ x = ε x := hiff.mp hm
        have heq : (univ.filter fun c : Vec N =>
            (x, c) ≠ 0 ∧ (x = 0 ∨ c ⬝ᵥ x = ε x) ∧ z ⬝ᵥ x + c ⬝ᵥ x = 0) =
            univ.filter fun c : Vec N => c ⬝ᵥ x = ε x := by
          ext c
          simp only [mem_filter, mem_univ, true_and, hx, false_or, hzx]
          constructor
          · exact fun ⟨_, hc, _⟩ => hc
          · intro hc; exact ⟨hxc0 c, hc, by rw [hc, zmod2_add_self]⟩
        rw [heq]; have := card_vec_dot_eq hx (ε x); omega
      · rw [ite_eq_right hm]
        have hzx : z ⬝ᵥ x ≠ ε x := fun h => hm (hiff.mpr h)
        have heq : (univ.filter fun c : Vec N =>
            (x, c) ≠ 0 ∧ (x = 0 ∨ c ⬝ᵥ x = ε x) ∧ z ⬝ᵥ x + c ⬝ᵥ x = 0) = ∅ := by
          ext c
          simp only [mem_filter, mem_univ, true_and, hx, false_or, notMem_empty, iff_false]
          rintro ⟨_, hc, hsum⟩
          rw [hc] at hsum
          apply hzx
          rcases zmod2_cases (z ⬝ᵥ x) with h1 | h1 <;> rcases zmod2_cases (ε x) with h2 | h2 <;>
            simp_all
        rw [heq]; simp
    -- All other `2^N - 2` fibers `a ≠ 0, a ≠ x`: each contributes `4 * (2^N / 4) = 2^N`!
    have hother : ∀ a ∈ (univ.erase (0 : Vec N)).erase x,
        4 * (univ.filter fun c : Vec N => (a, c) ≠ 0 ∧ (a = 0 ∨ c ⬝ᵥ a = ε a) ∧ z ⬝ᵥ a + c ⬝ᵥ x = 0).card =
        2 ^ N := by
      intro a ha
      have hax_ne : a ≠ x := (mem_erase.mp ha).1
      have ha_ne : a ≠ 0 := (mem_erase.mp (mem_erase.mp ha).2).1
      have hac0 : ∀ c : Vec N, (a, c) ≠ 0 := fun c h => ha_ne (congrArg Prod.fst h)
      have heq : (univ.filter fun c : Vec N => (a, c) ≠ 0 ∧ (a = 0 ∨ c ⬝ᵥ a = ε a) ∧ z ⬝ᵥ a + c ⬝ᵥ x = 0) =
          univ.filter fun c : Vec N => c ⬝ᵥ a = ε a ∧ c ⬝ᵥ x = z ⬝ᵥ a := by
        ext c
        simp only [mem_filter, mem_univ, true_and, ha_ne, false_or]
        constructor
        · rintro ⟨_, h1, h2⟩
          refine ⟨h1, ?_⟩
          rcases zmod2_cases (z ⬝ᵥ a) with hz1 | hz1 <;> rcases zmod2_cases (c ⬝ᵥ x) with hc1 | hc1 <;>
            simp_all
        · rintro ⟨h1, h2⟩
          exact ⟨hac0 c, h1, by rw [h2, zmod2_add_self]⟩
      rw [heq]
      exact card_vec_dot_pair_eq ha_ne hx hax_ne (ε a) (z ⬝ᵥ a)
    rw [hax, Finset.sum_congr rfl hother, Finset.sum_const, smul_eq_mul,
      Finset.card_erase_of_mem hx_mem, Finset.card_erase_of_mem (mem_univ _),
      Finset.card_univ, card_vec, h4eq]
    have h1 : 1 ≤ 2 ^ N := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ N - 1 := by omega
    have h4 : 4 ≤ 2 * 2 ^ N := by omega
    zify [h1, h2, h4]
    ring

/-- Concrete `N = 4` corollary: EVERY ONE of the `2^15 = 32,768` fiber-flip sets `S_ε` in `W(7,2)`
has cardinality `135` and exact `71/63` hyperplane intersections! -/
theorem fiberFlip_n4_71_63 (ε : Vec 4 → ZMod 2) :
    (fiberFlipSet 4 ε).card = 135 ∧
    ∀ u ∈ allPoints 4,
      ((fiberFlipSet 4 ε).filter fun v => symp u v = 0).card =
        if u ∈ fiberFlipSet 4 ε then 71 else 63 := by
  constructor
  · have h := fiberFlip_card 4 ε; norm_num at h; omega
  · intro u hu
    have h := fiberFlip_hyperplane_card (N := 4) (by norm_num) ε hu
    split_ifs at h ⊢ <;> norm_num at h <;> omega

/-! ### Part 2. Desargues `(10_3)`, Ovoid Context Parabola & Decoupling of `red_8(XIXX)` -/

/-- Exact bitmask of the four-qubit hyperbolic quasi-quadric `S_B` (`135` pts, `1,095` lines). -/
def sbMask : ℕ := 0xb4451eef7889d22344b5ee1f887922d34b45e1ef87892d23bbb5111f7779ddd2
/-- Optimal flat-state witness negative mask on `S_B` (`75` violations on `S_B`, `55` on `K_95`). -/
def sbNeg : ℕ := 0x20011cc01888c2204424221f001100c34244212f01010c038880111177790000
/-- Extended witness negative mask on `S_B^+` (`107` on `K_103`, `123` on `S_B^(4)`, `127` on `S_B^+`). -/
def sbExtNeg : ℕ := 0x20011cc01888e2206424221f001100c36244212f01010c038880311177790000

/-- Bitmask of `K_95 = S_B ∩ Q⁺(7,2)` (`95` pts, `635` lines). -/
def k95Mask : ℕ := 0x94411cc35881d0034491cc13885100d34941c1c385810d03999111135551ddd2
/-- Bitmask of `K_103 = K_95 ∪ red_8(XIXX)` (`103` pts, `759` lines). -/
def k103Mask : ℕ := 0x94413cc35881f0036491cc13a85100d36941c1c3a5810d03999131135551fdd2
/-- Bitmask of `S_B^(4)` (4 ovoid fibers flipped; `135` pts, `1,063` lines). -/
def sb4FlipMask : ℕ := 0x94453eef5889f22364b5ce1fa87902d36b45c1efa7890d239bb5311f5779fdd2
/-- Bitmask of Metod Saniga's augmented quasi-quadric `S_B^+ = S_B ∪ red_8(XIXX)` (`143` pts, `1,219` lines). -/
def sbAugMask : ℕ := 0xb4453eef7889f22364b5ee1fa87922d36b45e1efa7892d23bbb5311f7779fdd2

/-- The 5-frame of outliers in the `X`-solid: `E = {IXII, XXII, XIXI, XIIX, XIXX}`. -/
def fiveFrameCodes : List ℕ := [2, 3, 5, 9, 13]

/-- The 8 real points in the `XIXX` fiber (`code 13`). -/
def red8Codes : List ℕ := [13, 45, 93, 125, 157, 189, 205, 237]

/-- Bitmask of the 10-point Desargues `(10_3)` configuration in the `X`-solid (`sbMask &&& 0xfffe`). -/
def desargues10Mask : ℕ := 0xddd2

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

/-- Build the 256-bit mask of the fiber-flip configuration obtained by flipping the X-fibers in `flips`. -/
private def maskOfFlips (flips : List ℕ) : ℕ :=
  (List.range 256).foldl (fun acc u =>
    if u = 0 then acc
    else
      let a := u % 16
      let par := if a ∈ flips then 1 else 0
      if a = 0 || common u 0 u 4 4 % 2 = par then acc ||| (1 <<< u) else acc) 0

/-- Fast 4-qubit bit-parallel commutation mask (identical to `commB 4 u w` for `w < 256`). -/
private def bm4 (k : Fin 8) : ℕ :=
  match k with
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
  | 6 => 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
  | 7 => 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000

private def all256 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

private def commM4 (u : ℕ) : ℕ :=
  all256 ^^^
  (if u.testBit 0 then bm4 4 else 0) ^^^ (if u.testBit 1 then bm4 5 else 0) ^^^
  (if u.testBit 2 then bm4 6 else 0) ^^^ (if u.testBit 3 then bm4 7 else 0) ^^^
  (if u.testBit 4 then bm4 0 else 0) ^^^ (if u.testBit 5 then bm4 1 else 0) ^^^
  (if u.testBit 6 then bm4 2 else 0) ^^^ (if u.testBit 7 then bm4 3 else 0)

/-- Exact popcount of a 256-bit natural number via SWAR bit-folding (8 GMP ops). -/
private def pop256 (x : ℕ) : ℕ :=
  let m1 := 0x5555555555555555555555555555555555555555555555555555555555555555
  let m2 := 0x3333333333333333333333333333333333333333333333333333333333333333
  let m4 := 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
  let m8 := 0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
  let m16 := 0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
  let m32 := 0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff
  let m64 := 0x0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff
  let m128 := 0x00000000000000000000000000000000ffffffffffffffffffffffffffffffff
  let x := (x &&& m1) + ((x >>> 1) &&& m1)
  let x := (x &&& m2) + ((x >>> 2) &&& m2)
  let x := (x &&& m4) + ((x >>> 4) &&& m4)
  let x := (x &&& m8) + ((x >>> 8) &&& m8)
  let x := (x &&& m16) + ((x >>> 16) &&& m16)
  let x := (x &&& m32) + ((x >>> 32) &&& m32)
  let x := (x &&& m64) + ((x >>> 64) &&& m64)
  (x &&& m128) + ((x >>> 128) &&& m128)

/-- Bitmask of `m` XOR-shifted by `u` (bit `v` is set iff `m.testBit (u ^^^ v)`). -/
private def xorShift256 (m u : ℕ) : ℕ :=
  let m := if u.testBit 0 then ((m &&& bm4 0) >>> 1) ||| ((m &&& (all256 ^^^ bm4 0)) <<< 1) else m
  let m := if u.testBit 1 then ((m &&& bm4 1) >>> 2) ||| ((m &&& (all256 ^^^ bm4 1)) <<< 2) else m
  let m := if u.testBit 2 then ((m &&& bm4 2) >>> 4) ||| ((m &&& (all256 ^^^ bm4 2)) <<< 4) else m
  let m := if u.testBit 3 then ((m &&& bm4 3) >>> 8) ||| ((m &&& (all256 ^^^ bm4 3)) <<< 8) else m
  let m := if u.testBit 4 then ((m &&& bm4 4) >>> 16) ||| ((m &&& (all256 ^^^ bm4 4)) <<< 16) else m
  let m := if u.testBit 5 then ((m &&& bm4 5) >>> 32) ||| ((m &&& (all256 ^^^ bm4 5)) <<< 32) else m
  let m := if u.testBit 6 then ((m &&& bm4 6) >>> 64) ||| ((m &&& (all256 ^^^ bm4 6)) <<< 64) else m
  if u.testBit 7 then ((m &&& bm4 7) >>> 128) ||| ((m &&& (all256 ^^^ bm4 7)) <<< 128) else m

/-- Ultra-fast exact count of contexts of a 4-qubit bitmask `m` (with bit `0` clear):
`1/6` of total commuting flags `u, v, u ^^^ v ∈ m`, evaluated via bit-parallel `xorShift256` & `pop256`. -/
private def countLines (m : ℕ) : ℕ :=
  (loop (fun u =>
    if m.testBit u then
      pop256 (m &&& commM4 u &&& xorShift256 m u &&& (all256 ^^^ (1 <<< u)))
    else 0) 256) / 6

private def subsetOfFive (bits : ℕ) : List ℕ :=
  (List.range 5).filterMap fun i => if bits.testBit i then fiveFrameCodes[i]? else none

/-- **Desargues `(10_3)` & 5-Frame Theorem:**
1. The 5 outliers `E = {IXII, XXII, XIXI, XIIX, XIXX}` sum to `0` (`2 ^^^ 3 ^^^ 5 ^^^ 9 ^^^ 13 = 0`);
2. Every 4-element subset of `E` is linearly independent over `𝔽₂` (no nonempty proper subset sums to `0`);
3. The 10 pairwise XORs of `E` equal the 10 `X`-solid points of `S_B ∩ Q⁺(7,2)` (`desargues10Mask`);
4. `desargues10Mask` has `10` points, `10` lines (`60` flags), and uniform line degree `3` per point. -/
theorem desargues_five_frame_and_10_3 :
    (2 ^^^ 3 ^^^ 5 ^^^ 9 ^^^ 13 = 0) ∧
    (allUpTo (fun bits =>
      if bits = 0 || bits = 31 then true
      else ((subsetOfFive bits).foldl (· ^^^ ·) 0) != 0) 32 = true) ∧
    ((sbMask &&& 0xfffe) = desargues10Mask) ∧
    (loop (fun z => if desargues10Mask.testBit z then 1 else 0) 256 = 10) ∧
    (countLines desargues10Mask = 10) ∧
    (allUpTo (fun z => !desargues10Mask.testBit z ||
      decide (flagRow 4 desargues10Mask z = 6)) 256 = true) := by
  decide +kernel

/-- **Ovoid Context Parabola Theorem (all 32 subsets `T ⊆ E` + collinear negative control):**
For every subset `T ⊆ E` of size `k = |T|`, the fiber-flip configuration `S_T` has exact context count
`L(S_T) = 1575 - 256·k + 32·k²` (with unique minimum `1,063` at `k = 4`, equal to `sb4FlipMask`),
whereas flipping the collinear triple `{1, 4, 5}` gives `967 ≠ 1,095`. -/
theorem ovoid_context_parabola :
    (allUpTo (fun bits =>
      let T := subsetOfFive bits
      let k := T.length
      decide (countLines (maskOfFlips T) = 1575 + 32 * k * k - 256 * k)) 32 = true) ∧
    (maskOfFlips [2, 3, 5, 9] = sb4FlipMask) ∧
    (countLines sb4FlipMask = 1063) ∧
    (countLines (maskOfFlips [1, 4, 5]) = 967) := by
  decide +kernel

/-- Bitmask of `red_8(XIXX)` (`8` real points in the `XIXX` fiber). -/
private def red8Mask : ℕ :=
  red8Codes.foldl (fun acc p => acc ||| (1 <<< p)) 0

/-- Precomputed list of the `124` new contexts `(u, v, w)` added by `red_8(XIXX)` to `S_B`,
each carrying `(u, v, w, expectedSign == 1)` for O(124) per-extension evaluation. -/
private def newContexts124 : List (ℕ × ℕ × ℕ × Int) :=
  (List.range 256).foldl (fun acc u =>
    if sbAugMask.testBit u then
      let cm := sbAugMask &&& commM4 u &&& xorShift256 sbAugMask u
      (List.range 256).foldl (fun acc2 v =>
        let w := u ^^^ v
        if u < v && v < w && cm.testBit v &&
            (red8Mask.testBit u || red8Mask.testBit v || red8Mask.testBit w) then
          (u, v, w, lineSignCode 4 u v) :: acc2
        else acc2) acc
    else acc) []

/-- Count how many of the `124` new contexts added by `red_8(XIXX)` are violated under an 8-bit extension `bits`. -/
private def extViolCount (ctx : List (ℕ × ℕ × ℕ × Int)) (bits : ℕ) : ℕ :=
  let extNeg := (List.range 8).foldl (fun acc i =>
    match red8Codes[i]? with
    | some p => if bits.testBit i then acc ||| (1 <<< p) else acc &&& (all256 ^^^ (1 <<< p))
    | none => acc) sbNeg
  ctx.countP fun (u, v, w, lsign) =>
    decide (sInt extNeg u * sInt extNeg v * sInt extNeg w ≠ lsign)

private def extAll256Stats : Bool :=
  let ctx := newContexts124
  decide (ctx.length = 124) &&
  allUpTo (fun bits => decide (52 ≤ extViolCount ctx bits)) 256 &&
  decide (loop (fun bits => if extViolCount ctx bits == 52 then 1 else 0) 256 = 2)

/-- **Structural Properties of Metod Saniga's Augmented Quasi-Quadric `S_B^+`:**
1. Exact decoupling: `red_8(XIXX)` adds `124` contexts to `K_95` and `124` contexts to `S_B` (`0` contexts
   linking `red_8(XIXX)` to `S_B \ Q⁺(7,2)`), of which `28` lie inside the totally isotropic solid
   `Fano(IZZZ) ∪ red_8(XIXX)` and `96` cross it;
2. `K_103` contains all `71` points of the tangent hyperplane `Q⁺(7,2) ∩ IZZZ⊥` (`code 224 = IZZZ`);
3. Exhaustive check over all `2^8 = 256` extensions on `red_8(XIXX)` proves exact minimum `+52`
   (attained by exactly `2` extensions related by a global flip on `red_8`);
4. Constant external hyperplane count: EVERY ONE of the `112` external observables `u ∉ S_B^+`
   commutes with EXACTLY `67` observables of `S_B^+`;
5. Non-squareness (`Theorem 4` obstruction): `15 · 143 = 2,145` is not a perfect square. -/
theorem sb_aug_structural_properties :
    (countLines k95Mask = 635) ∧
    (countLines k103Mask = 759) ∧
    (countLines sbMask = 1095) ∧
    (countLines sbAugMask = 1219) ∧
    -- `71/71` of `Q⁺(7,2) ∩ IZZZ⊥` (code `224 = 14 * 16`, i.e. `IZZZ`) lie in `k103Mask`:
    (pop256 (TrialityResiduals.q7plusMask &&& commM4 224) = 71) ∧
    (((TrialityResiduals.q7plusMask &&& commM4 224) &&& k103Mask) =
      (TrialityResiduals.q7plusMask &&& commM4 224)) ∧
    -- All `256` extensions on `red_8(XIXX)` add `≥ 52` violations, with exactly `2` achieving `52`:
    (extAll256Stats = true) ∧
    -- Constant external hyperplane intersection `HP_out(S_B^+) = 67` across all `112` external points:
    (allUpTo (fun u => if u = 0 || sbAugMask.testBit u then true
      else decide (pop256 (sbAugMask &&& commM4 u) = 67)) 256 = true) ∧
    -- Non-squareness `15 * 143 ≠ k^2`:
    (∀ k : ℕ, 15 * 143 ≠ k ^ 2) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k hk
  have h1 : k ≤ 46 ∨ 47 ≤ k := by omega
  rcases h1 with h | h <;> nlinarith

/-! ### Part 3. General Pairwise-Line-Disjoint Mermin–Peres Grid Lower Bound & Sharp Brackets -/

/-- Canonical unordered triple encoding of a line `{a, b, a ^^^ b}` as a sorted triple of codes. -/
private def canonLineCode (a b : ℕ) : ℕ × ℕ × ℕ :=
  let c := a ^^^ b
  let x := min a (min b c)
  let z := max a (max b c)
  let y := a ^^^ b ^^^ c ^^^ x ^^^ z
  (x, y, z)

/-- The 6 canonical line triples of a Mermin–Peres 4-tuple `(u, v, x, y)`. -/
private def gridLineCodes (g : ℕ × ℕ × ℕ × ℕ) : List (ℕ × ℕ × ℕ) :=
  let (u, v, x, y) := g
  [ canonLineCode u v,
    canonLineCode x y,
    canonLineCode (u ^^^ x) (v ^^^ y),
    canonLineCode u x,
    canonLineCode v y,
    canonLineCode (u ^^^ v) (x ^^^ y) ]

/-- Decidable check that `(u, v, x, y)` is a valid Mermin–Peres 4-tuple inside `mask`. -/
private def mpGridOk (mask : ℕ) (g : ℕ × ℕ × ℕ × ℕ) : Bool :=
  let (u, v, x, y) := g
  let uv := u ^^^ v; let xy := x ^^^ y; let ux := u ^^^ x; let vy := v ^^^ y; let all4 := uv ^^^ xy
  decide (u < 256) && decide (v < 256) && decide (x < 256) && decide (y < 256) &&
  mask.testBit u && mask.testBit v && mask.testBit uv &&
  mask.testBit x && mask.testBit y && mask.testBit xy &&
  mask.testBit ux && mask.testBit vy && mask.testBit all4 &&
  commB 4 u v && commB 4 x y && commB 4 u x && commB 4 v y &&
  !commB 4 u y && !commB 4 v x

private def tripleKey (t : ℕ × ℕ × ℕ) : ℕ :=
  (t.1 <<< 16) ||| (t.2.1 <<< 8) ||| t.2.2

private inductive NatTree
  | leaf : NatTree
  | node : ℕ → NatTree → NatTree → NatTree

private def NatTree.mem (x : ℕ) : NatTree → Bool
  | .leaf => false
  | .node v l r => if x == v then true else if x < v then l.mem x else r.mem x

private def NatTree.ins (x : ℕ) : NatTree → NatTree
  | .leaf => .node x .leaf .leaf
  | .node v l r => if x == v then .node v l r else if x < v then .node v (l.ins x) r else .node v l (r.ins x)

private lemma NatTree.mem_ins (x y : ℕ) (t : NatTree) :
    (t.ins x).mem y = (decide (y = x) || t.mem y) := by
  induction t with
  | leaf =>
    simp only [ins, mem, beq_iff_eq, Bool.or_false]
    by_cases h : y = x <;> simp [h]
  | node v l r ihl ihr =>
    unfold ins
    split_ifs with hxv hlt
    · have hxv' : x = v := beq_iff_eq.mp hxv
      subst hxv'
      simp only [mem, beq_iff_eq]
      by_cases hyv : y = x <;> simp [hyv]
    · simp only [mem, beq_iff_eq]
      by_cases hyv : y = v
      · subst hyv
        have hne : ¬ (y = x) := by omega
        simp [hne]
      · simp only [hyv, ↓reduceIte]
        by_cases hylt : y < v
        · simp only [hylt, ↓reduceIte, ihl]
        · have hne : ¬ (y = x) := by omega
          simp [hylt, hne]
    · have hgt : v < x := by
        have hne : x ≠ v := fun h => hxv (beq_iff_eq.mpr h)
        omega
      simp only [mem, beq_iff_eq]
      by_cases hyv : y = v
      · subst hyv
        have hne : ¬ (y = x) := by omega
        simp [hne]
      · simp only [hyv, ↓reduceIte]
        by_cases hylt : y < v
        · have hne : ¬ (y = x) := by omega
          simp [hylt, hne]
        · simp only [hylt, ↓reduceIte, ihr]

private def noDupTree (t : NatTree) : List ℕ → Bool
  | [] => true
  | x :: xs => !t.mem x && noDupTree (t.ins x) xs

private lemma nodup_of_noDupTree (L : List ℕ) (t : NatTree) (h : noDupTree t L = true) :
    L.Nodup ∧ ∀ y ∈ L, t.mem y = false := by
  induction L generalizing t with
  | nil => exact ⟨List.nodup_nil, fun _ hy => nomatch hy⟩
  | cons x xs ih =>
    simp only [noDupTree, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hnd, hall⟩ := ih (t.ins x) h.2
    refine ⟨List.nodup_cons.mpr ⟨fun hx => ?_, hnd⟩, fun y hy => ?_⟩
    · have h1 := hall x hx
      rw [NatTree.mem_ins] at h1
      simp at h1
    · rcases List.mem_cons.mp hy with rfl | hxs
      · exact h.1
      · have h1 := hall y hxs
        rw [NatTree.mem_ins, Bool.or_eq_false_iff] at h1
        exact h1.2

/-- O(n log n) structurally recursive kernel check that all grids in `gs` are valid in `mask` AND all
`6 · |gs|` lines are pairwise distinct (via BST insertion on 24-bit keys, zero `WellFounded.fix`). -/
private def disjointMPGridsOk (mask : ℕ) (gs : List (ℕ × ℕ × ℕ × ℕ)) : Bool :=
  gs.all (mpGridOk mask) &&
    noDupTree .leaf ((gs.flatMap gridLineCodes).map tripleKey)

private lemma xor_cancel_l (a b : ℕ) : a ^^^ (a ^^^ b) = b := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

private lemma xor_cancel_r (a b : ℕ) : (a ^^^ b) ^^^ b = a := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

private lemma canonLineCode_to_lineOf {a b : ℕ} (ha : a < 256) (hb : b < 256) :
    let t := canonLineCode a b
    ({ptOfCode 4 t.1, ptOfCode 4 t.2.1, ptOfCode 4 t.2.2} : Finset (Pt 4)) =
      lineOf (ptOfCode 4 a, ptOfCode 4 b) := by
  dsimp only [canonLineCode, lineOf]
  rw [← ptOfCode_xor]
  set c := a ^^^ b
  have hxor0 : a ^^^ b ^^^ c = 0 := by simp [c]
  have h1 : ({a, b, c} : Finset ℕ) = {min a (min b c), min a (min b c) ^^^ max a (max b c), max a (max b c)} := by
    have hcases : (a ≤ b ∧ b ≤ c) ∨ (a ≤ c ∧ c ≤ b) ∨ (b ≤ a ∧ a ≤ c) ∨
        (b ≤ c ∧ c ≤ a) ∨ (c ≤ a ∧ a ≤ b) ∨ (c ≤ b ∧ b ≤ a) := by omega
    have hmiddle : ∀ p q r : ℕ, (p = a ∧ q = b ∧ r = c ∨ p = a ∧ q = c ∧ r = b ∨
        p = b ∧ q = a ∧ r = c ∨ p = b ∧ q = c ∧ r = a ∨
        p = c ∧ q = a ∧ r = b ∨ p = c ∧ q = b ∧ r = a) →
        p ^^^ r = q := by
      rintro p q r (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
      · exact xor_cancel_l p q
      · rfl
      · dsimp only [c]; rw [Nat.xor_comm q p]; exact xor_cancel_l p q
      · exact Nat.xor_comm p r
      · exact xor_cancel_r q r
      · dsimp only [c]; rw [Nat.xor_comm r q]; exact xor_cancel_r q r
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hmin : min a (min b c) = a := by omega
      have hmax : max a (max b c) = c := by omega
      rw [hmin, hmax, hmiddle a b c (Or.inl ⟨rfl, rfl, rfl⟩)]
    · have hmin : min a (min b c) = a := by omega
      have hmax : max a (max b c) = b := by omega
      rw [hmin, hmax, hmiddle a c b (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))]
      ext x; simp only [mem_insert, mem_singleton]; tauto
    · have hmin : min a (min b c) = b := by omega
      have hmax : max a (max b c) = c := by omega
      rw [hmin, hmax, hmiddle b a c (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))]
      ext x; simp only [mem_insert, mem_singleton]; tauto
    · have hmin : min a (min b c) = b := by omega
      have hmax : max a (max b c) = a := by omega
      rw [hmin, hmax, hmiddle b c a (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))]
      ext x; simp only [mem_insert, mem_singleton]; tauto
    · have hmin : min a (min b c) = c := by omega
      have hmax : max a (max b c) = b := by omega
      rw [hmin, hmax, hmiddle c a b (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))))]
      ext x; simp only [mem_insert, mem_singleton]; tauto
    · have hmin : min a (min b c) = c := by omega
      have hmax : max a (max b c) = a := by omega
      rw [hmin, hmax, hmiddle c b a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))))]
      ext x; simp only [mem_insert, mem_singleton]; tauto
  rw [hxor0, Nat.zero_xor]
  have himg := congrArg (Finset.image (ptOfCode 4)) h1
  simpa [Finset.image_insert, Finset.image_singleton] using himg.symm

private lemma canonLineCode_lt {a b : ℕ} (ha : a < 256) (hb : b < 256) :
    let t := canonLineCode a b
    t.1 < 256 ∧ t.2.1 < 256 ∧ t.2.2 < 256 := by
  have hc : a ^^^ b < 256 := Nat.xor_lt_two_pow (n := 8) ha hb
  dsimp only [canonLineCode]
  have h1 : min a (min b (a ^^^ b)) < 256 := by omega
  have h3 : max a (max b (a ^^^ b)) < 256 := by omega
  have hxor0 : a ^^^ b ^^^ (a ^^^ b) = 0 := by simp
  rw [hxor0, Nat.zero_xor]
  exact ⟨h1, Nat.xor_lt_two_pow (n := 8) h1 h3, h3⟩

/-- **General Pairwise-Line-Disjoint Mermin–Peres Grid Lower Bound:**
If `disjointMPGridsOk mask gs = true`, then EVERY `±1` assignment `f` on `cfg 4 mask` violates
at least `gs.length` contexts! -/
theorem disjoint_mp_grids_lower_bound (mask : ℕ) (gs : List (ℕ × ℕ × ℕ × ℕ))
    (hok : disjointMPGridsOk mask gs = true) (f : Pt 4 → ℝ)
    (hf : ∀ u ∈ cfg 4 mask, f u = 1 ∨ f u = -1) :
    gs.length ≤ (violatedLines (cfg 4 mask) f).card := by
  classical
  have hparts := (Bool.and_eq_true _ _).mp hok
  have hall : ∀ g ∈ gs, mpGridOk mask g = true := List.all_eq_true.mp hparts.1
  have hnodup : (gs.flatMap gridLineCodes).Nodup :=
    List.Nodup.of_map tripleKey (nodup_of_noDupTree _ .leaf hparts.2).1
  let toLine : ℕ × ℕ × ℕ → Finset (Pt 4) := fun t => {ptOfCode 4 t.1, ptOfCode 4 t.2.1, ptOfCode 4 t.2.2}
  -- Every grid `g ∈ gs` contributes at least one `t ∈ gridLineCodes g` with `toLine t ∈ violatedLines`.
  have hex : ∀ g ∈ gs, ∃ t ∈ gridLineCodes g, toLine t ∈ violatedLines (cfg 4 mask) f := by
    intro ⟨u, v, x, y⟩ hg
    have hm := hall (u, v, x, y) hg
    simp only [mpGridOk, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hm
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hu256, hv256⟩, hx256⟩, hy256⟩, hmu⟩, hmv⟩, hmuv⟩, hmx⟩, hmy⟩, hmxy⟩,
      hmux⟩, hmvy⟩, hmall4⟩, hcuv⟩, hcxy⟩, hcux⟩, hcvy⟩, hncuy⟩, hncvx⟩ := hm
    have huv256 : u ^^^ v < 256 := Nat.xor_lt_two_pow (n := 8) hu256 hv256
    have hxy256 : x ^^^ y < 256 := Nat.xor_lt_two_pow (n := 8) hx256 hy256
    have hux256 : u ^^^ x < 256 := Nat.xor_lt_two_pow (n := 8) hu256 hx256
    have hvy256 : v ^^^ y < 256 := Nat.xor_lt_two_pow (n := 8) hv256 hy256
    have hall256 : (u ^^^ v) ^^^ (x ^^^ y) < 256 := Nat.xor_lt_two_pow (n := 8) huv256 hxy256
    have huM : ptOfCode 4 u ∈ cfg 4 mask := (ptOfCode_mem_cfg hu256).mpr hmu
    have hvM : ptOfCode 4 v ∈ cfg 4 mask := (ptOfCode_mem_cfg hv256).mpr hmv
    have huvM : ptOfCode 4 u + ptOfCode 4 v ∈ cfg 4 mask := by
      rw [← ptOfCode_xor]; exact (ptOfCode_mem_cfg huv256).mpr hmuv
    have hxM : ptOfCode 4 x ∈ cfg 4 mask := (ptOfCode_mem_cfg hx256).mpr hmx
    have hyM : ptOfCode 4 y ∈ cfg 4 mask := (ptOfCode_mem_cfg hy256).mpr hmy
    have hxyM : ptOfCode 4 x + ptOfCode 4 y ∈ cfg 4 mask := by
      rw [← ptOfCode_xor]; exact (ptOfCode_mem_cfg hxy256).mpr hmxy
    have huxM : ptOfCode 4 u + ptOfCode 4 x ∈ cfg 4 mask := by
      rw [← ptOfCode_xor]; exact (ptOfCode_mem_cfg hux256).mpr hmux
    have hvyM : ptOfCode 4 v + ptOfCode 4 y ∈ cfg 4 mask := by
      rw [← ptOfCode_xor]; exact (ptOfCode_mem_cfg hvy256).mpr hmvy
    have hallM : ptOfCode 4 u + ptOfCode 4 v + (ptOfCode 4 x + ptOfCode 4 y) ∈ cfg 4 mask := by
      rw [← ptOfCode_xor, ← ptOfCode_xor, ← ptOfCode_xor]
      exact (ptOfCode_mem_cfg hall256).mpr hmall4
    have hallM' : (ptOfCode 4 u + ptOfCode 4 x) + (ptOfCode 4 v + ptOfCode 4 y) ∈ cfg 4 mask := by
      have : (ptOfCode 4 u + ptOfCode 4 x) + (ptOfCode 4 v + ptOfCode 4 y) =
          ptOfCode 4 u + ptOfCode 4 v + (ptOfCode 4 x + ptOfCode 4 y) := by abel
      rwa [this]
    have suv : symp (ptOfCode 4 u) (ptOfCode 4 v) = 0 := (symp_ptOfCode_eq_zero 4 u v).mpr hcuv
    have sxy : symp (ptOfCode 4 x) (ptOfCode 4 y) = 0 := (symp_ptOfCode_eq_zero 4 x y).mpr hcxy
    have sux : symp (ptOfCode 4 u) (ptOfCode 4 x) = 0 := (symp_ptOfCode_eq_zero 4 u x).mpr hcux
    have svy : symp (ptOfCode 4 v) (ptOfCode 4 y) = 0 := (symp_ptOfCode_eq_zero 4 v y).mpr hcvy
    have suy : symp (ptOfCode 4 u) (ptOfCode 4 y) = 1 := by
      rcases zmod2_cases (symp (ptOfCode 4 u) (ptOfCode 4 y)) with h0 | h1
      · have := (symp_ptOfCode_eq_zero 4 u y).mp h0; rw [hncuy] at this; exact absurd this (by decide)
      · exact h1
    have svx : symp (ptOfCode 4 v) (ptOfCode 4 x) = 1 := by
      rcases zmod2_cases (symp (ptOfCode 4 v) (ptOfCode 4 x)) with h0 | h1
      · have := (symp_ptOfCode_eq_zero 4 v x).mp h0; rw [hncvx] at this; exact absurd this (by decide)
      · exact h1
    have srow2 : symp (ptOfCode 4 u + ptOfCode 4 x) (ptOfCode 4 v + ptOfCode 4 y) = 0 := by
      rw [symp_add_right, ExactDegreesN4N5.symp_add_left, ExactDegreesN4N5.symp_add_left,
        suv, symp_comm (ptOfCode 4 x) (ptOfCode 4 v), svx, suy, sxy]; decide
    have scol2 : symp (ptOfCode 4 u + ptOfCode 4 v) (ptOfCode 4 x + ptOfCode 4 y) = 0 := by
      rw [symp_add_right, ExactDegreesN4N5.symp_add_left, ExactDegreesN4N5.symp_add_left,
        sux, suy, svx, svy]; decide
    have hmp := TrialityResiduals.mermin_peres_4tuple_violated suv sxy sux svy suy svx f
      (hf _ huM) (hf _ hvM) (hf _ huvM) (hf _ hxM) (hf _ hyM) (hf _ hxyM)
      (hf _ huxM) (hf _ hvyM) (hf _ hallM)
    rcases hmp with h | h | h | h | h | h
    · refine ⟨canonLineCode u v, by simp [gridLineCodes], ?_⟩
      dsimp only [toLine]
      rw [canonLineCode_to_lineOf hu256 hv256]
      exact mem_image.mpr ⟨(ptOfCode 4 u, ptOfCode 4 v),
        mem_filter.mpr ⟨mem_flags.mpr ⟨huM, hvM, huvM, suv⟩, h⟩, rfl⟩
    · refine ⟨canonLineCode x y, by simp [gridLineCodes], ?_⟩
      dsimp only [toLine]
      rw [canonLineCode_to_lineOf hx256 hy256]
      exact mem_image.mpr ⟨(ptOfCode 4 x, ptOfCode 4 y),
        mem_filter.mpr ⟨mem_flags.mpr ⟨hxM, hyM, hxyM, sxy⟩, h⟩, rfl⟩
    · refine ⟨canonLineCode (u ^^^ x) (v ^^^ y), by simp [gridLineCodes], ?_⟩
      dsimp only [toLine]
      rw [canonLineCode_to_lineOf hux256 hvy256, ptOfCode_xor, ptOfCode_xor]
      exact mem_image.mpr ⟨(ptOfCode 4 u + ptOfCode 4 x, ptOfCode 4 v + ptOfCode 4 y),
        mem_filter.mpr ⟨mem_flags.mpr ⟨huxM, hvyM, hallM', srow2⟩, h⟩, rfl⟩
    · refine ⟨canonLineCode u x, by simp [gridLineCodes], ?_⟩
      dsimp only [toLine]
      rw [canonLineCode_to_lineOf hu256 hx256]
      exact mem_image.mpr ⟨(ptOfCode 4 u, ptOfCode 4 x),
        mem_filter.mpr ⟨mem_flags.mpr ⟨huM, hxM, huxM, sux⟩, h⟩, rfl⟩
    · refine ⟨canonLineCode v y, by simp [gridLineCodes], ?_⟩
      dsimp only [toLine]
      rw [canonLineCode_to_lineOf hv256 hy256]
      exact mem_image.mpr ⟨(ptOfCode 4 v, ptOfCode 4 y),
        mem_filter.mpr ⟨mem_flags.mpr ⟨hvM, hyM, hvyM, svy⟩, h⟩, rfl⟩
    · refine ⟨canonLineCode (u ^^^ v) (x ^^^ y), by simp [gridLineCodes], ?_⟩
      dsimp only [toLine]
      rw [canonLineCode_to_lineOf huv256 hxy256, ptOfCode_xor, ptOfCode_xor]
      exact mem_image.mpr ⟨(ptOfCode 4 u + ptOfCode 4 v, ptOfCode 4 x + ptOfCode 4 y),
        mem_filter.mpr ⟨mem_flags.mpr ⟨huvM, hxyM, hallM, scol2⟩, h⟩, rfl⟩
  -- For any `i : Fin gs.length`, pick its violated triple `pick i ∈ gridLineCodes gs[i]`.
  let pick : Fin gs.length → ℕ × ℕ × ℕ := fun i =>
    (hex (gs[i]) (List.getElem_mem i.isLt)).choose
  have hpick_mem : ∀ i : Fin gs.length, pick i ∈ gridLineCodes (gs[i]) := fun i =>
    (hex (gs[i]) (List.getElem_mem i.isLt)).choose_spec.1
  have hpick_viol : ∀ i : Fin gs.length, toLine (pick i) ∈ violatedLines (cfg 4 mask) f := fun i =>
    (hex (gs[i]) (List.getElem_mem i.isLt)).choose_spec.2
  -- Every canonical triple `t` coming from a valid grid has `t.1 < t.2.1 < t.2.2 < 256`, so `toLine` is injective!
  have hpick_ord : ∀ i : Fin gs.length, (pick i).1 < (pick i).2.1 ∧ (pick i).2.1 < (pick i).2.2 ∧
      (pick i).2.2 < 256 := by
    intro i
    have hm := hall gs[i] (List.getElem_mem i.isLt)
    rcases hg_eq : gs[i] with ⟨u, v, x, y⟩
    rw [hg_eq] at hm
    simp only [mpGridOk, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hm
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hu256, hv256⟩, hx256⟩, hy256⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩,
      _⟩, _⟩, _⟩, hcuv⟩, hcxy⟩, hcux⟩, hcvy⟩, hncuy⟩, hncvx⟩ := hm
    have hlt_tri : ∀ a b : ℕ, a < 256 → b < 256 → a ≠ b → a ≠ 0 → b ≠ 0 →
        let t := canonLineCode a b; t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.2.2 < 256 := by
      intro a b ha hb hab ha0 hb0
      have hc0 : a ^^^ b ≠ 0 := by
        intro h; apply hab
        have := congrArg (· ^^^ b) h
        rw [xor_cancel_r, Nat.zero_xor] at this; exact this
      have hac : a ≠ a ^^^ b := by
        intro h; apply hb0
        have := congrArg (a ^^^ ·) h
        rw [Nat.xor_self, xor_cancel_l] at this; exact this.symm
      have hbc : b ≠ a ^^^ b := by
        intro h; apply ha0
        have := congrArg (· ^^^ b) h
        rw [Nat.xor_self, xor_cancel_r] at this; exact this.symm
      have hc256 : a ^^^ b < 256 := Nat.xor_lt_two_pow (n := 8) ha hb
      have hmid : a ^^^ b ^^^ (a ^^^ b) = 0 := by simp
      dsimp only [canonLineCode]
      rw [hmid, Nat.zero_xor]
      have hord : (a < b ∧ b < a ^^^ b) ∨ (a < a ^^^ b ∧ a ^^^ b < b) ∨
          (b < a ∧ a < a ^^^ b) ∨ (b < a ^^^ b ∧ a ^^^ b < a) ∨
          (a ^^^ b < a ∧ a < b) ∨ (a ^^^ b < b ∧ b < a) := by omega
      rcases hord with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have m1 : min a (min b (a ^^^ b)) = a := by omega
        have m2 : max a (max b (a ^^^ b)) = a ^^^ b := by omega
        rw [m1, m2, xor_cancel_l]; omega
      · have m1 : min a (min b (a ^^^ b)) = a := by omega
        have m2 : max a (max b (a ^^^ b)) = b := by omega
        rw [m1, m2]; omega
      · have m1 : min a (min b (a ^^^ b)) = b := by omega
        have m2 : max a (max b (a ^^^ b)) = a ^^^ b := by omega
        have mx : b ^^^ (a ^^^ b) = a := by rw [Nat.xor_comm a b]; exact xor_cancel_l b a
        rw [m1, m2, mx]; omega
      · have m1 : min a (min b (a ^^^ b)) = b := by omega
        have m2 : max a (max b (a ^^^ b)) = a := by omega
        have mx : b ^^^ a = a ^^^ b := Nat.xor_comm b a
        rw [m1, m2, mx]; omega
      · have m1 : min a (min b (a ^^^ b)) = a ^^^ b := by omega
        have m2 : max a (max b (a ^^^ b)) = b := by omega
        rw [m1, m2, xor_cancel_r]; omega
      · have m1 : min a (min b (a ^^^ b)) = a ^^^ b := by omega
        have m2 : max a (max b (a ^^^ b)) = a := by omega
        have mx : (a ^^^ b) ^^^ a = b := by rw [Nat.xor_comm a b]; exact xor_cancel_r b a
        rw [m1, m2, mx]; omega
    -- Wait: instead of proving `a ≠ b` for all 6 lines manually, notice: `toLine (pick i) ∈ violatedLines`
    -- already guarantees `(toLine (pick i)).card = 3` (since `0 ∉ cfg 4 mask` is implied by `mpGridOk` — wait,
    -- we just prove `toLine t1 = toLine t2 → t1 = t2` for any two sorted triples `< 256`!).
    -- Even simpler: prove `a ≠ b ∧ a ≠ 0 ∧ b ≠ 0` directly from `commB`? No, check `t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.2.2 < 256` directly!
    -- For `(u, v, x, y)` in `mpGridOk`: `u, v, x, y, ...` are all distinct because `!commB 4 u y` and `!commB 4 v x`!
    have h0_ne : ∀ a : ℕ, !commB 4 a y = true ∨ !commB 4 v a = true → a ≠ 0 := by
      intro a ha h0; subst h0; simp [commB, common] at ha
    -- Check `t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.2.2 < 256` directly from `toLine (pick i) ∈ violatedLines`?
    -- Actually `canonLineCode_lt` already gives `< 256`, and `hpick_mem` gives `pick i ∈ gridLineCodes (u, v, x, y)`.
    -- Wait: let's just include `t.1 < t.2.1 ∧ t.2.1 < t.2.2` inside `mpGridOk`? Even cleaner, no extra proof needed!
    have h_ne0_of_anticomm : ∀ a b : ℕ, commB 4 a b = false → a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b := by
      intro a b hab
      refine ⟨?_, ?_, ?_⟩
      · rintro rfl; simp [commB, common] at hab
      · rintro rfl; simp [commB, common] at hab
      · rintro rfl; have : commB 4 a a = true := by
          unfold commB; simp only [beq_iff_eq]; omega
        rw [this] at hab; exact absurd hab (by decide)
    -- Actually, we can prove directly that `pick` is injective into `violatedLines` using `ptOfCode_inj`:
    -- wait, we only need `pick i ≠ pick j` when `i ≠ j` (from `hnodup`), AND `toLine (pick i) = toLine (pick j) → pick i = pick j`!
    -- Wait: let's check `a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b` for all 6 pairs of `(u, v, x, y)`:
    have h_symp_ne : ∀ a b c : ℕ, commB 4 a c = true → commB 4 b c = false → a ≠ b := by
      intro a b c h1 h2 h; rw [h, h2] at h1; exact absurd h1 (by decide)
    have h1 := h_ne0_of_anticomm u y (by simpa using hncuy)
    have h2 := h_ne0_of_anticomm v x (by simpa using hncvx)
    -- All 6 pairs are distinct & nonzero because each pair has a third point commuting with one and anticommuting with the other!
    have huv_ne : u ≠ v := h_symp_ne u v x hcux hncvx
    have hxy_ne : x ≠ y := h_symp_ne x y u (by simpa [commB, Nat.add_comm] using hcux) (by simpa [commB, Nat.add_comm] using hncuy)
    have hux_ne : u ≠ x := h_symp_ne u x v (by simpa [commB, Nat.add_comm] using hcuv) (by simpa [commB, Nat.add_comm] using hncvx)
    have hvy_ne : v ≠ y := h_symp_ne v y u (by simpa [commB, Nat.add_comm] using hcuv) (by simpa [commB, Nat.add_comm] using hncuy)
    have hux_0 : u ^^^ x ≠ 0 := by intro h; apply hux_ne; have := congrArg (· ^^^ x) h; simpa [Nat.xor_assoc] using this
    have hvy_0 : v ^^^ y ≠ 0 := by intro h; apply hvy_ne; have := congrArg (· ^^^ y) h; simpa [Nat.xor_assoc] using this
    have huv_0 : u ^^^ v ≠ 0 := by intro h; apply huv_ne; have := congrArg (· ^^^ v) h; simpa [Nat.xor_assoc] using this
    have hxy_0 : x ^^^ y ≠ 0 := by intro h; apply hxy_ne; have := congrArg (· ^^^ y) h; simpa [Nat.xor_assoc] using this
    have hr2_ne : u ^^^ x ≠ v ^^^ y := by
      intro h
      have hcomm1 : symp (ptOfCode 4 (u ^^^ x)) (ptOfCode 4 v) = 1 := by
        rw [ptOfCode_xor, ExactDegreesN4N5.symp_add_left, (symp_ptOfCode_eq_zero 4 u v).mpr hcuv]
        rcases zmod2_cases (symp (ptOfCode 4 x) (ptOfCode 4 v)) with h0 | h1
        · rw [symp_comm] at h0; have := (symp_ptOfCode_eq_zero 4 v x).mp h0
          rw [hncvx] at this; exact absurd this (by decide)
        · simpa using h1
      have hcomm2 : symp (ptOfCode 4 (v ^^^ y)) (ptOfCode 4 v) = 0 := by
        rw [ptOfCode_xor, ExactDegreesN4N5.symp_add_left, symp_self, symp_comm,
          (symp_ptOfCode_eq_zero 4 v y).mpr hcvy]; simp
      rw [h] at hcomm1; rw [hcomm2] at hcomm1; exact absurd hcomm1 (by decide)
    have hc2_ne : u ^^^ v ≠ x ^^^ y := by
      intro h
      have hcomm1 : symp (ptOfCode 4 (u ^^^ v)) (ptOfCode 4 x) = 1 := by
        rw [ptOfCode_xor, ExactDegreesN4N5.symp_add_left, (symp_ptOfCode_eq_zero 4 u x).mpr hcux]
        rcases zmod2_cases (symp (ptOfCode 4 v) (ptOfCode 4 x)) with h0 | h1
        · have := (symp_ptOfCode_eq_zero 4 v x).mp h0; rw [hncvx] at this; exact absurd this (by decide)
        · simpa using h1
      have hcomm2 : symp (ptOfCode 4 (x ^^^ y)) (ptOfCode 4 x) = 0 := by
        rw [ptOfCode_xor, ExactDegreesN4N5.symp_add_left, symp_self, symp_comm,
          (symp_ptOfCode_eq_zero 4 x y).mpr hcxy]; simp
      rw [h] at hcomm1; rw [hcomm2] at hcomm1; exact absurd hcomm1 (by decide)
    have hpm := hpick_mem i
    rw [hg_eq] at hpm
    simp only [gridLineCodes, List.mem_cons, List.not_mem_nil, or_false] at hpm
    rcases hpm with h | h | h | h | h | h
    · rw [h]; exact hlt_tri u v hu256 hv256 huv_ne h1.1 h2.1
    · rw [h]; exact hlt_tri x y hx256 hy256 hxy_ne h2.2.1 h1.2.1
    · rw [h]; exact hlt_tri (u ^^^ x) (v ^^^ y) (Nat.xor_lt_two_pow (n := 8) hu256 hx256)
        (Nat.xor_lt_two_pow (n := 8) hv256 hy256) hr2_ne hux_0 hvy_0
    · rw [h]; exact hlt_tri u x hu256 hx256 hux_ne h1.1 h2.2.1
    · rw [h]; exact hlt_tri v y hv256 hy256 hvy_ne h2.1 h1.2.1
    · rw [h]; exact hlt_tri (u ^^^ v) (x ^^^ y) (Nat.xor_lt_two_pow (n := 8) hu256 hv256)
        (Nat.xor_lt_two_pow (n := 8) hx256 hy256) hc2_ne huv_0 hxy_0
  -- Show `i ↦ toLine (pick i)` is injective on `Fin gs.length`!
  have hinj : Function.Injective (fun i : Fin gs.length => toLine (pick i)) := by
    intro i j hij
    have hp_eq : pick i = pick j := by
      dsimp only at hij
      rcases hpi : pick i with ⟨ai, bi, ci⟩
      rcases hpj : pick j with ⟨aj, bj, cj⟩
      have hoi := hpick_ord i
      have hoj := hpick_ord j
      rw [hpi] at hoi hij
      rw [hpj] at hoj hij
      dsimp only at hoi hoj hij
      have hset : ({ai, bi, ci} : Finset ℕ) = {aj, bj, cj} := by
        ext z
        constructor
        · intro hz
          have hzP : ptOfCode 4 z ∈ toLine (aj, bj, cj) := by
            rw [← hij]; simp only [toLine, mem_insert, mem_singleton] at hz ⊢
            rcases hz with rfl | rfl | rfl <;> simp
          simp only [toLine, mem_insert, mem_singleton] at hzP
          have hz256 : z < 256 := by
            simp only [mem_insert, mem_singleton] at hz
            rcases hz with rfl | rfl | rfl <;> omega
          rcases hzP with h | h | h
          · simp [ptOfCode_inj hz256 (by omega) h]
          · simp [ptOfCode_inj hz256 (by omega) h]
          · simp [ptOfCode_inj hz256 (by omega) h]
        · intro hz
          have hzP : ptOfCode 4 z ∈ toLine (ai, bi, ci) := by
            rw [hij]; simp only [toLine, mem_insert, mem_singleton] at hz ⊢
            rcases hz with rfl | rfl | rfl <;> simp
          simp only [toLine, mem_insert, mem_singleton] at hzP
          have hz256 : z < 256 := by
            simp only [mem_insert, mem_singleton] at hz
            rcases hz with rfl | rfl | rfl <;> omega
          rcases hzP with h | h | h
          · simp [ptOfCode_inj hz256 (by omega) h]
          · simp [ptOfCode_inj hz256 (by omega) h]
          · simp [ptOfCode_inj hz256 (by omega) h]
      have ha_in : ai ∈ ({aj, bj, cj} : Finset ℕ) := hset ▸ by simp
      have hb_in : bi ∈ ({aj, bj, cj} : Finset ℕ) := hset ▸ by simp
      have hc_in : ci ∈ ({aj, bj, cj} : Finset ℕ) := hset ▸ by simp
      have haj_in : aj ∈ ({ai, bi, ci} : Finset ℕ) := hset.symm ▸ by simp
      have hbj_in : bj ∈ ({ai, bi, ci} : Finset ℕ) := hset.symm ▸ by simp
      have hcj_in : cj ∈ ({ai, bi, ci} : Finset ℕ) := hset.symm ▸ by simp
      simp only [mem_insert, mem_singleton] at ha_in hb_in hc_in haj_in hbj_in hcj_in
      have e1 : ai = aj := by omega
      have e3 : ci = cj := by omega
      have e2 : bi = bj := by omega
      rw [e1, e2, e3]
    -- `pick i = pick j` forces `i = j` by `Nodup (gs.flatMap gridLineCodes)`!
    by_contra hne
    have hflat_nodup := List.nodup_flatMap.mp hnodup
    have hpw := hflat_nodup.2
    -- Index-based pairwise disjointness of `gs.map gridLineCodes` from `List.Pairwise List.Disjoint`!
    have hij_lt : i.val < j.val ∨ j.val < i.val := by omega
    have hdisj_at : ∀ a b : Fin gs.length, a.val < b.val →
        List.Disjoint (gridLineCodes gs[a]) (gridLineCodes gs[b]) := by
      intro a b hab
      have hpw' := List.pairwise_iff_getElem.mp hpw
      exact hpw' a.val b.val a.isLt b.isLt hab
    rcases hij_lt with hlt | hlt
    · exact hdisj_at i j hlt (hpick_mem i) (hp_eq ▸ hpick_mem j)
    · exact hdisj_at j i hlt (hpick_mem j) (hp_eq.symm ▸ hpick_mem i)
  have hcard := Fintype.card_le_of_injective
    (fun i : Fin gs.length => (⟨toLine (pick i), hpick_viol i⟩ : {L // L ∈ violatedLines (cfg 4 mask) f}))
    (fun i j h => hinj (congrArg Subtype.val h))
  simpa using hcard

/-! ### Part 4. Explicit Pairwise-Line-Disjoint Packings & Exact Witness Upper Bounds -/

/-- 53 pairwise-line-disjoint Mermin–Peres grids inside `K_95 = S_B ∩ Q⁺(7,2)`. -/
def k95DisjointGrids : List (ℕ × ℕ × ℕ × ℕ) :=
  [(1,96,10,16),(1,160,6,16),(1,224,14,16),(4,16,11,64),(4,48,10,64),(4,160,8,64),(6,96,10,80),
   (6,224,8,32),(7,48,97,32),(7,96,11,144),(7,224,8,112),(8,16,55,128),(8,48,22,128),(8,96,20,128),
   (10,160,22,96),(10,224,20,48),(11,48,65,192),(11,160,55,80),(11,224,52,176),(14,96,20,32),
   (14,160,22,144),(15,96,148,176),(15,160,55,208),(16,36,192,95),(26,160,6,128),(1,74,32,80),
   (1,102,64,24),(1,110,128,112),(1,134,192,112),(1,170,206,90),(1,174,234,26),(4,24,128,80),
   (4,26,40,246),(4,56,144,64),(4,59,32,193),(4,155,170,235),(4,171,186,219),(6,24,144,36),
   (6,97,120,207),(6,104,129,32),(6,225,240,64),(7,56,128,36),(7,59,80,144),(8,52,103,128),
   (8,87,102,135),(8,118,80,186),(10,65,176,215),(12,20,230,144),(12,22,192,126),(12,231,246,102),
   (14,118,208,44),(15,52,103,28),(20,170,207,80)]

/-- 87 pairwise-line-disjoint Mermin–Peres grids inside `K_103 = K_95 ∪ red_8(XIXX)`. -/
def k103DisjointGrids : List (ℕ × ℕ × ℕ × ℕ) :=
  [(1,224,14,16),(4,16,11,64),(4,48,10,64),(4,160,8,64),(6,224,8,32),(7,224,8,112),(8,16,55,128),
   (8,48,22,128),(8,96,20,128),(10,224,20,48),(11,224,52,176),(14,96,20,32),(14,160,22,144),
   (15,48,97,32),(15,96,52,16),(15,160,55,176),(16,72,192,159),(20,160,12,192),(30,96,4,144),
   (30,160,6,128),(36,132,8,88),(40,72,4,180),(48,72,192,174),(48,132,80,74),(52,148,12,220),
   (1,110,10,190),(1,174,32,88),(1,206,6,126),(4,24,59,64),(4,56,128,64),(4,155,32,112),
   (4,171,186,74),(6,104,11,164),(7,56,90,206),(7,104,128,112),(8,52,87,128),(8,103,118,183),
   (10,164,240,63),(11,148,112,88),(14,97,118,230),(14,102,161,129),(14,164,193,32),(14,180,208,75),
   (15,87,192,44),(15,164,193,26),(20,40,132,104),(20,111,170,55),(22,104,10,80),(24,36,72,222),
   (24,110,231,234),(28,40,192,80),(30,65,164,128),(40,207,222,110),(59,159,134,222),(1,96,12,55),
   (1,160,44,90),(1,192,74,125),(6,16,97,60),(6,96,10,65),(6,112,26,45),(7,48,10,171),(7,80,11,157),
   (7,96,59,22),(10,16,87,118),(10,160,230,129),(10,176,225,45),(11,48,65,183),(11,144,161,189),
   (11,160,215,26),(12,16,215,74),(12,32,22,189),(12,48,225,103),(13,112,225,102),(13,144,183,75),
   (13,176,33,250),(16,134,234,7),(16,170,236,215),(26,170,129,220),(28,32,230,237),(32,204,144,150),
   (45,80,134,231),(48,204,219,134),(59,155,220,157),(96,134,161,220),(112,150,189,186),
   (123,144,26,246),(125,176,60,240)]

/-- 112 pairwise-line-disjoint Mermin–Peres grids inside `S_B^(4)` (`135` pts, `1,063` lines; floor `59`). -/
def sb4FlipDisjointGrids : List (ℕ × ℕ × ℕ × ℕ) :=
  [(4,16,11,64),(4,48,10,64),(4,160,8,64),(8,16,7,128),(8,48,6,128),(8,96,20,128),(14,16,1,32),
   (14,96,20,32),(14,160,22,128),(15,96,52,16),(15,160,55,176),(16,72,192,159),(16,104,224,7),
   (19,64,6,144),(19,128,10,80),(19,227,33,65),(20,36,10,234),(20,160,12,192),(21,128,44,192),
   (21,229,34,226),(24,40,102,246),(25,233,34,114),(30,96,164,48),(34,64,69,240),(34,128,89,240),
   (34,208,1,96),(35,211,65,97),(36,132,8,120),(1,224,98,80),(6,224,99,192),(26,224,4,144),
   (1,110,10,190),(1,162,6,16),(1,174,64,88),(1,206,44,52),(1,226,102,16),(4,24,59,231),
   (4,40,128,215),(4,56,155,230),(4,170,32,80),(4,171,176,87),(6,104,11,164),(6,120,10,164),
   (6,147,96,57),(6,227,26,74),(7,50,10,169),(7,56,90,36),(7,98,11,114),(8,22,32,144),(8,52,80,144),
   (8,55,102,150),(8,103,118,157),(10,83,87,50),(10,227,16,34),(11,50,150,181),(11,52,231,128),
   (11,148,161,32),(11,226,48,35),(12,21,22,118),(12,36,55,95),(12,52,215,175),(12,53,33,83),
   (12,197,193,162),(12,229,48,99),(14,97,118,230),(14,102,193,225),(14,161,180,235),
   (14,164,208,155),(15,87,97,189),(15,103,161,125),(15,148,192,176),(15,164,240,26),(19,74,97,125),
   (19,101,225,160),(19,134,161,1),(19,169,229,69),(20,40,111,206),(20,174,235,230),(21,103,101,204),
   (21,134,160,74),(21,162,201,35),(21,227,231,48),(22,69,45,204),(22,197,171,34),(25,163,171,48),
   (28,137,75,233),(34,149,201,169),(56,95,206,132),(57,197,219,102),(59,201,7,176),(1,192,74,157),
   (6,112,129,189),(7,80,219,205),(10,176,225,205),(12,32,246,93),(13,32,118,220),(13,80,225,103),
   (13,112,231,102),(13,176,33,26),(13,192,87,161),(28,32,171,205),(45,144,193,123),(59,144,215,125),
   (80,135,189,28),(112,134,157,97),(1,204,128,183),(6,155,240,90),(6,235,97,160),(7,234,96,246),
   (11,230,55,22),(33,205,90,134),(93,161,186,64)]

/-- 121 pairwise-line-disjoint Mermin–Peres grids inside `S_B^+` (`143` pts, `1,219` lines; floor `95`). -/
def sbAugDisjointGrids : List (ℕ × ℕ × ℕ × ℕ) :=
  [(1,224,14,16),(4,16,11,64),(4,32,10,64),(4,48,25,64),(4,144,8,64),(4,160,24,64),(4,176,40,64),
   (6,224,8,32),(7,224,8,29),(8,16,53,128),(8,48,22,128),(8,80,20,128),(8,96,36,128),(8,112,52,128),
   (10,224,19,48),(11,224,50,80),(12,224,20,109),(14,112,20,32),(14,160,19,128),(14,176,22,55),
   (15,48,50,211),(15,96,52,16),(15,144,55,118),(15,160,87,176),(15,192,103,44),(16,40,34,29),
   (16,104,98,7),(16,110,32,1),(16,132,192,95),(16,164,162,11),(16,206,226,29),(19,99,33,129),
   (19,163,6,1),(19,192,74,160),(19,227,97,1),(20,36,10,90),(20,132,40,88),(20,160,44,21),
   (20,164,235,59),(21,32,34,129),(21,69,12,204),(21,101,103,28),(21,128,109,192),(21,197,40,150),
   (21,229,77,141),(24,32,6,97),(24,40,102,246),(24,72,36,206),(24,96,44,25),(25,169,34,69),
   (25,233,36,132),(26,224,4,173),(29,77,36,222),(29,141,69,83),(29,192,137,60),(30,110,33,250),
   (30,160,35,197),(32,69,144,150),(32,72,193,207),(32,77,208,34),(34,192,201,176),(35,192,22,28),
   (35,211,65,126),(40,72,12,197),(48,72,147,149),(48,132,83,74),(53,208,88,174),(55,215,69,120),
   (57,201,4,171),(57,208,148,222),(63,159,87,98),(69,128,60,4),(95,160,8,69),(96,190,137,99),
   (121,169,164,186),(1,34,236,89),(1,98,204,89),(4,155,170,125),(6,227,155,162),(7,178,186,25),
   (8,103,118,157),(10,83,87,50),(10,163,183,197),(11,226,118,101),(12,53,33,83),(12,229,193,99),
   (19,134,161,189),(21,134,233,219),(22,197,205,103),(24,110,231,234),(28,169,129,227),
   (34,65,197,252),(34,137,193,236),(72,150,180,235),(1,192,74,125),(6,112,129,93),(7,80,59,45),
   (10,176,1,45),(11,144,55,45),(12,32,230,157),(13,32,6,252),(13,80,1,103),(13,112,87,246),
   (13,144,33,59),(13,176,150,74),(13,192,7,97),(22,102,161,60),(26,170,6,235),(28,32,135,205),
   (32,93,204,171),(45,192,74,65),(75,144,28,125),(90,176,33,205),(7,90,208,155),(7,234,128,161),
   (10,231,16,60),(13,183,225,75),(13,193,230,96),(26,205,64,225),(45,204,219,48),(55,157,208,252)]

private lemma k95_grids_ok : disjointMPGridsOk k95Mask k95DisjointGrids = true := by decide +kernel
private lemma k103_grids_ok : disjointMPGridsOk k103Mask k103DisjointGrids = true := by decide +kernel
private lemma sb4_grids_ok : disjointMPGridsOk sb4FlipMask sb4FlipDisjointGrids = true := by decide +kernel
private lemma sbaug_grids_ok : disjointMPGridsOk sbAugMask sbAugDisjointGrids = true := by decide +kernel

private lemma k95_vb :
    block (fastViolRow 10 4 k95Mask sbNeg) 16 0 = 20 ∧
    block (fastViolRow 10 4 k95Mask sbNeg) 16 1 = 18 ∧
    block (fastViolRow 10 4 k95Mask sbNeg) 16 2 = 22 ∧
    block (fastViolRow 10 4 k95Mask sbNeg) 16 3 = 18 ∧
    block (fastViolRow 10 4 k95Mask sbNeg) 16 4 = 22 ∧
    block (fastViolRow 10 4 k95Mask sbNeg) 16 5 = 22 ∧
    block (fastViolRow 10 4 k95Mask sbNeg) 16 6 = 18 ∧
    block (fastViolRow 10 4 k95Mask sbNeg) 16 7 = 22 ∧
    block (fastViolRow 10 4 k95Mask sbNeg) 16 8 = 22 ∧
    block (fastViolRow 10 4 k95Mask sbNeg) 16 9 = 22 ∧
    block (fastViolRow 10 4 k95Mask sbNeg) 16 10 = 18 ∧
    block (fastViolRow 10 4 k95Mask sbNeg) 16 11 = 22 ∧
    block (fastViolRow 10 4 k95Mask sbNeg) 16 12 = 22 ∧
    block (fastViolRow 10 4 k95Mask sbNeg) 16 13 = 22 ∧
    block (fastViolRow 10 4 k95Mask sbNeg) 16 14 = 18 ∧
    block (fastViolRow 10 4 k95Mask sbNeg) 16 15 = 22 := by decide +kernel

private lemma k103_vb :
    block (fastViolRow 10 4 k103Mask sbExtNeg) 16 0 = 58 ∧
    block (fastViolRow 10 4 k103Mask sbExtNeg) 16 1 = 30 ∧
    block (fastViolRow 10 4 k103Mask sbExtNeg) 16 2 = 44 ∧
    block (fastViolRow 10 4 k103Mask sbExtNeg) 16 3 = 30 ∧
    block (fastViolRow 10 4 k103Mask sbExtNeg) 16 4 = 34 ∧
    block (fastViolRow 10 4 k103Mask sbExtNeg) 16 5 = 44 ∧
    block (fastViolRow 10 4 k103Mask sbExtNeg) 16 6 = 30 ∧
    block (fastViolRow 10 4 k103Mask sbExtNeg) 16 7 = 44 ∧
    block (fastViolRow 10 4 k103Mask sbExtNeg) 16 8 = 34 ∧
    block (fastViolRow 10 4 k103Mask sbExtNeg) 16 9 = 44 ∧
    block (fastViolRow 10 4 k103Mask sbExtNeg) 16 10 = 30 ∧
    block (fastViolRow 10 4 k103Mask sbExtNeg) 16 11 = 44 ∧
    block (fastViolRow 10 4 k103Mask sbExtNeg) 16 12 = 44 ∧
    block (fastViolRow 10 4 k103Mask sbExtNeg) 16 13 = 34 ∧
    block (fastViolRow 10 4 k103Mask sbExtNeg) 16 14 = 64 ∧
    block (fastViolRow 10 4 k103Mask sbExtNeg) 16 15 = 34 := by decide +kernel

private lemma sb4_vb :
    block (fastViolRow 10 4 sb4FlipMask sbExtNeg) 16 0 = 58 ∧
    block (fastViolRow 10 4 sb4FlipMask sbExtNeg) 16 1 = 44 ∧
    block (fastViolRow 10 4 sb4FlipMask sbExtNeg) 16 2 = 48 ∧
    block (fastViolRow 10 4 sb4FlipMask sbExtNeg) 16 3 = 44 ∧
    block (fastViolRow 10 4 sb4FlipMask sbExtNeg) 16 4 = 36 ∧
    block (fastViolRow 10 4 sb4FlipMask sbExtNeg) 16 5 = 48 ∧
    block (fastViolRow 10 4 sb4FlipMask sbExtNeg) 16 6 = 44 ∧
    block (fastViolRow 10 4 sb4FlipMask sbExtNeg) 16 7 = 48 ∧
    block (fastViolRow 10 4 sb4FlipMask sbExtNeg) 16 8 = 36 ∧
    block (fastViolRow 10 4 sb4FlipMask sbExtNeg) 16 9 = 48 ∧
    block (fastViolRow 10 4 sb4FlipMask sbExtNeg) 16 10 = 44 ∧
    block (fastViolRow 10 4 sb4FlipMask sbExtNeg) 16 11 = 48 ∧
    block (fastViolRow 10 4 sb4FlipMask sbExtNeg) 16 12 = 48 ∧
    block (fastViolRow 10 4 sb4FlipMask sbExtNeg) 16 13 = 36 ∧
    block (fastViolRow 10 4 sb4FlipMask sbExtNeg) 16 14 = 72 ∧
    block (fastViolRow 10 4 sb4FlipMask sbExtNeg) 16 15 = 36 := by decide +kernel

private lemma sbaug_vb :
    block (fastViolRow 10 4 sbAugMask sbExtNeg) 16 0 = 58 ∧
    block (fastViolRow 10 4 sbAugMask sbExtNeg) 16 1 = 46 ∧
    block (fastViolRow 10 4 sbAugMask sbExtNeg) 16 2 = 48 ∧
    block (fastViolRow 10 4 sbAugMask sbExtNeg) 16 3 = 46 ∧
    block (fastViolRow 10 4 sbAugMask sbExtNeg) 16 4 = 38 ∧
    block (fastViolRow 10 4 sbAugMask sbExtNeg) 16 5 = 48 ∧
    block (fastViolRow 10 4 sbAugMask sbExtNeg) 16 6 = 46 ∧
    block (fastViolRow 10 4 sbAugMask sbExtNeg) 16 7 = 48 ∧
    block (fastViolRow 10 4 sbAugMask sbExtNeg) 16 8 = 38 ∧
    block (fastViolRow 10 4 sbAugMask sbExtNeg) 16 9 = 48 ∧
    block (fastViolRow 10 4 sbAugMask sbExtNeg) 16 10 = 46 ∧
    block (fastViolRow 10 4 sbAugMask sbExtNeg) 16 11 = 48 ∧
    block (fastViolRow 10 4 sbAugMask sbExtNeg) 16 12 = 48 ∧
    block (fastViolRow 10 4 sbAugMask sbExtNeg) 16 13 = 38 ∧
    block (fastViolRow 10 4 sbAugMask sbExtNeg) 16 14 = 80 ∧
    block (fastViolRow 10 4 sbAugMask sbExtNeg) 16 15 = 38 := by decide +kernel

/-- **Sharp Bracket on `K_95 = S_B ∩ Q⁺(7,2)`:** `53 ≤ d(K_95) ≤ 55` (beating floor `39` by `+14`). -/
theorem k95_bounds_53_55 :
    (∀ f : Pt 4 → ℝ, (∀ u ∈ cfg 4 k95Mask, f u = 1 ∨ f u = -1) →
      53 ≤ (violatedLines (cfg 4 k95Mask) f).card) ∧
    (∃ f : Pt 4 → ℝ, (∀ u, f u = 1 ∨ f u = -1) ∧
      (violatedLines (cfg 4 k95Mask) f).card = 55) := by
  refine ⟨fun f hf => disjoint_mp_grids_lower_bound k95Mask k95DisjointGrids k95_grids_ok f hf, ?_⟩
  let f : Pt 4 → ℝ := fun u => ((sgnOf 4 sbNeg u : ℤ) : ℝ)
  refine ⟨f, sgnOf_values 4 sbNeg, ?_⟩
  have hv : (violated (cfg 4 k95Mask) f).card = 6 * 55 := by
    have h := loop_blocks (fastViolRow 10 4 k95Mask sbNeg) 16 16
    rcases k95_vb with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
    rw [loop_sixteen, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15] at h
    have e : (2 : ℕ) ^ (2 * 4) = 16 * 16 := by norm_num
    rw [card_violated_cfg_fast (b := 10) (N := 4) (by norm_num) (by norm_num), e]
    exact h.trans (by norm_num)
  have h6 := card_violated_eq_six (cfg 4 k95Mask) (zero_not_mem_cfg (by decide)) f
  omega

/-- **Sharp Bracket on `K_103 = K_95 ∪ red_8(XIXX)`:** `87 ≤ d(K_103) ≤ 107` (beating floor `65` by `+22`). -/
theorem k103_bounds_87_107 :
    (∀ f : Pt 4 → ℝ, (∀ u ∈ cfg 4 k103Mask, f u = 1 ∨ f u = -1) →
      87 ≤ (violatedLines (cfg 4 k103Mask) f).card) ∧
    (∃ f : Pt 4 → ℝ, (∀ u, f u = 1 ∨ f u = -1) ∧
      (violatedLines (cfg 4 k103Mask) f).card = 107) := by
  refine ⟨fun f hf => disjoint_mp_grids_lower_bound k103Mask k103DisjointGrids k103_grids_ok f hf, ?_⟩
  let f : Pt 4 → ℝ := fun u => ((sgnOf 4 sbExtNeg u : ℤ) : ℝ)
  refine ⟨f, sgnOf_values 4 sbExtNeg, ?_⟩
  have hv : (violated (cfg 4 k103Mask) f).card = 6 * 107 := by
    have h := loop_blocks (fastViolRow 10 4 k103Mask sbExtNeg) 16 16
    rcases k103_vb with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
    rw [loop_sixteen, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15] at h
    have e : (2 : ℕ) ^ (2 * 4) = 16 * 16 := by norm_num
    rw [card_violated_cfg_fast (b := 10) (N := 4) (by norm_num) (by norm_num), e]
    exact h.trans (by norm_num)
  have h6 := card_violated_eq_six (cfg 4 k103Mask) (zero_not_mem_cfg (by decide)) f
  omega

/-- **Sharp Bracket on `S_B^(4)` (`135` pts, `1,063` lines, floor `59`):**
`112 ≤ d(S_B^(4)) ≤ 123`, strictly breaking spectral-floor saturation (`59 < 112`) by `+53`! -/
theorem sb4flip_bounds_112_123 :
    (∀ f : Pt 4 → ℝ, (∀ u ∈ cfg 4 sb4FlipMask, f u = 1 ∨ f u = -1) →
      112 ≤ (violatedLines (cfg 4 sb4FlipMask) f).card) ∧
    (∃ f : Pt 4 → ℝ, (∀ u, f u = 1 ∨ f u = -1) ∧
      (violatedLines (cfg 4 sb4FlipMask) f).card = 123) := by
  refine ⟨fun f hf => disjoint_mp_grids_lower_bound sb4FlipMask sb4FlipDisjointGrids sb4_grids_ok f hf, ?_⟩
  let f : Pt 4 → ℝ := fun u => ((sgnOf 4 sbExtNeg u : ℤ) : ℝ)
  refine ⟨f, sgnOf_values 4 sbExtNeg, ?_⟩
  have hv : (violated (cfg 4 sb4FlipMask) f).card = 6 * 123 := by
    have h := loop_blocks (fastViolRow 10 4 sb4FlipMask sbExtNeg) 16 16
    rcases sb4_vb with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
    rw [loop_sixteen, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15] at h
    have e : (2 : ℕ) ^ (2 * 4) = 16 * 16 := by norm_num
    rw [card_violated_cfg_fast (b := 10) (N := 4) (by norm_num) (by norm_num), e]
    exact h.trans (by norm_num)
  have h6 := card_violated_eq_six (cfg 4 sb4FlipMask) (zero_not_mem_cfg (by decide)) f
  omega

/-- **Sharp Bracket on Metod Saniga's Augmented Quasi-Quadric `S_B^+` (`143` pts, `1,219` lines):**
`121 ≤ d(S_B^+) ≤ 127` (beating Theorem 1 spectral floor `95` by `+26`, gap `6`). -/
theorem sb_aug_bounds_121_127 :
    (∀ f : Pt 4 → ℝ, (∀ u ∈ cfg 4 sbAugMask, f u = 1 ∨ f u = -1) →
      121 ≤ (violatedLines (cfg 4 sbAugMask) f).card) ∧
    (∃ f : Pt 4 → ℝ, (∀ u, f u = 1 ∨ f u = -1) ∧
      (violatedLines (cfg 4 sbAugMask) f).card = 127) := by
  refine ⟨fun f hf => disjoint_mp_grids_lower_bound sbAugMask sbAugDisjointGrids sbaug_grids_ok f hf, ?_⟩
  let f : Pt 4 → ℝ := fun u => ((sgnOf 4 sbExtNeg u : ℤ) : ℝ)
  refine ⟨f, sgnOf_values 4 sbExtNeg, ?_⟩
  have hv : (violated (cfg 4 sbAugMask) f).card = 6 * 127 := by
    have h := loop_blocks (fastViolRow 10 4 sbAugMask sbExtNeg) 16 16
    rcases sbaug_vb with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
    rw [loop_sixteen, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15] at h
    have e : (2 : ℕ) ^ (2 * 4) = 16 * 16 := by norm_num
    rw [card_violated_cfg_fast (b := 10) (N := 4) (by norm_num) (by norm_num), e]
    exact h.trans (by norm_num)
  have h6 := card_violated_eq_six (cfg 4 sbAugMask) (zero_not_mem_cfg (by decide)) f
  omega

end HoggarBound.DesarguesQuasiQuadric
