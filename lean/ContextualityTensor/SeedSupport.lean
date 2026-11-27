import ContextualityTensor.PhysicalBridge
import ContextualityTensor.Support

/-!
# Literal Three-Qubit Pentagram Pauli Realization & Exact Seed-Support Identification

Closes the remaining Track 2 formalization items noted in `ERRATA.md`:
1. Constructs the 10 literal three-qubit Mermin pentagram Pauli observables (`ZII, IZI, IIZ,
   XII, IXI, IIX, ZZZ, ZXX, XZX, XXZ`) as real symmetric involutive `8×8` integer matrices
   embedding faithfully into complex `8×8` matrices, verifies mutual commutation and exact
   context products (`+I` on contexts `0..3`, `-I` on context `4`), and establishes the
   six-qubit disjoint two-pentagram physical bridge (`actual_six_qubit_pentagram_operator_sign`).
2. Computes the matrix anticommutation graphs `squareAnticommMatrix` (`L(K_{3,3})`, 4-regular,
   18 edges) and `pentagramAnticommMatrix` (Petersen graph, 3-regular, 15 edges) directly from
   `squareMatrix` and `pentagramMatrix`, and proves by kernel evaluation (`decide +kernel`)
   that their nonempty full supports (`graphSupportWithEmpty` in `Support.lean`) equal
   precisely `squareContext` (`HS(L(K_{3,3}))`) and `pentagramContext` (`HS(Petersen)`).
3. Instantiates `Support.lean` for arbitrary `k : ℕ`, proving that the nonempty full supports
   of the `k`-block disjoint anticommutation graphs coincide identically with
   `actualContexts (k := k) squareContext` and `actualContexts (k := k) pentagramContext`.
-/

open Finset Matrix
open scoped Kronecker

namespace ContextualityTensor

/-! ### Part 1. Three-qubit Mermin pentagram literal Pauli realization -/

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℤ
abbrev Qubit3Idx := (Fin 2 × Fin 2) × Fin 2
abbrev Mat8 := Matrix Qubit3Idx Qubit3Idx ℤ
abbrev Mat64 := Matrix (Qubit3Idx × Qubit3Idx) (Qubit3Idx × Qubit3Idx) ℤ

def matI2 : Mat2 := !![1, 0; 0, 1]
def matX2 : Mat2 := !![0, 1; 1, 0]
def matZ2 : Mat2 := !![1, 0; 0, -1]

def kron3 (A B C : Mat2) : Mat8 := (A ⊗ₖ B) ⊗ₖ C

/-- The ten three-qubit Mermin pentagram observables:
`ZII, IZI, IIZ, XII, IXI, IIX, ZZZ, ZXX, XZX, XXZ`.
All ten have real integral entries in `{-1, 0, +1}`, embedding faithfully into `ℂ`. -/
def pentagramMatrix : Fin 10 → Mat8 := ![
  kron3 matZ2 matI2 matI2,
  kron3 matI2 matZ2 matI2,
  kron3 matI2 matI2 matZ2,
  kron3 matX2 matI2 matI2,
  kron3 matI2 matX2 matI2,
  kron3 matI2 matI2 matX2,
  kron3 matZ2 matZ2 matZ2,
  kron3 matZ2 matX2 matX2,
  kron3 matX2 matZ2 matX2,
  kron3 matX2 matX2 matZ2]

def pentagramContextList : Fin 5 → List (Fin 10) :=
  ![[0, 1, 2, 6], [0, 4, 5, 7], [3, 1, 5, 8], [3, 4, 2, 9], [6, 7, 8, 9]]

theorem pentagram_context_list_matches (c : Fin 5) :
    (pentagramContextList c).toFinset = pentagramContext c := by
  revert c; decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pentagram_observables : ∀ i : Fin 10,
    pentagramMatrix i * pentagramMatrix i = 1 ∧ (pentagramMatrix i).transpose = pentagramMatrix i := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pentagram_observables_distinct : Function.Injective pentagramMatrix := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pentagram_observables_nonidentity : ∀ i : Fin 10, pentagramMatrix i ≠ 1 := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pentagram_context_commute : ∀ (c : Fin 5) (i j : Fin 10),
    i ∈ pentagramContext c → j ∈ pentagramContext c →
    pentagramMatrix i * pentagramMatrix j = pentagramMatrix j * pentagramMatrix i := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pentagram_context_products : ∀ c : Fin 5,
    ((pentagramContextList c).map pentagramMatrix).prod =
      if c == 4 then -(1 : Mat8) else 1 := by
  decide +kernel

theorem pentagram_complex_context (c : Fin 5) :
    (((pentagramContextList c).map pentagramMatrix).prod).map (Int.castRingHom ℂ) =
      ((sign (c == 4) : ℤ) : ℂ) • (1 : Matrix Qubit3Idx Qubit3Idx ℂ) := by
  rw [pentagram_context_products]
  ext i j
  by_cases hc : c == 4 <;> by_cases hij : i = j <;> simp [sign, hc, hij]

/-! ### Part 2. Six-qubit disjoint two-pentagram physical bridge -/

def pentagramLeftEmbed : Mat8 →* Mat64 where
  toFun A := A ⊗ₖ (1 : Mat8)
  map_one' := Matrix.one_kronecker_one
  map_mul' A B := by rw [← Matrix.mul_kronecker_mul]; simp

def pentagramRightEmbed : Mat8 →* Mat64 where
  toFun A := (1 : Mat8) ⊗ₖ A
  map_one' := Matrix.one_kronecker_one
  map_mul' A B := by rw [← Matrix.mul_kronecker_mul]; simp

def optionalPentagramContext : Option (Fin 5) → List (Fin 10)
  | none => []
  | some c => pentagramContextList c

def optionalPentagramSign : Option (Fin 5) → ℤ
  | none => 1
  | some c => sign (c == 4)

def sixQubitPentagramContext (c d : Option (Fin 5)) : List Mat64 :=
  ((optionalPentagramContext c).map fun i => pentagramLeftEmbed (pentagramMatrix i)) ++
  ((optionalPentagramContext d).map fun i => pentagramRightEmbed (pentagramMatrix i))

theorem optional_pentagram_context_product (c : Option (Fin 5)) :
    ((optionalPentagramContext c).map pentagramMatrix).prod = optionalPentagramSign c • (1 : Mat8) := by
  cases c with
  | none => simp [optionalPentagramContext, optionalPentagramSign]
  | some c =>
    rw [optionalPentagramContext, pentagram_context_products]
    by_cases h : c == 4 <;> simp [optionalPentagramSign, sign, h]

theorem six_qubit_pentagram_context_product (c d : Option (Fin 5)) :
    (sixQubitPentagramContext c d).prod =
      (optionalPentagramSign c * optionalPentagramSign d) • (1 : Mat64) := by
  simp only [sixQubitPentagramContext, List.prod_append]
  have hl : ((optionalPentagramContext c).map fun i => pentagramLeftEmbed (pentagramMatrix i)).prod =
      pentagramLeftEmbed (((optionalPentagramContext c).map pentagramMatrix).prod) := by
    rw [map_list_prod]; simp only [List.map_map, Function.comp_def]
  have hr : ((optionalPentagramContext d).map fun i => pentagramRightEmbed (pentagramMatrix i)).prod =
      pentagramRightEmbed (((optionalPentagramContext d).map pentagramMatrix).prod) := by
    rw [map_list_prod]; simp only [List.map_map, Function.comp_def]
  rw [hl, hr, optional_pentagram_context_product, optional_pentagram_context_product]
  change ((optionalPentagramSign c • (1 : Mat8)) ⊗ₖ (1 : Mat8)) *
      ((1 : Mat8) ⊗ₖ (optionalPentagramSign d • (1 : Mat8))) = _
  rw [Matrix.smul_kronecker, Matrix.kronecker_smul, Matrix.one_kronecker_one]
  simp

theorem optional_pentagram_sign_matches (q : Option (Fin 5)) :
    extend (fun c => sign (c == 4)) q = optionalPentagramSign q := by
  cases q <;> rfl

theorem actual_six_qubit_pentagram_sign (q : Fin 2 → Option (Fin 5)) (hq : q ∈ contexts 2 (Fin 5)) :
    actualSign pentagramContext (fun c => c == 4) (unionContext pentagramContext q) =
      optionalPentagramSign (q 0) * optionalPentagramSign (q 1) := by
  rw [actualSign_union pentagramContext _ pentagram_context_injective pentagram_context_nonempty q hq]
  simp only [Fin.prod_univ_two, optional_pentagram_sign_matches]

/-- The quantum scalar sign of all 35 nonempty six-qubit disjoint two-pentagram contexts
equals the combinatorial sign used by `actualViolations`. -/
theorem actual_six_qubit_pentagram_operator_sign (q : Fin 2 → Option (Fin 5))
    (hq : q ∈ contexts 2 (Fin 5)) :
    (sixQubitPentagramContext (q 0) (q 1)).prod =
      actualSign pentagramContext (fun c => c == 4) (unionContext pentagramContext q) • (1 : Mat64) := by
  rw [actual_six_qubit_pentagram_sign q hq]
  exact six_qubit_pentagram_context_product (q 0) (q 1)

theorem six_qubit_pentagram_complex_context (c d : Option (Fin 5)) :
    ((sixQubitPentagramContext c d).prod).map (Int.castRingHom ℂ) =
      ((optionalPentagramSign c * optionalPentagramSign d : ℤ) : ℂ) •
        (1 : Matrix (Qubit3Idx × Qubit3Idx) (Qubit3Idx × Qubit3Idx) ℂ) := by
  rw [six_qubit_pentagram_context_product]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases h : i = j <;> simp [h]

/-! ### Part 3. Matrix anticommutation graphs & exact `HS(L(K_{3,3}))`, `HS(Petersen)` identification -/

/-- Exact anticommutation matrix derived literally from `squareMatrix`. -/
def squareAnticommMatrix (i j : Fin 9) : ZMod 2 :=
  if squareMatrix i * squareMatrix j = squareMatrix j * squareMatrix i then 0 else 1

/-- Exact anticommutation matrix derived literally from `pentagramMatrix`. -/
def pentagramAnticommMatrix (i j : Fin 10) : ZMod 2 :=
  if pentagramMatrix i * pentagramMatrix j = pentagramMatrix j * pentagramMatrix i then 0 else 1

/-- Fast closed-form adjacency of `L(K_{3,3})`: two grid cells anticommute iff they lie in
different rows and different columns. -/
private def squareAdjFast (i j : Fin 9) : ZMod 2 :=
  if i.val / 3 ≠ j.val / 3 ∧ i.val % 3 ≠ j.val % 3 then 1 else 0

private def pentXMask : Fin 10 → Nat := ![0, 0, 0, 4, 2, 1, 0, 3, 5, 6]
private def pentZMask : Fin 10 → Nat := ![4, 2, 1, 0, 0, 0, 7, 4, 2, 1]

/-- Fast closed-form symplectic anticommutation adjacency of the Petersen graph on 10 vertices. -/
private def pentagramAdjFast (i j : Fin 10) : ZMod 2 :=
  let m := (pentXMask i &&& pentZMask j) ^^^ (pentZMask i &&& pentXMask j)
  if ((m &&& 1) + ((m >>> 1) &&& 1) + ((m >>> 2) &&& 1)) % 2 = 0 then 0 else 1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem squareAdjFast_eq_matrix : squareAdjFast = squareAnticommMatrix := by
  funext i j; revert i j; decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem pentagramAdjFast_eq_matrix : pentagramAdjFast = pentagramAnticommMatrix := by
  funext i j; revert i j; decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem square_seed_support_fast :
    ∀ s : Finset (Fin 9),
      (s.Nonempty ∧ graphSupportWithEmpty squareAdjFast s) ↔ ∃ c : Fin 6, s = squareContext c := by
  intro s
  unfold graphSupportWithEmpty
  revert s
  decide +kernel

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
private theorem pentagram_seed_support_fast :
    ∀ s : Finset (Fin 10),
      (s.Nonempty ∧ graphSupportWithEmpty pentagramAdjFast s) ↔ ∃ c : Fin 5, s = pentagramContext c := by
  intro s
  unfold graphSupportWithEmpty
  revert s
  decide +kernel

/-- **Exact `HS(L(K_{3,3}))` identification:** the nonempty full supports of the anticommutation
graph of the nine Peres–Mermin Pauli matrices are precisely the six contexts `squareContext`. -/
theorem square_seed_support_eq_hs (s : Finset (Fin 9)) :
    (s.Nonempty ∧ graphSupportWithEmpty squareAnticommMatrix s) ↔
      ∃ c : Fin 6, s = squareContext c := by
  rw [← squareAdjFast_eq_matrix]
  exact square_seed_support_fast s

/-- **Exact `HS(Petersen)` identification:** the nonempty full supports of the anticommutation
graph of the ten three-qubit Mermin pentagram Pauli matrices are precisely the five contexts
`pentagramContext`. -/
theorem pentagram_seed_support_eq_hs (s : Finset (Fin 10)) :
    (s.Nonempty ∧ graphSupportWithEmpty pentagramAnticommMatrix s) ↔
      ∃ c : Fin 5, s = pentagramContext c := by
  rw [← pentagramAdjFast_eq_matrix]
  exact pentagram_seed_support_fast s

/-! ### Part 4. Instantiation of `Support.lean` for arbitrary `k : ℕ` -/

/-- Embedding `Fin k × V ↪ Σ _ : Fin k, V` identifying tagged pairs with sigma vertices. -/
def prodToSigma {k : ℕ} {V : Type*} : (Fin k × V) ↪ (Σ _i : Fin k, V) where
  toFun p := ⟨p.1, p.2⟩
  inj' := by rintro ⟨i, u⟩ ⟨j, v⟩ h; cases h; rfl

theorem graphSupportWithEmpty_empty {W : Type*} [Fintype W] [DecidableEq W]
    (A : W → W → ZMod 2) : graphSupportWithEmpty A ∅ := by
  constructor
  · intro u hu; exact (Finset.notMem_empty u hu).elim
  · intro u; simp

/-- Generic bridge instantiating `Support.lean`: whenever the nonempty full supports of `A`
coincide with `seed`, the nonempty full supports of `k` disjoint blocks of `A` coincide
identically with `actualContexts (k := k) seed`. -/
theorem block_support_eq_actualContexts {k : ℕ} {C V : Type*} [Fintype C] [DecidableEq C]
    [Fintype V] [DecidableEq V] (A : V → V → ZMod 2) (seed : C → Finset V)
    (hne : ∀ c, (seed c).Nonempty)
    (hseed : ∀ t : Finset V, (t.Nonempty ∧ graphSupportWithEmpty A t) ↔ ∃ c : C, t = seed c)
    (s : Finset (Fin k × V)) :
    (s.Nonempty ∧ graphSupportWithEmpty (blockAdjacency (fun _ : Fin k => A)) s) ↔
      s.map prodToSigma ∈ actualContexts (k := k) seed := by
  classical
  constructor
  · rintro ⟨hsne, hsupp⟩
    have hfib := (graph_support_disjoint_iff (fun _ : Fin k => A) s).mp hsupp
    have hfib_opt : ∀ i : Fin k, ∃ o : Option C, supportFiber s i = selectedContext seed o := by
      intro i
      by_cases hi : (supportFiber s i).Nonempty
      · obtain ⟨c, hc⟩ := (hseed (supportFiber s i)).mp ⟨hi, hfib i⟩
        exact ⟨some c, hc⟩
      · exact ⟨none, Finset.not_nonempty_iff_eq_empty.mp hi⟩
    choose q hq using hfib_opt
    have hq_ne : q ≠ emptyChoice := by
      intro heq
      obtain ⟨i, hi⟩ := (support_nonempty_iff s).mp hsne
      have h0 : supportFiber s i = ∅ := by
        rw [hq i, heq]; rfl
      exact hi.ne_empty h0
    have hq_mem : q ∈ contexts k C := Finset.mem_erase.mpr ⟨hq_ne, Finset.mem_univ q⟩
    refine Finset.mem_image.mpr ⟨q, hq_mem, ?_⟩
    ext ⟨i, v⟩
    simp only [unionContext, Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_map,
      prodToSigma]
    constructor
    · intro hv
      have hvs : (i, v) ∈ s := (mem_supportFiber s i v).mp (by rw [hq i]; exact hv)
      exact ⟨(i, v), hvs, rfl⟩
    · rintro ⟨⟨j, w⟩, hmem, heq⟩
      cases heq
      rw [← hq j]
      exact (mem_supportFiber s j w).mpr hmem
  · intro hmem
    obtain ⟨q, hq_mem, hq_eq⟩ := Finset.mem_image.mp hmem
    have hfib_eq : ∀ i : Fin k, supportFiber s i = selectedContext seed (q i) := by
      intro i
      ext v
      have hiff : (⟨i, v⟩ : Σ _ : Fin k, V) ∈ unionContext seed q ↔
          (⟨i, v⟩ : Σ _ : Fin k, V) ∈ s.map prodToSigma := by rw [hq_eq]
      simp only [unionContext, Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_map,
        prodToSigma] at hiff
      rw [mem_supportFiber, hiff]
      constructor
      · intro hv; exact ⟨(i, v), hv, rfl⟩
      · rintro ⟨⟨j, w⟩, hw, heq⟩; cases heq; exact hw
    constructor
    · rw [support_nonempty_iff]
      have hq_ne : q ≠ emptyChoice := (Finset.mem_erase.mp hq_mem).1
      by_contra hall
      simp only [not_exists, Finset.not_nonempty_iff_eq_empty] at hall
      apply hq_ne
      funext i
      cases hqi : q i with
      | none => rfl
      | some c =>
        have hempty : supportFiber s i = ∅ := hall i
        rw [hfib_eq i, hqi] at hempty
        exact ((hne c).ne_empty hempty).elim
    · rw [graph_support_disjoint_iff]
      intro i
      rw [hfib_eq i]
      cases hqi : q i with
      | none => exact graphSupportWithEmpty_empty A
      | some c => exact ((hseed (seed c)).mpr ⟨c, rfl⟩).2

/-- For every `k : ℕ`, the nonempty full supports of `k` disjoint copies of the Peres–Mermin
anticommutation graph `L(K_{3,3})` coincide identically with `actualContexts (k := k) squareContext`. -/
theorem square_kblock_support_iff (k : ℕ) (s : Finset (Fin k × Fin 9)) :
    (s.Nonempty ∧ graphSupportWithEmpty (blockAdjacency (fun _ : Fin k => squareAnticommMatrix)) s) ↔
      s.map prodToSigma ∈ actualContexts (k := k) squareContext :=
  block_support_eq_actualContexts squareAnticommMatrix squareContext
    square_context_nonempty square_seed_support_eq_hs s

/-- For every `k : ℕ`, the nonempty full supports of `k` disjoint copies of the Mermin pentagram
anticommutation graph (`Petersen`) coincide identically with `actualContexts (k := k) pentagramContext`. -/
theorem pentagram_kblock_support_iff (k : ℕ) (s : Finset (Fin k × Fin 10)) :
    (s.Nonempty ∧ graphSupportWithEmpty (blockAdjacency (fun _ : Fin k => pentagramAnticommMatrix)) s) ↔
      s.map prodToSigma ∈ actualContexts (k := k) pentagramContext :=
  block_support_eq_actualContexts pentagramAnticommMatrix pentagramContext
    pentagram_context_nonempty pentagram_seed_support_eq_hs s

end ContextualityTensor
