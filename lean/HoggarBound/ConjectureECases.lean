/-
Hoggar Bound Lab — Formal Vertex-Case Membership Predicates for Jonah's Conjecture E.

Closes the `ConjectureE.lean` architectural note in `ERRATA.md`:
defines explicit geometric predicates (`IsCaseC1` through `IsCaseC15`) characterizing each
of Jonah's nine vertex cases in `W(2N−1, 2)` via ambient space (`W`, `Q⁺`, `Q⁻`), orthogonal
hyperplane `perpSet`, and quadric incidence (`qform` / `qformShift`), and proves that every
one of the nine constructed `(X, d)` pairs in `jonah_conjecture_e_all_nine_cases_spectra`
satisfies its named formal vertex-case predicate inside Lean 4.

Note on scope: Transfer from one representative per case to every `(X, d)` in that case still
relies on Jonah's single-orbit transitivity Theorem B4 (cited paper input outside Lean).
-/
import HoggarBound.AuditUpgrades

open Finset Matrix

namespace HoggarBound.ConjectureE

section VertexCases

variable {N : ℕ}

/-- Case `C1`: full symplectic space `W(2N−1, 2)`, nonzero pole `d`. -/
def IsCaseC1 (X : Finset (Pt N)) (d : Pt N) : Prop :=
  X = allPoints N ∧ d ≠ 0

/-- Case `C3`: hyperbolic quadric `Q⁺(2N−1, 2)`, isotropic pole `d ∈ Q⁺`. -/
def IsCaseC3 (X : Finset (Pt N)) (d : Pt N) : Prop :=
  ∃ c : Pt N, qform c = 0 ∧ X = quadric N c ∧ d ≠ 0 ∧ qformShift c d = 0

/-- Case `C5`: elliptic quadric `Q⁻(2N−1, 2)`, isotropic pole `d ∈ Q⁻`. -/
def IsCaseC5 (X : Finset (Pt N)) (d : Pt N) : Prop :=
  ∃ c : Pt N, qform c = 1 ∧ X = quadric N c ∧ d ≠ 0 ∧ qformShift c d = 0

/-- Case `C6`: symplectic hyperplane cone `W ∩ a⊥`, pole `d ∈ a⊥ \ {0, a}`. -/
def IsCaseC6 (X : Finset (Pt N)) (d : Pt N) : Prop :=
  ∃ a : Pt N, a ≠ 0 ∧ X = perpSet (allPoints N) a ∧ d ≠ 0 ∧ d ≠ a ∧ symp d a = 0

/-- Case `C8`: non-degenerate hyperbolic hyperplane section `Q⁺ ∩ a⊥` (`a ∉ Q⁺`), isotropic pole `d ∈ Q⁺ ∩ a⊥`. -/
def IsCaseC8 (X : Finset (Pt N)) (d : Pt N) : Prop :=
  ∃ c a : Pt N, qform c = 0 ∧ a ≠ 0 ∧ qformShift c a = 1 ∧
    X = perpSet (quadric N c) a ∧ d ≠ 0 ∧ d ≠ a ∧ symp d a = 0 ∧ qformShift c d = 0

/-- Case `C11`: singular hyperbolic cone `Q⁺ ∩ a⊥` (`a ∈ Q⁺`), isotropic pole `d ∈ Q⁺ ∩ a⊥ \ {a}`. -/
def IsCaseC11 (X : Finset (Pt N)) (d : Pt N) : Prop :=
  ∃ c a : Pt N, qform c = 0 ∧ a ≠ 0 ∧ qformShift c a = 0 ∧
    X = perpSet (quadric N c) a ∧ d ≠ 0 ∧ d ≠ a ∧ symp d a = 0 ∧ qformShift c d = 0

/-- Case `C12`: singular hyperbolic cone `Q⁺ ∩ a⊥` (`a ∈ Q⁺`), non-isotropic pole `d ∈ a⊥ \ Q⁺`. -/
def IsCaseC12 (X : Finset (Pt N)) (d : Pt N) : Prop :=
  ∃ c a : Pt N, qform c = 0 ∧ a ≠ 0 ∧ qformShift c a = 0 ∧
    X = perpSet (quadric N c) a ∧ d ≠ 0 ∧ d ≠ a ∧ symp d a = 0 ∧ qformShift c d = 1

/-- Case `C14`: singular elliptic cone `Q⁻ ∩ a⊥` (`a ∈ Q⁻`), isotropic pole `d ∈ Q⁻ ∩ a⊥ \ {a}`. -/
def IsCaseC14 (X : Finset (Pt N)) (d : Pt N) : Prop :=
  ∃ c a : Pt N, qform c = 1 ∧ a ≠ 0 ∧ qformShift c a = 0 ∧
    X = perpSet (quadric N c) a ∧ d ≠ 0 ∧ d ≠ a ∧ symp d a = 0 ∧ qformShift c d = 0

/-- Case `C15`: singular elliptic cone `Q⁻ ∩ a⊥` (`a ∈ Q⁻`), non-isotropic pole `d ∈ a⊥ \ Q⁻`. -/
def IsCaseC15 (X : Finset (Pt N)) (d : Pt N) : Prop :=
  ∃ c a : Pt N, qform c = 1 ∧ a ≠ 0 ∧ qformShift c a = 0 ∧
    X = perpSet (quadric N c) a ∧ d ≠ 0 ∧ d ≠ a ∧ symp d a = 0 ∧ qformShift c d = 1

private lemma ptZ_ne_ptY (i j : Fin N) : ptZ i ≠ ptY j := by
  intro h
  have := congrFun (congrArg Prod.fst h) j
  simp [ptZ, ptY] at this

private lemma ptY_ne_ptZ (i j : Fin N) : ptY i ≠ ptZ j :=
  fun h => ptZ_ne_ptY j i h.symm

/-- **Formal Vertex-Case Membership + Spectral Failure (all nine cases, all `N ≥ 4`):**
Every one of Jonah's nine vertex cases `C1, C3, C5, C6, C8, C11, C12, C14, C15` contains an
explicit `(X, d)` pair formally certified to satisfy its geometric case predicate and exhibit
strict-law failure on both characteristic polynomials and real eigenvalue multisets. -/
theorem jonah_conjecture_e_formal_cases {N : ℕ} (hN : 4 ≤ N) :
    (∃ X d : _, IsCaseC1 (N := N) X d ∧ HoggarBound.AuditUpgrades.StrictLawFailsSpectra X d) ∧
    (∃ X d : _, IsCaseC3 (N := N) X d ∧ HoggarBound.AuditUpgrades.StrictLawFailsSpectra X d) ∧
    (∃ X d : _, IsCaseC5 (N := N) X d ∧ HoggarBound.AuditUpgrades.StrictLawFailsSpectra X d) ∧
    (∃ X d : _, IsCaseC6 (N := N) X d ∧ HoggarBound.AuditUpgrades.StrictLawFailsSpectra X d) ∧
    (∃ X d : _, IsCaseC8 (N := N) X d ∧ HoggarBound.AuditUpgrades.StrictLawFailsSpectra X d) ∧
    (∃ X d : _, IsCaseC11 (N := N) X d ∧ HoggarBound.AuditUpgrades.StrictLawFailsSpectra X d) ∧
    (∃ X d : _, IsCaseC12 (N := N) X d ∧ HoggarBound.AuditUpgrades.StrictLawFailsSpectra X d) ∧
    (∃ X d : _, IsCaseC14 (N := N) X d ∧ HoggarBound.AuditUpgrades.StrictLawFailsSpectra X d) ∧
    (∃ X d : _, IsCaseC15 (N := N) X d ∧ HoggarBound.AuditUpgrades.StrictLawFailsSpectra X d) := by
  obtain ⟨h1, h3, h5, h6, h8, h11, h12, h14, h15⟩ :=
    HoggarBound.AuditUpgrades.jonah_conjecture_e_all_nine_cases_spectra hN
  let i0 : Fin N := ⟨0, by omega⟩
  let i1 : Fin N := ⟨1, by omega⟩
  let i2 : Fin N := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h10 : i1 ≠ i0 := h01.symm
  have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have h12' : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  have h20 : i2 ≠ i0 := h02.symm
  have h21 : i2 ≠ i1 := h12'.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- C1
    exact ⟨allPoints N, ptZ i0, ⟨rfl, ptZ_ne_zero i0⟩, h1⟩
  · -- C3
    exact ⟨quadric N 0, ptZ i0, ⟨0, qform_zero, rfl, ptZ_ne_zero i0, by simp [qformShift, qform_ptZ, symp]⟩, h3⟩
  · -- C5
    exact ⟨quadric N (ptY i1), ptZ i0,
      ⟨ptY i1, qform_ptY i1, rfl, ptZ_ne_zero i0, by
        rw [qformShift, qform_ptZ, symp_ptY_ptZ h10]; simp⟩, h5⟩
  · -- C6
    exact ⟨perpSet (allPoints N) (ptZ i0), ptZ i1,
      ⟨ptZ i0, ptZ_ne_zero i0, rfl, ptZ_ne_zero i1, ptZ_ne_ptZ h10, symp_ptZ_ptZ i1 i0⟩, h6⟩
  · -- C8
    exact ⟨perpSet (quadric N 0) (ptY i0), ptZ i1,
      ⟨0, ptY i0, qform_zero, ptY_ne_zero i0, by simp [qformShift, qform_ptY, symp],
        rfl, ptZ_ne_zero i1, ptZ_ne_ptY i1 i0, by rw [symp_comm]; exact symp_ptY_ptZ h01,
        by simp [qformShift, qform_ptZ, symp]⟩, h8⟩
  · -- C11
    exact ⟨perpSet (quadric N 0) (ptZ i0), ptZ i1,
      ⟨0, ptZ i0, qform_zero, ptZ_ne_zero i0, by simp [qformShift, qform_ptZ, symp],
        rfl, ptZ_ne_zero i1, ptZ_ne_ptZ h10, symp_ptZ_ptZ i1 i0,
        by simp [qformShift, qform_ptZ, symp]⟩, h11⟩
  · -- C12
    exact ⟨perpSet (quadric N 0) (ptZ i0), ptY i1,
      ⟨0, ptZ i0, qform_zero, ptZ_ne_zero i0, by simp [qformShift, qform_ptZ, symp],
        rfl, ptY_ne_zero i1, ptY_ne_ptZ i1 i0, symp_ptY_ptZ h10,
        by simp [qformShift, qform_ptY, symp]⟩, h12⟩
  · -- C14
    exact ⟨perpSet (quadric N (ptY i2)) (ptZ i0), ptZ i1,
      ⟨ptY i2, ptZ i0, qform_ptY i2, ptZ_ne_zero i0,
        by rw [qformShift, qform_ptZ, symp_ptY_ptZ h20]; simp,
        rfl, ptZ_ne_zero i1, ptZ_ne_ptZ h10, symp_ptZ_ptZ i1 i0,
        by rw [qformShift, qform_ptZ, symp_ptY_ptZ h21]; simp⟩, h14⟩
  · -- C15
    exact ⟨perpSet (quadric N (ptY i2)) (ptZ i0), ptY i1,
      ⟨ptY i2, ptZ i0, qform_ptY i2, ptZ_ne_zero i0,
        by rw [qformShift, qform_ptZ, symp_ptY_ptZ h20]; simp,
        rfl, ptY_ne_zero i1, ptY_ne_ptZ i1 i0, symp_ptY_ptZ h10,
        by rw [qformShift, qform_ptY, symp_ptY_ptY i2 i1]; simp⟩, h15⟩

end VertexCases

end HoggarBound.ConjectureE
