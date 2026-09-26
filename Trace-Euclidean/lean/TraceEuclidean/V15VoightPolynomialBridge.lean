import TraceEuclidean.V15HunterDiscriminantBoxes
import TraceEuclidean.V15VoightDiscriminantData

/-!
# Full-polynomial bridge for the archived Voight tables

The generated data file now records every archived defining polynomial and
its power-order index.  This module connects those rows to the exact
discriminant-index filter used by the Hunter reduction.

The coefficient-to-polynomial-discriminant equality remains stated as one
precise arithmetic input.  The public Python generator and the independent
Mathematica check verify every concrete instance, while this file proves the
structural and finite-set consequences in Lean.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

/-- The finite set of defining polynomials in the archived table of degree
`degree`. -/
def v15VoightPolynomialBox (degree : ℕ) : Finset ℤ[X] :=
  (v15VoightPolynomialRows degree).toFinset.image
    V15VoightPolynomialRow.polynomial

/-- Every archived row contributes its defining polynomial to the associated
finite polynomial box. -/
theorem v15_voightPolynomial_mem_box
    {degree : ℕ} {row : V15VoightPolynomialRow}
    (hrow : row ∈ v15VoightPolynomialRows degree) :
    row.polynomial ∈ v15VoightPolynomialBox degree := by
  rw [v15VoightPolynomialBox, Finset.mem_image]
  exact ⟨row, by simpa using hrow, rfl⟩

/-- Exact arithmetic statement checked externally for every archived row:
the defining polynomial discriminant is the square of the power-order index
times the recorded field discriminant. -/
def V15VoightPolynomialDiscriminantInput : Prop :=
  ∀ degree row,
    row ∈ v15VoightPolynomialRows degree →
      row.polynomial.discr =
        (row.index : ℤ) ^ 2 * (row.fieldDiscriminant : ℤ)

/-- The executable structural predicate is equivalent to the four elementary
row conditions it records. -/
theorem v15_voightPolynomialRow_structurallyValid_iff
    (degree : ℕ) (row : V15VoightPolynomialRow) :
    row.structurallyValid degree = true ↔
      row.coefficients.length = degree + 1 ∧
      row.coefficients.getLast? = some 1 ∧
      0 < row.fieldDiscriminant ∧ 0 < row.index := by
  simp [V15VoightPolynomialRow.structurallyValid, and_assoc]

/-- A structurally valid archived row satisfying the checked discriminant
identity belongs to the exact indexed discriminant box. -/
theorem v15_voightPolynomialRow_mem_indexedDiscriminantBox_of_valid
    (hdiscriminant : V15VoightPolynomialDiscriminantInput)
    {degree : ℕ} {row : V15VoightPolynomialRow}
    (hrow : row ∈ v15VoightPolynomialRows degree)
    (hvalid : row.structurallyValid degree = true) :
    (row.polynomial, row.index) ∈
      v15IndexedDiscriminantBox (v15VoightPolynomialBox degree)
        (row.fieldDiscriminant : ℤ) := by
  have hconditions :=
    (v15_voightPolynomialRow_structurallyValid_iff degree row).1 hvalid
  exact v15_mem_indexedDiscriminantBox_of_relation
    (v15_voightPolynomial_mem_box hrow)
    (by exact_mod_cast (Nat.ne_of_gt hconditions.2.2.1))
    hconditions.2.2.2
    (hdiscriminant degree row hrow)

/-- If Lean has checked every structural row condition in a degree table,
then every row satisfying the externally replayed discriminant identity is
retained by the exact finite filter. -/
theorem v15_voightPolynomialRow_mem_indexedDiscriminantBox
    (hdiscriminant : V15VoightPolynomialDiscriminantInput)
    {degree : ℕ}
    (hall :
      (v15VoightPolynomialRows degree).all
        (V15VoightPolynomialRow.structurallyValid degree) = true)
    {row : V15VoightPolynomialRow}
    (hrow : row ∈ v15VoightPolynomialRows degree) :
    (row.polynomial, row.index) ∈
      v15IndexedDiscriminantBox (v15VoightPolynomialBox degree)
        (row.fieldDiscriminant : ℤ) := by
  apply v15_voightPolynomialRow_mem_indexedDiscriminantBox_of_valid
    hdiscriminant hrow
  exact (List.all_eq_true.mp hall) row hrow

end

end TraceEuclidean
