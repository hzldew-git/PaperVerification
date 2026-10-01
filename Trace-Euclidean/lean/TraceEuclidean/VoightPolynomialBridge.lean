import TraceEuclidean.HunterDiscriminantBoxes
import TraceEuclidean.VoightResultantCertificates

/-!
# Full-polynomial bridge for the archived Voight tables

The generated data file now records every archived defining polynomial and
its power-order index.  This module connects those rows to the exact
discriminant-index filter used by the Hunter reduction.

The generated integer Bareiss certificates prove every coefficient-to-
polynomial-discriminant equality.  The public Python generator and the
independent Mathematica check provide separate checks of the same rows.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

/-- The finite set of defining polynomials in the archived table of degree
`degree`. -/
def voightPolynomialBox (degree : ℕ) : Finset ℤ[X] :=
  (voightPolynomialRows degree).toFinset.image
    VoightPolynomialRow.polynomial

/-- Every archived row contributes its defining polynomial to the associated
finite polynomial box. -/
theorem voightPolynomial_mem_box
    {degree : ℕ} {row : VoightPolynomialRow}
    (hrow : row ∈ voightPolynomialRows degree) :
    row.polynomial ∈ voightPolynomialBox degree := by
  rw [voightPolynomialBox, Finset.mem_image]
  exact ⟨row, by simpa using hrow, rfl⟩

/-- Exact arithmetic property for every archived row: the defining polynomial
discriminant is the square of the power-order index times the recorded field
discriminant. -/
def VoightPolynomialDiscriminantInput : Prop :=
  ∀ degree row,
    row ∈ voightPolynomialRows degree →
      row.polynomial.discr =
        (row.index : ℤ) ^ 2 * (row.fieldDiscriminant : ℤ)

/-- The executable structural predicate is equivalent to the four elementary
row conditions it records. -/
theorem voightPolynomialRow_structurallyValid_iff
    (degree : ℕ) (row : VoightPolynomialRow) :
    row.structurallyValid degree = true ↔
      row.coefficients.length = degree + 1 ∧
      row.coefficients.getLast? = some 1 ∧
      0 < row.fieldDiscriminant ∧ 0 < row.index := by
  simp [VoightPolynomialRow.structurallyValid, and_assoc]

/-- The generated Bareiss certificates, together with the structural row
certificate, prove the discriminant identity for every archived polynomial. -/
theorem voightPolynomialDiscriminantInput :
    VoightPolynomialDiscriminantInput := by
  intro degree row hrow
  have hvalid :=
    (List.all_eq_true.mp
      (voightPolynomialRows_structural_certificate degree)) row hrow
  have hconditions :=
    (voightPolynomialRow_structurallyValid_iff degree row).1 hvalid
  have hresultant :=
    (List.all_eq_true.mp
      (voightPolynomialRows_resultant_certificate degree)) row hrow
  have hdegree : 0 < degree := by
    by_contra hnot
    have hzero : degree = 0 := Nat.eq_zero_of_not_pos hnot
    subst degree
    simp [voightPolynomialRows] at hrow
  exact voightPolynomial_discr_eq_of_certificate degree row hdegree
    hconditions.1 hconditions.2.1 hresultant

/-- A structurally valid archived row satisfying the checked discriminant
identity belongs to the exact indexed discriminant box. -/
theorem voightPolynomialRow_mem_indexedDiscriminantBox_of_valid
    {degree : ℕ} {row : VoightPolynomialRow}
    (hrow : row ∈ voightPolynomialRows degree)
    (hvalid : row.structurallyValid degree = true) :
    (row.polynomial, row.index) ∈
      indexedDiscriminantBox (voightPolynomialBox degree)
        (row.fieldDiscriminant : ℤ) := by
  have hconditions :=
    (voightPolynomialRow_structurallyValid_iff degree row).1 hvalid
  exact mem_indexedDiscriminantBox_of_relation
    (voightPolynomial_mem_box hrow)
    (by exact_mod_cast (Nat.ne_of_gt hconditions.2.2.1))
    hconditions.2.2.2
    (voightPolynomialDiscriminantInput degree row hrow)

/-- If Lean has checked every structural row condition in a degree table,
then every row is retained by the exact finite filter. -/
theorem voightPolynomialRow_mem_indexedDiscriminantBox
    {degree : ℕ}
    (hall :
      (voightPolynomialRows degree).all
        (VoightPolynomialRow.structurallyValid degree) = true)
    {row : VoightPolynomialRow}
    (hrow : row ∈ voightPolynomialRows degree) :
    (row.polynomial, row.index) ∈
      indexedDiscriminantBox (voightPolynomialBox degree)
        (row.fieldDiscriminant : ℤ) := by
  apply voightPolynomialRow_mem_indexedDiscriminantBox_of_valid
    hrow
  exact (List.all_eq_true.mp hall) row hrow

end

end TraceEuclidean
