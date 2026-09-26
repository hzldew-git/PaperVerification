import TraceEuclidean.V15HunterDiscriminantBoxes
import TraceEuclidean.V15VoightResultantCertificates

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

/-- Exact arithmetic property for every archived row: the defining polynomial
discriminant is the square of the power-order index times the recorded field
discriminant. -/
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

/-- The generated Bareiss certificates, together with the structural row
certificate, prove the discriminant identity for every archived polynomial. -/
theorem v15_voightPolynomialDiscriminantInput :
    V15VoightPolynomialDiscriminantInput := by
  intro degree row hrow
  have hvalid :=
    (List.all_eq_true.mp
      (v15_voightPolynomialRows_structural_certificate degree)) row hrow
  have hconditions :=
    (v15_voightPolynomialRow_structurallyValid_iff degree row).1 hvalid
  have hresultant :=
    (List.all_eq_true.mp
      (v15_voightPolynomialRows_resultant_certificate degree)) row hrow
  have hdegree : 0 < degree := by
    by_contra hnot
    have hzero : degree = 0 := Nat.eq_zero_of_not_pos hnot
    subst degree
    simp [v15VoightPolynomialRows] at hrow
  exact v15VoightPolynomial_discr_eq_of_certificate degree row hdegree
    hconditions.1 hconditions.2.1 hresultant

/-- A structurally valid archived row satisfying the checked discriminant
identity belongs to the exact indexed discriminant box. -/
theorem v15_voightPolynomialRow_mem_indexedDiscriminantBox_of_valid
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
    (v15_voightPolynomialDiscriminantInput degree row hrow)

/-- If Lean has checked every structural row condition in a degree table,
then every row is retained by the exact finite filter. -/
theorem v15_voightPolynomialRow_mem_indexedDiscriminantBox
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
    hrow
  exact (List.all_eq_true.mp hall) row hrow

end

end TraceEuclidean
