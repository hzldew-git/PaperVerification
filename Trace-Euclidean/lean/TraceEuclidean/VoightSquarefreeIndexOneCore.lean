import TraceEuclidean.VoightOrderIndexCore
import Mathlib.Data.Nat.Squarefree

/-!
# Exact field discriminants from one squarefree index-one certificate

This module contains only the generic theorem for a single certified row and
does not import the aggregate archived computations.
-/

namespace TraceEuclidean

noncomputable section

open NumberField Polynomial
open scoped Matrix NumberField

/-- A squarefree positive factor cannot contain a nontrivial square index. -/
theorem squarefree_squareFactor_eq_one
    (D a : ℕ) (E : ℤ)
    (hsquarefree : Squarefree D)
    (hfactor : (D : ℤ) = (a : ℤ) ^ 2 * E) :
    a = 1 ∧ E = (D : ℤ) := by
  have habs := congrArg Int.natAbs hfactor
  simp only [Int.natAbs_natCast, Int.natAbs_mul, Int.natAbs_pow] at habs
  have hdvd : a ^ 2 ∣ D := by
    rw [habs]
    exact dvd_mul_right _ _
  have hunit : IsUnit a := by
    by_contra hnot
    have hsquarefreePower : Squarefree (a ^ 2) :=
      hsquarefree.squarefree_of_dvd hdvd
    have hexponent :=
      hsquarefreePower.eq_zero_or_one_of_pow_of_not_isUnit hnot
    omega
  have ha : a = 1 := Nat.isUnit_iff.mp hunit
  subst a
  simpa using hfactor.symm

/-- The discriminant of any full integral family differs from the field
discriminant by the square of its determinant in an integral basis. -/
theorem integralFamily_discr_eq_det_sq_mul_fieldDiscriminant
    (K : Type*) [Field K] [NumberField K]
    (d : ℕ) (family : Fin d → RingOfIntegers K)
    (bO : Module.Basis (Fin d) ℤ (RingOfIntegers K)) :
    Algebra.discr ℤ family =
      (bO.toMatrix family).det ^ 2 * NumberField.discr K := by
  classical
  let P := bO.toMatrix family
  change Algebra.discr ℤ family = P.det ^ 2 * NumberField.discr K
  calc
    Algebra.discr ℤ family =
        Algebra.discr ℤ
          (Matrix.vecMul bO
            (P.map (algebraMap ℤ (RingOfIntegers K)))) := by
      rw [bO.toMatrix_map_vecMul family]
    _ = P.det ^ 2 * Algebra.discr ℤ bO :=
      Algebra.discr_of_matrix_vecMul bO P
    _ = P.det ^ 2 * NumberField.discr K := by
      rw [NumberField.discr_eq_discr K bO]

/-- An integral family of full cardinality with positive squarefree
discriminant is automatically exact at the field-discriminant level. -/
theorem fieldDiscriminant_eq_of_integralFamily_squarefree
    (K : Type*) [Field K] [NumberField K]
    (d D : ℕ) (hdegree : Module.finrank ℚ K = d)
    (family : Fin d → RingOfIntegers K)
    (hsquarefree : Squarefree D)
    (hfamily : Algebra.discr ℤ family = (D : ℤ)) :
    NumberField.discr K = (D : ℤ) := by
  obtain ⟨bO⟩ := exists_ringOfIntegers_basis_fin K d hdegree
  have hdet := integralFamily_discr_eq_det_sq_mul_fieldDiscriminant
    K d family bO
  rw [hfamily] at hdet
  have hfactor : (D : ℤ) =
      ((bO.toMatrix family).det.natAbs : ℤ) ^ 2 *
        NumberField.discr K := by
    simpa [sq_abs] using hdet
  exact (squarefree_squareFactor_eq_one D
    (bO.toMatrix family).det.natAbs (NumberField.discr K)
    hsquarefree hfactor).2

/-- Exact number-field semantics for one certified row. -/
def VoightPolynomialRow.PresentsExactTotallyRealNumberField
    (row : VoightPolynomialRow) : Prop :=
  ∃ hirrQ : Irreducible row.rationalPolynomial,
    letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
    NumberField.IsTotallyReal (AdjoinRoot row.rationalPolynomial) ∧
      Module.finrank ℚ (AdjoinRoot row.rationalPolynomial) =
        row.polynomial.natDegree ∧
      NumberField.discr (AdjoinRoot row.rationalPolynomial) =
        (row.fieldDiscriminant : ℤ)

/-- An indexed presentation with recorded index one and squarefree recorded
discriminant has the exact recorded field discriminant. -/
theorem VoightPolynomialRow.PresentsIndexedTotallyRealNumberField.exact_of_index_one_squarefree
    (row : VoightPolynomialRow)
    (hfull : row.PresentsIndexedTotallyRealNumberField)
    (hindex : row.index = 1)
    (hsquarefree : Squarefree row.fieldDiscriminant)
    (hrecorded : row.polynomial.discr =
      (row.index : ℤ) ^ 2 * (row.fieldDiscriminant : ℤ)) :
    row.PresentsExactTotallyRealNumberField := by
  rcases hfull with
    ⟨hirrQ, hreal, hdegree, a, hcoe, hmin, hgen,
      actualIndex, hactualPos, hactual, hiff⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  have hpolynomial : row.polynomial.discr =
      (row.fieldDiscriminant : ℤ) := by
    simpa [hindex] using hrecorded
  have hfactor : (row.fieldDiscriminant : ℤ) =
      (actualIndex : ℤ) ^ 2 *
        NumberField.discr (AdjoinRoot row.rationalPolynomial) :=
    hpolynomial.symm.trans hactual
  have hexact := squarefree_squareFactor_eq_one
    row.fieldDiscriminant actualIndex
    (NumberField.discr (AdjoinRoot row.rationalPolynomial))
    hsquarefree hfactor
  refine ⟨hirrQ, ?_⟩
  change NumberField.IsTotallyReal (AdjoinRoot row.rationalPolynomial) ∧
    Module.finrank ℚ (AdjoinRoot row.rationalPolynomial) =
      row.polynomial.natDegree ∧
    NumberField.discr (AdjoinRoot row.rationalPolynomial) =
      (row.fieldDiscriminant : ℤ)
  exact ⟨hreal, hdegree, hexact.2⟩

end

end TraceEuclidean
