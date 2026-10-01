import TraceEuclidean.DeterminantCertificate

/-!
# Kernel-replayed explicit resultant certificates

This module separates discovery of rational row operations from their proof.
The generated degree-five certificates below supply a literal operation list
and a literal upper-triangular matrix.  Lean checks the replay and diagonal
product by ordinary kernel reduction, without trusting compiled evaluation.
-/

namespace TraceEuclidean

open Matrix Polynomial

/-- A literal rational row reduction proves a determinant identity. -/
theorem det_eq_of_explicit_row_reduction {n : ℕ}
    (matrix reduced : Matrix (Fin n) (Fin n) ℚ)
    (operations : List (RowOperation n)) (expected : ℚ)
    (hreplay : RowOperation.applyAll operations matrix = reduced)
    (htriangular : reduced.BlockTriangular id)
    (hdiagonal :
      (∏ i, reduced i i) =
        RowOperation.multiplierAll operations * expected) :
    matrix.det = expected := by
  have hdet := RowOperation.det_applyAll operations matrix
  rw [hreplay, Matrix.det_of_upperTriangular htriangular,
    hdiagonal] at hdet
  exact (mul_left_cancel₀
    (RowOperation.multiplierAll_ne_zero operations) hdet).symm

/-- A resultant identity over the rationals supplies the corresponding
integral polynomial discriminant identity.  This is the compact interface
used by the Euclidean-resultant certificates for the degree-five frontier. -/
theorem voightPolynomial_discr_eq_of_resultant
    (degree : ℕ) (row : VoightPolynomialRow)
    (hdegree : 0 < degree)
    (hlength : row.coefficients.length = degree + 1)
    (hlast : row.coefficients.getLast? = some 1)
    (hresultant :
      let polynomial := row.polynomial.map (Int.castRingHom ℚ)
      polynomial.resultant polynomial.derivative degree (degree - 1) =
        voightExpectedResultant degree row) :
    row.polynomial.discr =
      (row.index : ℤ) ^ 2 * (row.fieldDiscriminant : ℤ) := by
  let polynomial := row.polynomial
  have hmonic : polynomial.IsMonicOfDegree degree :=
    voightPolynomial_isMonicOfDegree degree row hlength hlast
  have hdegreePolynomial : 0 < polynomial.degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos,
      hmonic.natDegree_eq]
    exact hdegree
  have hresultantZ :
      polynomial.resultant polynomial.derivative degree (degree - 1) =
        (-1 : ℤ) ^ (degree * (degree - 1) / 2) *
          polynomial.discr := by
    simpa [hmonic.natDegree_eq, hmonic.leadingCoeff_eq] using
      (Polynomial.resultant_deriv (f := polynomial) hdegreePolynomial)
  have hresultantQ :
      ((polynomial.resultant polynomial.derivative degree
          (degree - 1) : ℤ) : ℚ) =
        voightExpectedResultant degree row := by
    calc
      _ = (polynomial.map (Int.castRingHom ℚ)).resultant
          (polynomial.derivative.map (Int.castRingHom ℚ))
          degree (degree - 1) :=
        (Polynomial.resultant_map_map polynomial polynomial.derivative
          degree (degree - 1) (Int.castRingHom ℚ)).symm
      _ = (polynomial.map (Int.castRingHom ℚ)).resultant
          (polynomial.map (Int.castRingHom ℚ)).derivative
          degree (degree - 1) := by
        rw [Polynomial.derivative_map]
      _ = voightExpectedResultant degree row := hresultant
  have hsigned :
      (-1 : ℚ) ^ (degree * (degree - 1) / 2) *
          (polynomial.discr : ℚ) =
        (-1 : ℚ) ^ (degree * (degree - 1) / 2) *
          ((row.index : ℚ) ^ 2 *
            (row.fieldDiscriminant : ℚ)) := by
    calc
      _ = ((polynomial.resultant polynomial.derivative degree
          (degree - 1) : ℤ) : ℚ) := by
        rw [hresultantZ]
        push_cast
        rfl
      _ = voightExpectedResultant degree row := hresultantQ
      _ = _ := by
        simp [voightExpectedResultant]
        ring
  have hdiscriminantQ :
      (polynomial.discr : ℚ) =
        (row.index : ℚ) ^ 2 *
          (row.fieldDiscriminant : ℚ) :=
    mul_left_cancel₀
      (pow_ne_zero _ (by norm_num : (-1 : ℚ) ≠ 0)) hsigned
  exact_mod_cast hdiscriminantQ

/-- A kernel-checked determinant of the Sylvester matrix supplies the
polynomial discriminant identity used by the maximal-order certificates. -/
theorem voightPolynomial_discr_eq_of_resultant_det
    (degree : ℕ) (row : VoightPolynomialRow)
    (hdegree : 0 < degree)
    (hlength : row.coefficients.length = degree + 1)
    (hlast : row.coefficients.getLast? = some 1)
    (hdet :
      ((Int.castRingHom ℚ).mapMatrix
        (voightResultantMatrixInt degree row)).det =
        (voightExpectedResultantInt degree row : ℚ)) :
    row.polynomial.discr =
      (row.index : ℤ) ^ 2 * (row.fieldDiscriminant : ℤ) := by
  apply voightPolynomial_discr_eq_of_resultant
    degree row hdegree hlength hlast
  have hdet' := hdet
  rw [voightResultantMatrixInt_map,
    voightResultantMatrix_eq_sylvester] at hdet'
  simpa [Polynomial.resultant,
    voightExpectedResultantInt_cast] using hdet'

end TraceEuclidean
