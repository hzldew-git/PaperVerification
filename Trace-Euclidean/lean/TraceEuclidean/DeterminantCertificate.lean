import TraceEuclidean.IntegralDeterminantCertificate

/-!
# Executable determinant certificates for the Voight polynomial rows

This file provides a small certificate language for exact rational row
reduction.  The mathematical theorem is independent of the reduction
algorithm: a certificate is accepted only when replaying its elementary row
operations produces an upper triangular matrix with the claimed diagonal
product.
-/

namespace TraceEuclidean

open Matrix Polynomial

/-- Elementary rational row operations used by the determinant checker. -/
inductive RowOperation (n : ℕ) where
  | add (target source : Fin n) (scalar : ℚ)
  | swap (first second : Fin n)
deriving DecidableEq, Repr

namespace RowOperation

/-- Replay one elementary row operation.  An attempted addition of a row to
itself is treated as the identity operation. -/
def apply {n : ℕ} (operation : RowOperation n)
    (matrix : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  match operation with
  | .add target source scalar =>
      if target = source then matrix
      else matrix.updateRow target (matrix target + scalar • matrix source)
  | .swap first second =>
      matrix.submatrix (Equiv.swap first second) id

/-- The factor by which one operation changes the determinant. -/
def multiplier {n : ℕ} : RowOperation n → ℚ
  | .add _ _ _ => 1
  | .swap first second => if first = second then 1 else -1

/-- The determinant effect of one replayed row operation. -/
theorem det_apply {n : ℕ} (operation : RowOperation n)
    (matrix : Matrix (Fin n) (Fin n) ℚ) :
    (operation.apply matrix).det = operation.multiplier * matrix.det := by
  cases operation with
  | add target source scalar =>
      by_cases h : target = source
      · simp [apply, multiplier, h]
      · simp [apply, multiplier, h,
          Matrix.det_updateRow_add_smul_self matrix h]
  | swap first second =>
      rw [apply, Matrix.det_permute]
      by_cases h : first = second
      · simp [multiplier, h]
      · simp [multiplier, h, Equiv.Perm.sign_swap h]

/-- Replay a sequence of elementary row operations. -/
def applyAll {n : ℕ} :
    List (RowOperation n) →
      Matrix (Fin n) (Fin n) ℚ → Matrix (Fin n) (Fin n) ℚ
  | [], matrix => matrix
  | operation :: operations, matrix =>
      applyAll operations (operation.apply matrix)

/-- The determinant multiplier of a sequence of row operations. -/
def multiplierAll {n : ℕ} : List (RowOperation n) → ℚ
  | [] => 1
  | operation :: operations =>
      operation.multiplier * multiplierAll operations

/-- Replaying a sequence multiplies the determinant by the product of its
elementary multipliers. -/
theorem det_applyAll {n : ℕ} (operations : List (RowOperation n))
    (matrix : Matrix (Fin n) (Fin n) ℚ) :
    (applyAll operations matrix).det =
      multiplierAll operations * matrix.det := by
  induction operations generalizing matrix with
  | nil => simp [applyAll, multiplierAll]
  | cons operation operations induction =>
      rw [applyAll, induction, det_apply]
      simp only [multiplierAll]
      ring

/-- Every row-operation multiplier is nonzero. -/
theorem multiplier_ne_zero {n : ℕ} (operation : RowOperation n) :
    operation.multiplier ≠ 0 := by
  cases operation with
  | add => simp [multiplier]
  | swap first second =>
      by_cases h : first = second <;> simp [multiplier, h]

/-- Every multiplier produced by a sequence of row operations is nonzero. -/
theorem multiplierAll_ne_zero {n : ℕ}
    (operations : List (RowOperation n)) :
    multiplierAll operations ≠ 0 := by
  induction operations with
  | nil => simp [multiplierAll]
  | cons operation operations induction =>
      simp only [multiplierAll]
      exact mul_ne_zero (multiplier_ne_zero operation) induction

end RowOperation

/-- Find a nonzero pivot in the current column at or below the diagonal. -/
def findPivot {n : ℕ} (matrix : Matrix (Fin n) (Fin n) ℚ)
    (pivot : Fin n) : Option (Fin n) :=
  (List.finRange n).find? fun row =>
    decide (pivot ≤ row ∧ matrix row pivot ≠ 0)

/-- Eliminate the entries below one nonzero pivot and record the row
operations used. -/
def eliminateBelow {n : ℕ} (pivot : Fin n) :
    List (Fin n) → Matrix (Fin n) (Fin n) ℚ →
      List (RowOperation n) × Matrix (Fin n) (Fin n) ℚ
  | [], matrix => ([], matrix)
  | row :: rows, matrix =>
      if pivot < row then
        let operation := RowOperation.add row pivot
          (-(matrix row pivot / matrix pivot pivot))
        let result := eliminateBelow pivot rows (operation.apply matrix)
        (operation :: result.1, result.2)
      else
        eliminateBelow pivot rows matrix

/-- Fraction-free trust is not needed here: rational Gaussian elimination is
used only to *produce* elementary operations.  The checker later replays the
operations and verifies the resulting triangular matrix. -/
def gaussianAux {n : ℕ} :
    List (Fin n) → Matrix (Fin n) (Fin n) ℚ →
      List (RowOperation n) × Matrix (Fin n) (Fin n) ℚ
  | [], matrix => ([], matrix)
  | pivot :: pivots, matrix =>
      match findPivot matrix pivot with
      | none => gaussianAux pivots matrix
      | some pivotRow =>
          let swapOperation := RowOperation.swap pivot pivotRow
          let swapped := swapOperation.apply matrix
          let eliminated := eliminateBelow pivot (List.finRange n) swapped
          let remaining := gaussianAux pivots eliminated.2
          (swapOperation :: eliminated.1 ++ remaining.1, remaining.2)

/-- Operations proposed by exact rational Gaussian elimination. -/
def gaussianOperations {n : ℕ}
    (matrix : Matrix (Fin n) (Fin n) ℚ) :
    List (RowOperation n) :=
  (gaussianAux (List.finRange n) matrix).1

/-- Executable upper-triangularity test. -/
def isUpperTriangular {n : ℕ}
    (matrix : Matrix (Fin n) (Fin n) ℚ) : Bool :=
  (List.finRange n).all fun row =>
    (List.finRange n).all fun column =>
      decide (column < row → matrix row column = 0)

/-- Passing the executable test gives mathlib's upper-triangular predicate. -/
theorem blockTriangular_of_isUpperTriangular {n : ℕ}
    {matrix : Matrix (Fin n) (Fin n) ℚ}
    (h : isUpperTriangular matrix = true) :
    matrix.BlockTriangular id := by
  intro row column hcolumn
  have hrow := (List.all_eq_true.mp h) row (List.mem_finRange row)
  have hentry :=
    (List.all_eq_true.mp hrow) column (List.mem_finRange column)
  exact (of_decide_eq_true hentry) hcolumn

/-- A determinant certificate says that replay reaches an upper triangular
matrix and that its diagonal product has the claimed value after accounting
for row swaps. -/
def DeterminantCertificate {n : ℕ}
    (matrix : Matrix (Fin n) (Fin n) ℚ) (expected : ℚ) : Bool :=
  let operations := gaussianOperations matrix
  let reduced := RowOperation.applyAll operations matrix
  isUpperTriangular reduced &&
    decide ((∏ i, reduced i i) =
      RowOperation.multiplierAll operations * expected)

/-- A successfully replayed certificate proves the determinant claimed by
the certificate. -/
theorem det_eq_of_determinantCertificate {n : ℕ}
    {matrix : Matrix (Fin n) (Fin n) ℚ} {expected : ℚ}
    (certificate : DeterminantCertificate matrix expected = true) :
    matrix.det = expected := by
  let operations := gaussianOperations matrix
  let reduced := RowOperation.applyAll operations matrix
  have hcertificate :
      isUpperTriangular reduced = true ∧
        decide ((∏ i, reduced i i) =
          RowOperation.multiplierAll operations * expected) = true := by
    simpa [DeterminantCertificate, operations, reduced] using certificate
  have htriangular : reduced.BlockTriangular id :=
    blockTriangular_of_isUpperTriangular hcertificate.1
  have hdiagonal :
      (∏ i, reduced i i) =
        RowOperation.multiplierAll operations * expected :=
    of_decide_eq_true hcertificate.2
  have hreplay := RowOperation.det_applyAll operations matrix
  rw [Matrix.det_of_upperTriangular htriangular, hdiagonal] at hreplay
  exact (mul_left_cancel₀
    (RowOperation.multiplierAll_ne_zero operations) hreplay).symm

/-- A coefficient of an archived defining polynomial, cast to the rationals. -/
def voightCoefficient (row : VoightPolynomialRow) (exponent : ℕ) : ℚ :=
  (row.coefficients.getD exponent 0 : ℚ)

/-- A coefficient of the derivative of an archived defining polynomial. -/
def voightDerivativeCoefficient
    (row : VoightPolynomialRow) (exponent : ℕ) : ℚ :=
  (exponent + 1 : ℚ) * voightCoefficient row (exponent + 1)

/-- Integer coefficient lookup used by the Bareiss checker. -/
def voightCoefficientInt
    (row : VoightPolynomialRow) (exponent : ℕ) : ℤ :=
  row.coefficients.getD exponent 0

/-- Integer derivative coefficient used by the Bareiss checker. -/
def voightDerivativeCoefficientInt
    (row : VoightPolynomialRow) (exponent : ℕ) : ℤ :=
  (exponent + 1 : ℤ) * voightCoefficientInt row (exponent + 1)

/-- The list-backed polynomial has exactly the encoded coefficients. -/
@[simp]
theorem voightPolynomial_coeff (row : VoightPolynomialRow)
    (exponent : ℕ) :
    row.polynomial.coeff exponent = row.coefficients.getD exponent 0 := by
  simp [VoightPolynomialRow.polynomial, List.toFinsupp_apply]

/-- After mapping to the rationals, the coefficient function is the
computable list lookup used by the certificate matrix. -/
@[simp]
theorem voightPolynomial_map_coeff (row : VoightPolynomialRow)
    (exponent : ℕ) :
    (row.polynomial.map (Int.castRingHom ℚ)).coeff exponent =
      voightCoefficient row exponent := by
  simp [voightCoefficient]

/-- The computable rational Sylvester matrix whose determinant is the
resultant of an archived defining polynomial and its derivative. -/
def voightResultantMatrix (degree : ℕ) (row : VoightPolynomialRow) :
    Matrix (Fin (degree + (degree - 1)))
      (Fin (degree + (degree - 1))) ℚ :=
  Matrix.of fun matrixRow matrixColumn =>
    if matrixColumn.val < degree then
      if matrixColumn.val ≤ matrixRow.val ∧
          matrixRow.val ≤ matrixColumn.val + (degree - 1) then
        voightDerivativeCoefficient row
          (matrixRow.val - matrixColumn.val)
      else 0
    else
      let offset := matrixColumn.val - degree
      if offset ≤ matrixRow.val ∧ matrixRow.val ≤ offset + degree then
        voightCoefficient row (matrixRow.val - offset)
      else 0

/-- Integer Sylvester matrix replayed by the Bareiss checker. -/
def voightResultantMatrixInt
    (degree : ℕ) (row : VoightPolynomialRow) :
    Matrix (Fin (degree + (degree - 1)))
      (Fin (degree + (degree - 1))) ℤ :=
  Matrix.of fun matrixRow matrixColumn =>
    if matrixColumn.val < degree then
      if matrixColumn.val ≤ matrixRow.val ∧
          matrixRow.val ≤ matrixColumn.val + (degree - 1) then
        voightDerivativeCoefficientInt row
          (matrixRow.val - matrixColumn.val)
      else 0
    else
      let offset := matrixColumn.val - degree
      if offset ≤ matrixRow.val ∧ matrixRow.val ≤ offset + degree then
        voightCoefficientInt row (matrixRow.val - offset)
      else 0

/-- Casting the integer certificate matrix gives the rational matrix used in
the resultant bridge. -/
theorem voightResultantMatrixInt_map
    (degree : ℕ) (row : VoightPolynomialRow) :
    (Int.castRingHom ℚ).mapMatrix
        (voightResultantMatrixInt degree row) =
      voightResultantMatrix degree row := by
  ext matrixRow matrixColumn
  simp [voightResultantMatrixInt, voightResultantMatrix,
    voightDerivativeCoefficientInt, voightDerivativeCoefficient,
    voightCoefficientInt, voightCoefficient]

/-- The computable certificate matrix is definitionally the Sylvester
matrix used by mathlib's resultant. -/
theorem voightResultantMatrix_eq_sylvester
    (degree : ℕ) (row : VoightPolynomialRow) :
    voightResultantMatrix degree row =
      let polynomial := row.polynomial.map (Int.castRingHom ℚ)
      polynomial.sylvester polynomial.derivative degree (degree - 1) := by
  ext matrixRow matrixColumn
  induction matrixColumn using Fin.addCases with
  | left column =>
      simp [voightResultantMatrix, Polynomial.sylvester,
        voightDerivativeCoefficient, coeff_derivative]
      simp only [Fin.le_iff_val_le_val, Fin.val_castAdd]
      simp [voightCoefficient, mul_comm]
  | right column =>
      simp [voightResultantMatrix, Polynomial.sylvester,
        voightCoefficient]
      simp only [Nat.add_comm matrixRow.val degree,
        Nat.add_le_add_iff_left]

/-- The structural length and final-coefficient conditions make the encoded
polynomial monic of the recorded degree. -/
theorem voightPolynomial_isMonicOfDegree
    (degree : ℕ) (row : VoightPolynomialRow)
    (hlength : row.coefficients.length = degree + 1)
    (hlast : row.coefficients.getLast? = some 1) :
    row.polynomial.IsMonicOfDegree degree := by
  rw [Polynomial.isMonicOfDegree_iff]
  constructor
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro exponent hexponent
    rw [voightPolynomial_coeff,
      List.getD_eq_default row.coefficients 0]
    omega
  · rw [voightPolynomial_coeff, List.getD_eq_getElem?_getD]
    have hlast' := hlast
    rw [List.getLast?_eq_getElem?, hlength] at hlast'
    simp only [Nat.add_sub_cancel] at hlast'
    rw [hlast']
    rfl

/-- The resultant predicted by the archived field discriminant and the
power-order index. -/
def voightExpectedResultant (degree : ℕ)
    (row : VoightPolynomialRow) : ℚ :=
  (-1 : ℚ) ^ (degree * (degree - 1) / 2) *
    (row.index : ℚ) ^ 2 * (row.fieldDiscriminant : ℚ)

/-- Integral form of the resultant predicted by the archived row. -/
def voightExpectedResultantInt (degree : ℕ)
    (row : VoightPolynomialRow) : ℤ :=
  (-1 : ℤ) ^ (degree * (degree - 1) / 2) *
    (row.index : ℤ) ^ 2 * (row.fieldDiscriminant : ℤ)

/-- The integral expected resultant casts to the rational expression used by
the polynomial bridge. -/
theorem voightExpectedResultantInt_cast
    (degree : ℕ) (row : VoightPolynomialRow) :
    (voightExpectedResultantInt degree row : ℚ) =
      voightExpectedResultant degree row := by
  simp [voightExpectedResultantInt, voightExpectedResultant]

/-- Executable resultant certificate for one archived polynomial row. -/
def voightResultantCertificate (degree : ℕ)
    (row : VoightPolynomialRow) : Bool :=
  IntegralDeterminantCertificate
    (voightResultantMatrixInt degree row)
    (voightExpectedResultantInt degree row)

/-- A checked row certificate proves the corresponding rational resultant
identity for mathlib's polynomial. -/
theorem voightResultant_eq_expected_of_certificate
    (degree : ℕ) (row : VoightPolynomialRow)
    (hcertificate : voightResultantCertificate degree row = true) :
    let polynomial := row.polynomial.map (Int.castRingHom ℚ)
    polynomial.resultant polynomial.derivative degree (degree - 1) =
      voightExpectedResultant degree row := by
  have hdet :=
    det_map_eq_of_integralDeterminantCertificate hcertificate
  rw [voightResultantMatrixInt_map,
    voightResultantMatrix_eq_sylvester] at hdet
  simpa [voightResultantCertificate, Polynomial.resultant,
    voightExpectedResultantInt_cast] using hdet

/-- A checked determinant certificate and the elementary structural row
conditions prove the integral polynomial-discriminant identity. -/
theorem voightPolynomial_discr_eq_of_certificate
    (degree : ℕ) (row : VoightPolynomialRow)
    (hdegree : 0 < degree)
    (hlength : row.coefficients.length = degree + 1)
    (hlast : row.coefficients.getLast? = some 1)
    (hcertificate : voightResultantCertificate degree row = true) :
    row.polynomial.discr =
      (row.index : ℤ) ^ 2 * (row.fieldDiscriminant : ℤ) := by
  let polynomial := row.polynomial
  let polynomialQ := polynomial.map (Int.castRingHom ℚ)
  have hmonic : polynomial.IsMonicOfDegree degree :=
    voightPolynomial_isMonicOfDegree degree row hlength hlast
  have hdegreePolynomial : 0 < polynomial.degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos,
      hmonic.natDegree_eq]
    exact hdegree
  have hresultantZ :
      polynomial.resultant polynomial.derivative degree (degree - 1) =
        (-1 : ℤ) ^ (degree * (degree - 1) / 2) * polynomial.discr := by
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
      _ = voightExpectedResultant degree row := by
        simpa [polynomial] using
          (voightResultant_eq_expected_of_certificate
            degree row hcertificate)
  have hsigned :
      (-1 : ℚ) ^ (degree * (degree - 1) / 2) *
          (polynomial.discr : ℚ) =
        (-1 : ℚ) ^ (degree * (degree - 1) / 2) *
          ((row.index : ℚ) ^ 2 * (row.fieldDiscriminant : ℚ)) := by
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
        (row.index : ℚ) ^ 2 * (row.fieldDiscriminant : ℚ) :=
    mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (-1 : ℚ) ≠ 0)) hsigned
  exact_mod_cast hdiscriminantQ

end TraceEuclidean
