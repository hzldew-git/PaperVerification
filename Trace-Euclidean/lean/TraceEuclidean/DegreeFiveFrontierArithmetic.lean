import TraceEuclidean.ExplicitResultantCertificate
import TraceEuclidean.DensePolynomialCertificate

/-!
# Pure-kernel arithmetic for the final degree-five Hunter frontier

This module supplies the reusable reflection lemmas for reducible polynomial
certificates and for lower bounds that survive division by an arbitrary
positive square index.
-/

namespace TraceEuclidean

open Polynomial

/-! Interpret an ascending integer coefficient list as a polynomial. -/
def polynomialOfCoefficients (coefficients : List ℤ) : ℤ[X] :=
  (VoightPolynomialRow.mk 0 coefficients 0).polynomial

theorem degreeFive_eq_polynomialOfCoefficients
    {f : ℤ[X]} (hmonic : f.Monic) (hdegree : f.natDegree = 5) :
    f = polynomialOfCoefficients
      [f.coeff 0, f.coeff 1, f.coeff 2,
        f.coeff 3, f.coeff 4, 1] := by
  ext exponent
  rw [polynomialOfCoefficients, voightPolynomial_coeff]
  by_cases hle : exponent ≤ 5
  · interval_cases exponent <;> simp
    rw [← hdegree]
    exact hmonic.coeff_natDegree
  · have hlt : f.natDegree < exponent := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    change 0 = ([f.coeff 0, f.coeff 1, f.coeff 2,
      f.coeff 3, f.coeff 4, 1] : List ℤ).getD exponent 0
    symm
    exact List.getD_eq_default (l :=
      [f.coeff 0, f.coeff 1, f.coeff 2,
        f.coeff 3, f.coeff 4, 1]) (d := 0) (by simp; omega)

/-! A nontrivial factorization certificate in ascending coefficient order. -/
structure PolynomialFactorCertificate where
  coefficients : List ℤ
  leftFactor : List ℤ
  rightFactor : List ℤ
  leftDegree : ℕ
  rightDegree : ℕ
deriving DecidableEq, Repr

def PolynomialFactorCertificate.check
    (certificate : PolynomialFactorCertificate) : Bool :=
  DensePolynomial.equal certificate.coefficients
      (DensePolynomial.mul certificate.leftFactor
        certificate.rightFactor) &&
    decide (0 < certificate.leftDegree) &&
    decide (certificate.leftFactor.getD certificate.leftDegree 0 ≠ 0) &&
    decide (0 < certificate.rightDegree) &&
    decide (certificate.rightFactor.getD certificate.rightDegree 0 ≠ 0)

theorem polynomialOfCoefficients_eq_dense
    (coefficients : List ℤ) :
    polynomialOfCoefficients coefficients =
      DensePolynomial.toPolynomial coefficients := by
  ext exponent
  rw [polynomialOfCoefficients, voightPolynomial_coeff,
    DensePolynomial.coeff_toPolynomial]

theorem not_irreducible_of_factorCertificate
    (certificate : PolynomialFactorCertificate)
    (hcheck : certificate.check = true) :
    ¬Irreducible (polynomialOfCoefficients certificate.coefficients) := by
  have hparts :
      DensePolynomial.equal certificate.coefficients
          (DensePolynomial.mul certificate.leftFactor
            certificate.rightFactor) = true ∧
        0 < certificate.leftDegree ∧
        certificate.leftFactor.getD certificate.leftDegree 0 ≠ 0 ∧
        0 < certificate.rightDegree ∧
        certificate.rightFactor.getD certificate.rightDegree 0 ≠ 0 := by
    simpa [PolynomialFactorCertificate.check, Bool.and_assoc] using hcheck
  have hmul :
      polynomialOfCoefficients certificate.coefficients =
        polynomialOfCoefficients certificate.leftFactor *
          polynomialOfCoefficients certificate.rightFactor := by
    rw [polynomialOfCoefficients_eq_dense,
      polynomialOfCoefficients_eq_dense,
      polynomialOfCoefficients_eq_dense,
      ← DensePolynomial.toPolynomial_mul]
    exact DensePolynomial.toPolynomial_eq_of_equal hparts.1
  have hleftCoeff :
      (polynomialOfCoefficients certificate.leftFactor).coeff
        certificate.leftDegree ≠ 0 := by
    rw [polynomialOfCoefficients_eq_dense,
      DensePolynomial.coeff_toPolynomial]
    exact hparts.2.2.1
  have hrightCoeff :
      (polynomialOfCoefficients certificate.rightFactor).coeff
        certificate.rightDegree ≠ 0 := by
    rw [polynomialOfCoefficients_eq_dense,
      DensePolynomial.coeff_toPolynomial]
    exact hparts.2.2.2.2
  have hleftDegree :
      0 < (polynomialOfCoefficients certificate.leftFactor).natDegree :=
    hparts.2.1.trans_le (Polynomial.le_natDegree_of_ne_zero hleftCoeff)
  have hrightDegree :
      0 < (polynomialOfCoefficients certificate.rightFactor).natDegree :=
    hparts.2.2.2.1.trans_le
      (Polynomial.le_natDegree_of_ne_zero hrightCoeff)
  intro hirreducible
  rcases hirreducible.isUnit_or_isUnit hmul with hleft | hright
  · exact (Polynomial.not_isUnit_of_natDegree_pos _ hleftDegree) hleft
  · exact (Polynomial.not_isUnit_of_natDegree_pos _ hrightDegree) hright

/-! Check every possible positive square divisor up to the square root. -/
def discriminantQuotientSafe
    (threshold discriminant : ℕ) : Bool :=
  (List.range (Nat.sqrt discriminant + 1)).all fun index =>
    decide (0 < index → index ^ 2 ∣ discriminant →
      threshold ≤ discriminant / index ^ 2)

theorem lower_bound_of_discriminantQuotientSafe
    {threshold discriminant index : ℕ} {fieldDiscriminant : ℤ}
    (hdiscriminant : 0 < discriminant)
    (hcheck :
      discriminantQuotientSafe threshold discriminant = true)
    (hindex : 0 < index)
    (hrelation :
      (discriminant : ℤ) =
        (index : ℤ) ^ 2 * fieldDiscriminant) :
    threshold ≤ fieldDiscriminant.natAbs := by
  have hfield : fieldDiscriminant ≠ 0 := by
    intro hzero
    subst fieldDiscriminant
    norm_num at hrelation
    omega
  have habs :
      discriminant = index ^ 2 * fieldDiscriminant.natAbs := by
    have := congrArg Int.natAbs hrelation
    rw [Int.natAbs_mul, Int.natAbs_pow] at this
    simpa using this
  have hfieldAbs : 0 < fieldDiscriminant.natAbs :=
    Int.natAbs_pos.mpr hfield
  have hsquare : index ^ 2 ≤ discriminant := by
    rw [habs]
    exact Nat.le_mul_of_pos_right (index ^ 2) hfieldAbs
  have hroot : index ≤ Nat.sqrt discriminant :=
    Nat.le_sqrt'.2 hsquare
  have hmem : index ∈ List.range (Nat.sqrt discriminant + 1) :=
    List.mem_range.mpr (Nat.lt_succ_of_le hroot)
  have hall := (List.all_eq_true.mp hcheck) index hmem
  have hsafe :
      threshold ≤ discriminant / index ^ 2 :=
    (of_decide_eq_true hall) hindex ⟨fieldDiscriminant.natAbs, habs⟩
  rw [habs, Nat.mul_comm (index ^ 2),
    Nat.mul_div_left _ (pow_pos hindex 2)] at hsafe
  exact hsafe

end TraceEuclidean
