import TraceEuclidean.DegreeSevenFrontierArithmetic

/-!
# Discriminant certificates for the retained degree-seven frontier

The square part of each polynomial discriminant is separated from a
squarefree kernel.  The exact power-order index relation then forces the
field discriminant to be at least that kernel.  This avoids both a maximal
order computation and exhaustive enumeration of every possible index.
-/

namespace TraceEuclidean

open Polynomial

noncomputable section

/-- If `index ^ 2` divides `squarePart ^ 2 * kernel` and `kernel` is
squarefree, then the index already divides `squarePart`. -/
theorem index_dvd_squarePart_of_squarefree_kernel
    {index squarePart kernel : ℕ}
    (hindex : 0 < index) (hsquarePart : 0 < squarePart)
    (hkernel : 0 < kernel) (hkernelSquarefree : Squarefree kernel)
    (hdiv : index ^ 2 ∣ squarePart ^ 2 * kernel) :
    index ∣ squarePart := by
  apply (Nat.factorization_le_iff_dvd hindex.ne' hsquarePart.ne').mp
  intro prime
  have hfactorization :=
    (Nat.factorization_le_iff_dvd (pow_ne_zero 2 hindex.ne')
      (mul_ne_zero (pow_ne_zero 2 hsquarePart.ne') hkernel.ne')).mpr hdiv
  have hpoint := hfactorization prime
  rw [Nat.factorization_pow,
    Nat.factorization_mul (pow_ne_zero 2 hsquarePart.ne') hkernel.ne',
    Nat.factorization_pow] at hpoint
  have hkernelPoint := hkernelSquarefree.natFactorization_le_one prime
  change 2 * index.factorization prime ≤
    2 * squarePart.factorization prime + kernel.factorization prime at hpoint
  omega

/-- In an exact discriminant relation with squarefree residual kernel, the
absolute field discriminant is at least that kernel. -/
theorem fieldDiscriminant_lowerBound_of_squarePart
    {squarePart kernel index : ℕ} {fieldDiscriminant : ℤ}
    (hsquarePart : 0 < squarePart) (hkernel : 0 < kernel)
    (hkernelSquarefree : Squarefree kernel) (hindex : 0 < index)
    (hrelation :
      ((squarePart ^ 2 * kernel : ℕ) : ℤ) =
        (index : ℤ) ^ 2 * fieldDiscriminant) :
    kernel ≤ fieldDiscriminant.natAbs := by
  have habs : squarePart ^ 2 * kernel =
      index ^ 2 * fieldDiscriminant.natAbs := by
    change (squarePart : ℤ) ^ 2 * (kernel : ℤ) =
      (index : ℤ) ^ 2 * fieldDiscriminant at hrelation
    have := congrArg Int.natAbs hrelation
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast,
      Int.natAbs_natCast, Int.natAbs_mul, Int.natAbs_pow,
      Int.natAbs_natCast] at this
    simpa using this
  have hdiv : index ^ 2 ∣ squarePart ^ 2 * kernel :=
    ⟨fieldDiscriminant.natAbs, habs⟩
  obtain ⟨multiple, rfl⟩ := index_dvd_squarePart_of_squarefree_kernel
    hindex hsquarePart hkernel hkernelSquarefree hdiv
  have hmultiple : 0 < multiple := Nat.pos_of_mul_pos_left hsquarePart
  have hcancel : multiple ^ 2 * kernel = fieldDiscriminant.natAbs := by
    exact Nat.mul_left_cancel (pow_pos hindex 2)
      (by simpa [mul_pow, mul_assoc] using habs)
  rw [← hcancel]
  exact Nat.le_mul_of_pos_left kernel (pow_pos hmultiple 2)

/-- Proof-bearing data for one retained septic. -/
structure DegreeSevenSurvivorDiscriminantCertificate where
  coefficients : List ℤ
  discriminant : ℕ
  squarePart : ℕ
  kernel : ℕ
  squarePartPositive : 0 < squarePart
  kernelPositive : 0 < kernel
  discriminantFactorization : discriminant = squarePart ^ 2 * kernel
  kernelSquarefree : Squarefree kernel
  thresholdLowerBound : 20134393 ≤ kernel
  polynomialDiscriminant :
    (polynomialOfCoefficients coefficients).discr = (discriminant : ℤ)

namespace DegreeSevenSurvivorDiscriminantCertificate

/-- A certificate transfers its squarefree-kernel bound through the exact
power-order index relation carried by a Hunter field candidate. -/
theorem fieldDiscriminant_lowerBound
    {K : Type*} [Field K] [NumberField K]
    {f : ℤ[X]} (hfield : HunterFieldPolynomialCandidate K 7 194 f)
    (certificate : DegreeSevenSurvivorDiscriminantCertificate)
    (hcoefficients : certificate.coefficients =
      [f.coeff 0, f.coeff 1, f.coeff 2, f.coeff 3,
        f.coeff 4, f.coeff 5, f.coeff 6, 1]) :
    20134393 ≤ (NumberField.discr K).natAbs := by
  have hf :
      f = polynomialOfCoefficients
        [f.coeff 0, f.coeff 1, f.coeff 2, f.coeff 3,
          f.coeff 4, f.coeff 5, f.coeff 6, 1] :=
    degreeSeven_eq_polynomialOfCoefficients
      hfield.1.1 hfield.1.2.2.1
  rcases hfield.2 with ⟨a, hgen, hminpoly, index, hindex, hrelation⟩
  have hpolynomial :
      polynomialOfCoefficients certificate.coefficients = f := by
    rw [hcoefficients, ← hf]
  have hcertificateRelation :
      ((certificate.squarePart ^ 2 * certificate.kernel : ℕ) : ℤ) =
        (index : ℤ) ^ 2 * NumberField.discr K := by
    rw [← certificate.discriminantFactorization,
      ← certificate.polynomialDiscriminant, hpolynomial]
    exact hrelation
  exact certificate.thresholdLowerBound.trans
    (fieldDiscriminant_lowerBound_of_squarePart
      certificate.squarePartPositive certificate.kernelPositive
      certificate.kernelSquarefree hindex hcertificateRelation)

end DegreeSevenSurvivorDiscriminantCertificate

/-- Uniform proof-bearing interface for the final discriminant filter.  Most
survivors use a squarefree-kernel certificate; exceptional power orders may
instead supply an exact maximal-order computation. -/
structure DegreeSevenFieldDiscriminantLowerBoundCertificate where
  coefficients : List ℤ
  lowerBound :
    ∀ {K : Type*} [Field K] [NumberField K]
      {f : ℤ[X]},
      HunterFieldPolynomialCandidate K 7 194 f →
      coefficients =
        [f.coeff 0, f.coeff 1, f.coeff 2, f.coeff 3,
          f.coeff 4, f.coeff 5, f.coeff 6, 1] →
      20134393 ≤ (NumberField.discr K).natAbs

namespace DegreeSevenSurvivorDiscriminantCertificate

/-- Forget the internal squarefree-kernel data after obtaining the uniform
lower-bound interface used by block-level survivor lists. -/
def toLowerBoundCertificate
    (certificate : DegreeSevenSurvivorDiscriminantCertificate) :
    DegreeSevenFieldDiscriminantLowerBoundCertificate :=
  { coefficients := certificate.coefficients
    lowerBound := fun hfield hcoefficients =>
      certificate.fieldDiscriminant_lowerBound hfield hcoefficients }

end DegreeSevenSurvivorDiscriminantCertificate

end

end TraceEuclidean
