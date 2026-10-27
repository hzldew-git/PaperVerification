import NormEuclidean.IntegralDiagonalFrame
import NormEuclidean.DiagonalResidue
import NormEuclidean.InverseClassPrimes
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient

/-!
# Good reduction in rank at least three

An integral diagonal frame and a common denominator reduce the residue-vector
construction to the proved odd finite-field isotropy theorem. No freeness of
the integral lattice, residue-vector oracle, or source-ring inverse of two
is assumed. The remaining prime-existence input is isolated in
`HasInverseClassPrimesAway` and is not asserted to hold in this file.
-/

namespace NormEuclidean

open scoped nonZeroDivisors NumberField

variable {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V}

/-- A single nonzero denominator controls good reduction of a nonfree
integral lattice. Outside two and this denominator, every nonzero prime
has an actual nonzero isotropic residue representative in rank at least three. -/
theorem exists_good_reduction_denominator (L : Lattice (integerSubring K) Q)
    (hdim : 3 ≤ Module.finrank K V) :
    ∃ t : integerSubring K, t ≠ 0 ∧
      ∀ p : Ideal (integerSubring K), p.IsMaximal → p ≠ ⊥ →
        (2 : integerSubring K) ∉ p → t ∉ p →
        ∃ w ∈ L.carrier,
          w ∉ ((p : FractionalIdeal (integerSubring K)⁰ K) :
            Submodule (integerSubring K) K) • L.carrier ∧
          Q w ∈ (p : FractionalIdeal (integerSubring K)⁰ K) := by
  letI : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
  let D := L.integralDiagonalFrame
  refine ⟨D.denominator, D.denominator_ne_zero, ?_⟩
  intro p hp hp0 htwo ht
  letI : p.IsMaximal := hp
  letI : Module.Free ℤ (integerSubring K) :=
    inferInstanceAs (Module.Free ℤ (𝓞 K))
  letI : Module.Finite ℤ (integerSubring K) :=
    inferInstanceAs (Module.Finite ℤ (𝓞 K))
  letI : Finite ((integerSubring K) ⧸ p) := p.finiteQuotientOfFreeOfNeBot hp0
  exact exists_nondivisible_isotropic_mod_prime_of_diagonal_frame
    Q L.carrier D.basis D.basis_mem D.coeff D.diagonal D.denominator
    D.denominator_mem p htwo ht (by simpa only [Fintype.card_fin] using hdim)

/-- The residue-vector part of the class-number interface is now proved.
The sole remaining input in this rank range is field-theoretic inverse-class
prime existence with avoidance, stated independently of the lattice. -/
theorem hasGoodPrimeData_of_inverse_class_primes
    (L : Lattice (integerSubring K) Q) (hdim : 3 ≤ Module.finrank K V)
    (hprime : HasInverseClassPrimesAway K) : HasGoodPrimeData L := by
  obtain ⟨t, ht, hresidue⟩ := exists_good_reduction_denominator L hdim
  intro i hi
  obtain ⟨p, hp, hp0, hcop, htwo, htp, a, ha, hgen⟩ :=
    inverse_class_prime_avoiding_two_and_denominator K hprime i hi t ht
  obtain ⟨w, hw, hwp, hQw⟩ := hresidue p hp hp0 htwo htp
  exact ⟨p, hp, hp0, hcop, a, ha, hgen, w, hw, hwp, hQw⟩

/-- Theorem 1.2 (reference manuscript)'s field-class-number and freeness conclusions in rank at
least three, conditional only on the explicit field-theoretic prime-existence
input. This is not an unconditional proof of that external input or of the
lattice genus-class-number assertion. -/
theorem classNumber_and_freeness_of_inverse_class_primes
    (L : Lattice (integerSubring K) Q) (hdim : 3 ≤ Module.finrank K V)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hprime : HasInverseClassPrimesAway K) :
    IsPrincipalIdealRing (integerSubring K) ∧ NumberField.classNumber K = 1 ∧
      Module.Free (integerSubring K) L.carrier :=
  classNumber_and_freeness_of_good_prime_data L hA hE
    (hasGoodPrimeData_of_inverse_class_primes L hdim hprime)

end NormEuclidean
