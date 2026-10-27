import NormEuclidean.BinaryFieldArithmetic

/-!
# Completed splitting forces prime ideals to be principal

An actual one-prime idele is a local binary norm wherever the
discriminant is a square at that prime. Norm principality then makes the
prime ideal principal. This supplies the split-prime input of the
Hilbert class-field comparison; the class-field identification is separate.
-/

noncomputable section

namespace NormEuclidean.BinarySplittingPrimes

open IsDedekindDomain CompletedIntegralLattice
open scoped NumberField nonZeroDivisors

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {theta : Kˣ}

/-- Every prime at which the binary discriminant splits has a principal ideal. -/
theorem prime_isPrincipal_of_local_square (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (f : BinaryNormForm.Frame Q theta)
    (p : HeightOneSpectrum (integerSubring K))
    (hsquare : IsSquare
      (Units.map (algebraMap K (LocalField (integerSubring K) p)).toMonoidHom theta)) :
    p.asIdeal.IsPrincipal := by
  classical
  let a := FiniteIdele.ideleOfDivisor (K := K) (Finsupp.single p (1 : ℤ))
  have hn : ∀ q : HeightOneSpectrum (integerSubring K),
      Bong.Dyadic.IsQuadraticNorm (LocalField (integerSubring K) q)
        (Units.map (algebraMap K (LocalField (integerSubring K) q)).toMonoidHom theta)
        (FiniteIdele.componentUnit q a) := by
    intro q
    by_cases hq : q = p
    · subst q
      letI : CharZero (LocalField (integerSubring K) p) := Algebra.charZero_of_charZero K _
      exact Bong.Dyadic.isQuadraticNorm_of_isSquare_left _ hsquare
    · simp only [a, FiniteIdele.componentUnit_ideleOfDivisor,
        Finsupp.single_eq_of_ne hq, zpow_zero]
      exact Bong.Dyadic.isQuadraticNorm_one _ _
  have hc := NormIdelePrincipality.classHom_eq_one L hA hE (by omega) f a hn
  have hprincipal := (FiniteIdele.classHom_eq_one_iff_principal a).mp hc
  have hf : FiniteIdele.fractionalIdeal a =
      (p.asIdeal : FractionalIdeal (integerSubring K)⁰ K) := by
    simp [a, FiniteIdele.fractionalIdeal]
  rw [hf] at hprincipal
  exact (IsFractionRing.coeSubmodule_isPrincipal
    (R := integerSubring K) (K := K) (I := p.asIdeal)).mp hprincipal

end NormEuclidean.BinarySplittingPrimes
