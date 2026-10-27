import NormEuclidean.ChapterX.LocalNormIndices
import NormEuclidean.Reuse.Bong.Bong.MaximalDefectClassProof
import NormEuclidean.Reuse.Bong.Dyadic.UnramifiedNormDirectProof
import Bong.Dyadic.NumberFieldCompletion

/-!
# Unit norm equations from local unramified square-class conditions

At odd primes even parameter order suffices. At dyadic primes the maximal
relative defect condition suffices. The dyadic discriminant and norm laws
are instantiated by their existing proofs, rather than supplied as premises.
-/

noncomputable section

namespace NormEuclidean.UnramifiedUnitNorms

open Bong Bong.Dyadic IsDedekindDomain
open scoped NumberField WithZero

section Dyadic

variable {F : Type*} [Field F] [CharZero F] [ValuativeRel F]
  [TopologicalSpace F] [DyadicContext F]

/-- Maximal relative defect parameters represent every even-order scalar as a norm. -/
theorem isNorm_of_defect_ge_twoE (theta a : Fˣ)
    (hdefect : ((2 * ramificationIndex F : ℕ) : ℕ∞) ≤ quadraticDefect F theta)
    (ha : Even (ordUnit F a)) : IsQuadraticNorm F theta a := by
  letI : DyadicDiscriminantClassLaws F := dyadicDiscriminantClassLawsProved
  letI : DyadicMaximalDefectClassLaws F := dyadicMaximalDefectClassLawsProved
  letI : DyadicUnramifiedNormLaws F := dyadicUnramifiedNormLawsProvedDirect
  rcases isSquare_or_isSquare_div_discriminant_of_defect_ge_twoE theta hdefect with hs | hs
  · exact isQuadraticNorm_of_isSquare_left F hs
  · let delta : Fˣ := DyadicDiscriminantClassLaws.discriminantUnit
    obtain ⟨s, hs⟩ := hs
    have heq : theta = delta * s ^ 2 := by
      calc
        theta = (theta / delta) * delta := by simp
        _ = (s * s) * delta := by rw [hs]
        _ = delta * s ^ 2 := by rw [pow_two]; ac_rfl
    rw [heq]
    apply (isQuadraticNorm_mul_square_left_iff F delta a s).mpr
    exact (isQuadraticNorm_discriminant_iff_even_order a).mpr ha

end Dyadic

variable {K : Type*} [Field K] [NumberField K]

/-- At an odd completed place an even-order parameter has every unit as a norm. -/
theorem odd_unit_norm (p : HeightOneSpectrum (𝓞 K))
    (htwo : (2 : 𝓞 K) ∉ p.asIdeal) (theta a : (p.adicCompletion K)ˣ)
    (htheta : Even (WithZero.log (Valued.v (theta : p.adicCompletion K))))
    (ha : Valued.v (a : p.adicCompletion K) = 1) :
    IsQuadraticNorm (p.adicCompletion K) theta a := by
  obtain ⟨pi, hpi⟩ := LocalNormIndices.exists_uniformizer p
  exact IsQuadraticNorm.symm (p.adicCompletion K)
    (LocalNormIndices.norm_of_even_valuation p htwo a ha pi hpi theta htheta)

/-- At an actual dyadic completion the maximal-defect condition gives all unit norms. -/
theorem dyadic_unit_norm (p : HeightOneSpectrum (𝓞 K))
    (hp : (2 : 𝓞 K) ∈ p.asIdeal) (theta a : (p.adicCompletion K)ˣ)
    (hdefect : letI := Bong.NumberFieldCompletion.dyadicContext p hp
      ((2 * ramificationIndex (p.adicCompletion K) : ℕ) : ℕ∞) ≤
        quadraticDefect (p.adicCompletion K) theta)
    (ha : Valued.v (a : p.adicCompletion K) = 1) :
    IsQuadraticNorm (p.adicCompletion K) theta a := by
  letI := Bong.NumberFieldCompletion.dyadicContext p hp
  have hord : ordUnit (p.adicCompletion K) a = 0 := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    change Bong.NumberFieldCompletion.adicOrder p (a : p.adicCompletion K) = 0
    simp [Bong.NumberFieldCompletion.adicOrder, Bong.NumberFieldCompletion.adicOrderValue,
      a.ne_zero, ha]
  exact isNorm_of_defect_ge_twoE theta a hdefect (by rw [hord]; exact ⟨0, by simp⟩)

end NormEuclidean.UnramifiedUnitNorms
