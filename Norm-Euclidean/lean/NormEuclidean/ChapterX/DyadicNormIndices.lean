import NormEuclidean.ChapterX.LocalNormIndices
import NormEuclidean.Reuse.Bong.Dyadic.HilbertSymbolProof
import Bong.Dyadic.NumberFieldCompletion

/-!
# Quadratic norm indices at actual dyadic places

The local Hilbert-symbol proofs are instantiated with the concrete dyadic
context of a number-field completion. No Hilbert-symbol law or local
norm-index assertion is supplied as an arithmetic premise.
-/

noncomputable section

namespace NormEuclidean.DyadicNormIndices

open IsDedekindDomain Bong.Dyadic QuadraticExtensionNorm ExtensionIdeleNorm
open scoped NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- Every nonsquare parameter at a dyadic completion has norm index two.
The two-coset argument uses proved nondegeneracy and multiplication of nonnorms. -/
theorem quadraticNormGroup_index_two (p : HeightOneSpectrum (𝓞 K))
    (hp : (2 : 𝓞 K) ∈ p.asIdeal) (theta : (p.adicCompletion K)ˣ)
    (hnonsquare : ¬ IsSquare theta) :
    (quadraticNormGroup (p.adicCompletion K) theta).index = 2 := by
  letI : Bong.DyadicContext (p.adicCompletion K) := Bong.NumberFieldCompletion.dyadicContext p hp
  obtain ⟨a, ha⟩ := exists_hilbertSymbol_eq_neg_one_of_not_isSquare_proved theta hnonsquare
  have hnot : ¬ IsQuadraticNorm (p.adicCompletion K) theta a :=
    (hilbertSymbol_eq_neg_one_iff _ theta a).mp ha
  apply Subgroup.index_eq_two_iff_exists_notMem_and.mpr
  refine ⟨a, hnot, ?_⟩
  intro b
  by_cases hb : IsQuadraticNorm (p.adicCompletion K) theta b
  · exact Or.inr hb
  · exact Or.inl (isQuadraticNorm_mul_of_not_isQuadraticNorm theta b a hb hnot)

/-- The full one-or-two formula for every dyadic quadratic norm group,
with the split case included. -/
theorem quadraticNormGroup_index (p : HeightOneSpectrum (𝓞 K))
    (hp : (2 : 𝓞 K) ∈ p.asIdeal) (theta : (p.adicCompletion K)ˣ) :
    (quadraticNormGroup (p.adicCompletion K) theta).index =
      (by
        classical
        exact if IsSquare theta then 1 else 2) := by
  classical
  split_ifs with hs
  · exact LocalNormIndices.quadraticNormGroup_index_one theta hs
  · exact quadraticNormGroup_index_two p hp theta hs

universe u
variable {F : Type u} [Field F] [NumberField F]

/-- The actual extension-completion fiber has the computed dyadic index. -/
theorem finite_dyadic_index (theta : Fˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 F)) (hp : (2 : 𝓞 F) ∈ p.asIdeal) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    (finitePlaceFiberNormUnits (E := QuadraticAlgebra F theta.val 0) p).range.index =
      (by
        classical
        exact if IsSquare (Units.map (algebraMap F (p.adicCompletion F)).toMonoidHom theta)
          then 1 else 2) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  have heq : (finitePlaceFiberNormUnits (E := QuadraticAlgebra F theta.val 0) p).range =
      quadraticNormGroup (p.adicCompletion F)
        (Units.map (algebraMap F (p.adicCompletion F)).toMonoidHom theta) := by
    ext a
    exact CompletedNormImages.finite_norm_range_iff theta htheta p a
  rw [heq]
  exact quadraticNormGroup_index p hp _

end NormEuclidean.DyadicNormIndices
