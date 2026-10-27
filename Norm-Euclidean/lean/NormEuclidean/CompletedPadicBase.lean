import Bong.Dyadic.NumberFieldCompletion
import ValuedFieldTheory.LocalField.DiscreteValuationField.MixedCharacteristicQp

/-!
# The actual p-adic base field of an original number-field completion

The local-field package uses the original completed valuation. The proved
mixed-characteristic classification supplies the actual Q_p embedding and
finite dimension. Range restriction changes neither the valuation topology
nor the original field elements; no equality of absolute-value norms is used.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.CompletedPadicBase

open IsDedekindDomain Bong.NumberFieldCompletion
open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
open scoped NumberField WithZero

variable {F : Type*} [Field F] [NumberField F]

/-- The chosen local-field package has exactly the original completed valuation. -/
def localField (v : HeightOneSpectrum (𝓞 F)) :
    LocalField (v.adicCompletion F) where
  toCompleteDVF := ValuationTheory.Valuations.completeDVFOfCompleteValuedField
    (Gamma := ℤᵐ⁰)
  residueFinite := finiteResidueField v

/-- The rational prime is the actual characteristic of the completed residue field. -/
abbrev rationalPrime (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  (localField v).residueCharacteristic

instance rationalPrime_prime (v : HeightOneSpectrum (𝓞 F)) : Fact (rationalPrime v).Prime :=
  ⟨(localField v).residueCharacteristic_prime⟩

/-- The original completion is an algebra over its actual p-adic prime field. -/
@[implicit_reducible]
def padicAlgebra (v : HeightOneSpectrum (𝓞 F)) :
    Algebra ℚ_[rationalPrime v] (v.adicCompletion F) :=
  (localField v).qpadicNumbersAlgebra

/-- Finite dimension is derived from the actual complete local-field package. -/
theorem finiteDimensional (v : HeightOneSpectrum (𝓞 F)) :
    letI := padicAlgebra v
    FiniteDimensional ℚ_[rationalPrime v] (v.adicCompletion F) :=
  (localField v).finiteDimensional_over_qpadicNumbers

/-- Range restriction is equivalent to the original completed valuation. -/
theorem range_valuation_equiv (v : HeightOneSpectrum (𝓞 F)) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict
      (localField v).toCompleteDVF).IsEquiv
        (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) := by
  apply (Valuation.isEquiv_iff_valuationSubring _ _).mpr
  ext x
  exact WithZeroValuation.mem_mrangeRestrict_valuationSubring_iff _ x

/-- The p-adic coefficient map agrees with the original rational coefficient map. -/
theorem algebraMap_rat (v : HeightOneSpectrum (𝓞 F)) (q : ℚ) :
    letI := padicAlgebra v
    algebraMap ℚ_[rationalPrime v] (v.adicCompletion F) q = (q : v.adicCompletion F) := by
  letI := padicAlgebra v
  rw [(localField v).qpadicNumbersAlgebra_algebraMap_apply,
    (localField v).qpadicNumbersEquivQpadicClosureSubfield_ratCast]
  rfl

/-- Restricting the completed valuation to its range preserves its actual uniform space. -/
theorem range_uniform_eq (v : HeightOneSpectrum (𝓞 F)) :
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued
        (localField v).toCompleteDVF).toUniformSpace =
      (inferInstance : UniformSpace (v.adicCompletion F)) := by
  let w := LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict
    (localField v).toCompleteDVF
  have hv : (inferInstance : UniformSpace (v.adicCompletion F)) =
      (Valued.mk' (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).toUniformSpace :=
    Valued.toUniformSpace_eq (v.adicCompletion F) ℤᵐ⁰
  rw [hv]
  change (Valued.mk' w).toUniformSpace =
    (Valued.mk' (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).toUniformSpace
  apply le_antisymm
  · exact le_iff_uniformContinuous_id.mpr (range_valuation_equiv v).symm.uniformContinuous
  · exact le_iff_uniformContinuous_id.mpr (range_valuation_equiv v).uniformContinuous

/-- The actual p-adic coefficient embedding is continuous for the original completion topology. -/
theorem algebraMap_continuous (v : HeightOneSpectrum (𝓞 F)) :
    letI := padicAlgebra v
    Continuous (algebraMap ℚ_[rationalPrime v] (v.adicCompletion F)) := by
  letI := padicAlgebra v
  have hu := (localField v).qpadicNumbersToQpadicClosureSubfield_isUniformInducing
  change @IsUniformInducing ℚ_[rationalPrime v] (localField v).qpadicClosureSubfield
    inferInstance (@instUniformSpaceSubtype (v.adicCompletion F) _
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued
        (localField v).toCompleteDVF).toUniformSpace) _ at hu
  rw [range_uniform_eq] at hu
  exact hu.uniformContinuous.continuous.subtype_val

/-- The original completion is a topological Q_p module, without a norm equality premise. -/
theorem continuousSMul (v : HeightOneSpectrum (𝓞 F)) :
    letI := padicAlgebra v
    ContinuousSMul ℚ_[rationalPrime v] (v.adicCompletion F) := by
  letI := padicAlgebra v
  exact continuousSMul_of_algebraMap _ _ (algebraMap_continuous v)

end NormEuclidean.CompletedPadicBase
