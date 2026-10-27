import NormEuclidean.CompletedPadicValuation
import NormEuclidean.LocalTraceAnnihilator
import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Uniqueness

/-!
# The original completed integer ring is the actual integral closure of Z_p

The original valuation is proved to extend the actual p-adic valuation.
Finite separability and the complete-DVF uniqueness theorem identify its
original integer ring with the integral closure. Transport of the base
valuation ring along the actual Z_p equivalence supplies the desired
Z_p algebra and integral-closure instance, rather than an assumed certificate.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.CompletedPadicIntegers

open IsDedekindDomain Bong.NumberFieldCompletion CompletedPadicBase
open LocalFieldTheory.DiscreteValuationField.Examples
open ValuationTheory.DiscreteValuationField
open scoped NumberField WithZero

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] padicAlgebra CompletedPadicBase.finiteDimensional
  CompletedPadicValuation.hasExtension

/-- The Z_p coefficients act on the original completion through the actual Q_p embedding. -/
@[implicit_reducible]
def fieldAlgebra (v : HeightOneSpectrum (𝓞 F)) :
    Algebra ℤ_[rationalPrime v] (v.adicCompletion F) :=
  ((algebraMap ℚ_[rationalPrime v] (v.adicCompletion F)).comp
    (algebraMap ℤ_[rationalPrime v] ℚ_[rationalPrime v])).toAlgebra

attribute [local instance] fieldAlgebra

/-- The actual coefficient map lands in the original completed integer ring. -/
def integerMap (v : HeightOneSpectrum (𝓞 F)) :
    ℤ_[rationalPrime v] →+* integerRing v :=
  (algebraMap ℤ_[rationalPrime v] (v.adicCompletion F)).codRestrict (integerRing v) (by
    intro z
    apply (CompletedPadicValuation.integral_iff v _).mpr
    exact (LocalTraceAnnihilator.integral_range (rationalPrime v) _).mp ⟨z, rfl⟩)

/-- The actual original integer ring receives its Z_p algebra from this coefficient map. -/
@[implicit_reducible]
def integerAlgebra (v : HeightOneSpectrum (𝓞 F)) :
    Algebra ℤ_[rationalPrime v] (integerRing v) := (integerMap v).toAlgebra

attribute [local instance] integerAlgebra

/-- The original integer-ring inclusion preserves the actual p-adic coefficients. -/
theorem integerMap_coe (v : HeightOneSpectrum (𝓞 F)) (z : ℤ_[rationalPrime v]) :
    (integerMap v z : v.adicCompletion F) =
      algebraMap ℚ_[rationalPrime v] (v.adicCompletion F)
        (algebraMap ℤ_[rationalPrime v] ℚ_[rationalPrime v] z) := rfl

theorem fieldTower (v : HeightOneSpectrum (𝓞 F)) :
    IsScalarTower ℤ_[rationalPrime v] ℚ_[rationalPrime v] (v.adicCompletion F) :=
  IsScalarTower.of_algebraMap_eq' rfl

theorem integerTower (v : HeightOneSpectrum (𝓞 F)) :
    IsScalarTower ℤ_[rationalPrime v] (integerRing v) (v.adicCompletion F) :=
  IsScalarTower.of_algebraMap_eq' rfl

attribute [local instance] fieldTower integerTower

/-- The actual original integer ring is the integral closure of Z_p in the original completion. -/
theorem integralClosure (v : HeightOneSpectrum (𝓞 F)) :
    IsIntegralClosure (integerRing v) ℤ_[rationalPrime v] (v.adicCompletion F) := by
  let base := Qp.padicCompleteDVF (rationalPrime v)
  let target := (localField v).toCompleteDVF
  let V := base.valuationSubring
  letI : base.valuation.HasExtension target.valuation := CompletedPadicValuation.hasExtension v
  letI : Algebra V (integerRing v) := by
    change Algebra base.valuation.integer target.valuation.integer
    infer_instance
  letI : IsScalarTower V (integerRing v) (v.adicCompletion F) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hC := ValuedExtension.target_valuationSubring_isIntegralClosure_of_finite_separable
    (L := v.adicCompletion F) base target
  letI : IsIntegralClosure (integerRing v) V (v.adicCompletion F) := hC
  let e : ℤ_[rationalPrime v] ≃+* V := Qp.padicIntEquivValuationSubring (rationalPrime v)
  have he : (algebraMap V (v.adicCompletion F)).comp e.toRingHom =
      algebraMap ℤ_[rationalPrime v] (v.adicCompletion F) := by
    apply RingHom.ext
    intro z
    change algebraMap ℚ_[rationalPrime v] (v.adicCompletion F) ((e z : V) :
      ℚ_[rationalPrime v]) = _
    have hc : ((e z : V) : ℚ_[rationalPrime v]) = (z : ℚ_[rationalPrime v]) :=
      Qp.padicIntEquivValuationSubring_coe (rationalPrime v) z
    rw [hc]
    rfl
  refine { algebraMap_injective := Subtype.val_injective, isIntegral_iff := ?_ }
  intro x
  rw [e.isIntegral_iff he x]
  exact IsIntegralClosure.isIntegral_iff (A := integerRing v) (R := V) (B := v.adicCompletion F)

attribute [local instance] integralClosure

/-- Module finiteness of the original completed integers over Z_p is now derived. -/
theorem integral_finite (v : HeightOneSpectrum (𝓞 F)) :
    Module.Finite ℤ_[rationalPrime v] (integerRing v) :=
  IsIntegralClosure.finite ℤ_[rationalPrime v] ℚ_[rationalPrime v]
    (v.adicCompletion F) (integerRing v)

/-- Integrality over the actual Z_p coefficient algebra is original completed integrality. -/
theorem isIntegral_iff_mem (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    IsIntegral ℤ_[rationalPrime v] x ↔
      x ∈ (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).valuationSubring := by
  rw [IsIntegralClosure.isIntegral_iff (A := integerRing v)]
  exact ⟨fun ⟨z, hz⟩ ↦ hz ▸ z.property, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩

end NormEuclidean.CompletedPadicIntegers
