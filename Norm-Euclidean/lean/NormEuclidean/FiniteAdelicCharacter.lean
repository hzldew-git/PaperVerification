import NormEuclidean.CompletedPadicIntegers
import NormEuclidean.ComplexTraceCharacter
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Algebra.BigOperators.Finprod

/-!
# The actual finite adelic trace character

The local characters vanish on the actual completed integer rings.
Restrictedness therefore gives finite support on every actual finite
adele, making the global sum a genuine additive homomorphism.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.FiniteAdelicCharacter

open NumberField IsDedekindDomain Bong.NumberFieldCompletion
open scoped NumberField Classical nonZeroDivisors

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] CompletedPadicBase.padicAlgebra CompletedPadicBase.finiteDimensional
  CompletedPadicIntegers.fieldAlgebra CompletedPadicIntegers.integerAlgebra
  CompletedPadicIntegers.fieldTower CompletedPadicIntegers.integerTower
  CompletedPadicIntegers.integralClosure CompletedPadicIntegers.integral_finite

local instance integralTorsionFree (v : HeightOneSpectrum (𝓞 F)) :
    Module.IsTorsionFree ℤ_[CompletedPadicBase.rationalPrime v] (integerRing v) :=
  LocalTraceAnnihilator.integralTorsionFree
    (CompletedPadicBase.rationalPrime v) (v.adicCompletion F) (integerRing v)

/-- The constructed local trace character on the original completion. -/
def localCharacter (v : HeightOneSpectrum (𝓞 F)) :
    v.adicCompletion F →+ RationalPrimaryCharacter.Circle :=
  LocalTraceAnnihilator.traceCharacter (CompletedPadicBase.rationalPrime v)
    (v.adicCompletion F)

/-- Every actual completed integer is annihilated by the local trace character. -/
theorem on_integers (v : HeightOneSpectrum (𝓞 F)) (x : integerRing v) :
    localCharacter v (x : v.adicCompletion F) = 0 := by
  have h1 : (1 : v.adicCompletion F) ∈ LocalTraceAnnihilator.codifferent
      (CompletedPadicBase.rationalPrime v) (v.adicCompletion F) (integerRing v) := by
    rw [LocalTraceAnnihilator.codifferent_eq_dual]
    exact (FractionalIdeal.one_le_dual_one ℤ_[CompletedPadicBase.rationalPrime v]
      ℚ_[CompletedPadicBase.rationalPrime v])
        ((FractionalIdeal.mem_one_iff _).mpr ⟨1, map_one _⟩)
  have h := LocalTraceAnnihilator.on_codifferent (CompletedPadicBase.rationalPrime v)
    (v.adicCompletion F) (integerRing v) 1 h1 x
  change localCharacter v (1 * (x : v.adicCompletion F)) = 0 at h
  simpa only [one_mul] using h

/-- Restrictedness gives finite support for the actual local character values. -/
theorem finite_support (a : FiniteAdeleRing (𝓞 F) F) :
    Function.HasFiniteSupport (fun v ↦ localCharacter v (a v)) := by
  have h : {v : HeightOneSpectrum (𝓞 F) | a v ∉ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.mp a.property
  refine h.subset fun v hv hi ↦ hv ?_
  exact on_integers v ⟨a v, hi⟩

/-- The actual finite adelic trace character is the finite sum of its original local values. -/
def character : FiniteAdeleRing (𝓞 F) F →+ RationalPrimaryCharacter.Circle where
  toFun a := ∑ᶠ v : HeightOneSpectrum (𝓞 F), localCharacter v (a v)
  map_zero' := by
    change (∑ᶠ v : HeightOneSpectrum (𝓞 F), localCharacter v 0) = 0
    simp
  map_add' a b := by
    change (∑ᶠ v : HeightOneSpectrum (𝓞 F), localCharacter v (a v + b v)) = _
    simp_rw [map_add]
    exact finsum_add_distrib (finite_support a) (finite_support b)

theorem character_apply (a : FiniteAdeleRing (𝓞 F) F) :
    character a = ∑ᶠ v : HeightOneSpectrum (𝓞 F), localCharacter v (a v) := rfl

/-- The full integral finite adele subgroup lies in the actual character kernel. -/
theorem integral_zero (a : FiniteAdeleRing (𝓞 F) F)
    (ha : ∀ v, a v ∈ integerRing v) : character a = 0 := by
  change (∑ᶠ v : HeightOneSpectrum (𝓞 F), localCharacter v (a v)) = 0
  simp only [fun v ↦ on_integers v ⟨a v, ha v⟩, finsum_zero]

end NormEuclidean.FiniteAdelicCharacter
