import NormEuclidean.InfiniteAdelicTrace
import NormEuclidean.GlobalFiniteTraceCharacter
import NormEuclidean.FiniteAdelicCharacterTopology
import NormEuclidean.TraceCharacterProducts
import Mathlib.NumberTheory.NumberField.AdeleRing

/-!
# The actual global adelic trace character and the diagonal product formula

The infinite trace uses a negative sign, opposite to the constructed
positive local p-primary phases. The resulting continuous character
on the actual adele ring is trivial on every principal global adele.
Both its finite factorization and archimedean contribution are literal.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.AdelicTraceCharacter

open NumberField IsDedekindDomain
open scoped NumberField Classical

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] CompletedPadicBase.padicAlgebra

/-- The standard real-circle exponential phase as an actual additive character. -/
def realPhase : AddChar (AddCircle (1 : ℝ)) ℂ where
  toFun x := (AddCircle.toCircle x : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by simp only [AddCircle.toCircle_add, Circle.coe_mul]

theorem realPhase_continuous : Continuous realPhase :=
  continuous_subtype_val.comp AddCircle.continuous_toCircle

/-- The actual circle-valued global character, with compatible finite and infinite signs. -/
def circleCharacter : AdeleRing (𝓞 F) F →+ AddCircle (1 : ℝ) where
  toFun a := -(InfiniteAdelicTrace.trace a.1 : AddCircle (1 : ℝ)) +
    ComplexTraceCharacter.realClass (FiniteAdelicCharacter.character a.2)
  map_zero' := by simp
  map_add' a b := by
    change -(InfiniteAdelicTrace.trace (a.1 + b.1) : AddCircle (1 : ℝ)) +
      ComplexTraceCharacter.realClass (FiniteAdelicCharacter.character (a.2 + b.2)) = _
    simp only [map_add, AddCircle.coe_add]
    abel

/-- The circle-valued character is continuous for the actual adelic product topology. -/
theorem circleCharacter_continuous : Continuous (circleCharacter (F := F)) := by
  have hi : Continuous (fun a : AdeleRing (𝓞 F) F ↦
      (InfiniteAdelicTrace.trace a.1 : AddCircle (1 : ℝ))) :=
    (AddCircle.continuous_mk' (1 : ℝ)).comp
      (InfiniteAdelicTrace.trace_continuous.comp continuous_fst)
  have hf : Continuous (fun a : AdeleRing (𝓞 F) F ↦
      ComplexTraceCharacter.realClass (FiniteAdelicCharacter.character a.2)) :=
    ((FiniteAdelicCharacterTopology.locallyConstant.comp
      ComplexTraceCharacter.realClass).continuous).comp continuous_snd
  exact hi.neg.add hf

/-- The finite and infinite trace classes cancel on every diagonal global element. -/
theorem circle_diagonal (x : F) :
    circleCharacter (algebraMap F (AdeleRing (𝓞 F) F) x) = 0 := by
  change -(InfiniteAdelicTrace.trace (algebraMap F (InfiniteAdeleRing F) x) :
    AddCircle (1 : ℝ)) + ComplexTraceCharacter.realClass
      (FiniteAdelicCharacter.character (algebraMap F (FiniteAdeleRing (𝓞 F) F) x)) = 0
  rw [InfiniteAdelicTrace.diagonal, GlobalFiniteTraceCharacter.diagonal,
    ComplexTraceCharacter.realClass_rat, neg_add_cancel]

/-- The genuine unit-modulus global adelic trace character. -/
def character : AddChar (AdeleRing (𝓞 F) F) ℂ :=
  realPhase.compAddMonoidHom circleCharacter

theorem character_continuous : Continuous (character (F := F)) :=
  realPhase_continuous.comp circleCharacter_continuous

theorem character_norm (a : AdeleRing (𝓞 F) F) : ‖character a‖ = 1 := Circle.norm_coe _

/-- The negative archimedean factor on the actual infinite adele ring. -/
def infiniteCharacter : AddChar (InfiniteAdeleRing F) ℂ where
  toFun a := realPhase (-(InfiniteAdelicTrace.trace a : AddCircle (1 : ℝ)))
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    simp only [map_add, AddCircle.coe_add, neg_add, realPhase.map_add_eq_mul]

/-- The actual global character factors into its archimedean and all actual finite local factors. -/
theorem factorization (a : AdeleRing (𝓞 F) F) :
    character a = infiniteCharacter a.1 *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        ComplexTraceCharacter.trace (CompletedPadicBase.rationalPrime v)
          (v.adicCompletion F) (a.2 v) := by
  change realPhase (-(InfiniteAdelicTrace.trace a.1 : AddCircle (1 : ℝ)) +
    ComplexTraceCharacter.realClass (FiniteAdelicCharacter.character a.2)) = _
  rw [realPhase.map_add_eq_mul]
  exact congrArg (fun z ↦ infiniteCharacter a.1 * z)
    (TraceCharacterProducts.finite_product a.2)

/-- The complete global character product is one on every principal global adele. -/
theorem diagonal (x : F) : character (algebraMap F (AdeleRing (𝓞 F) F) x) = 1 := by
  change realPhase (circleCharacter (algebraMap F (AdeleRing (𝓞 F) F) x)) = 1
  rw [circle_diagonal, realPhase.map_zero_eq_one]

/-- Explicit local-product form of the diagonal global trace-character formula. -/
theorem diagonal_product (x : F) :
    infiniteCharacter (algebraMap F (InfiniteAdeleRing F) x) *
      (∏ᶠ v : HeightOneSpectrum (𝓞 F),
        ComplexTraceCharacter.trace (CompletedPadicBase.rationalPrime v)
          (v.adicCompletion F) (algebraMap F (v.adicCompletion F) x)) = 1 := by
  exact (factorization (algebraMap F (AdeleRing (𝓞 F) F) x)).symm.trans (diagonal x)

end NormEuclidean.AdelicTraceCharacter
