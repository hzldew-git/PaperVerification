import NormEuclidean.FiniteAdelicCharacter

/-! Genuine products of the constructed local complex trace characters. -/

noncomputable section

namespace NormEuclidean.TraceCharacterProducts

open NumberField IsDedekindDomain Bong.NumberFieldCompletion
open scoped NumberField Classical

/-- The faithful rational phase sends finitely supported sums to actual finite products. -/
theorem phase_finsum {I : Type*} (f : I → RationalPrimaryCharacter.Circle)
    (hf : Function.HasFiniteSupport f) :
    ComplexTraceCharacter.phase (∑ᶠ i, f i) = ∏ᶠ i, ComplexTraceCharacter.phase (f i) := by
  have hs : Function.mulSupport (fun i ↦ ComplexTraceCharacter.phase (f i)) ⊆
      (hf.toFinset : Set I) := by
    intro i hi
    apply hf.mem_toFinset.mpr
    intro hz
    apply hi
    change ComplexTraceCharacter.phase (f i) = 1
    rw [hz, ComplexTraceCharacter.phase.map_zero_eq_one]
  rw [finsum_eq_sum_of_support_subset f hf.coe_toFinset.ge,
    finprod_eq_prod_of_mulSupport_subset _ hs]
  change ComplexTraceCharacter.phase.toMonoidHom (Multiplicative.ofAdd (∑ i ∈ hf.toFinset, f i))
    = _
  rw [ofAdd_sum, map_prod]
  rfl

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] CompletedPadicBase.padicAlgebra

/-- Every actual finite adele has only finitely many nontrivial local complex trace factors. -/
theorem complex_finite_support (a : FiniteAdeleRing (𝓞 F) F) :
    Function.HasFiniteMulSupport (fun v : HeightOneSpectrum (𝓞 F) ↦
      ComplexTraceCharacter.trace (CompletedPadicBase.rationalPrime v)
        (v.adicCompletion F) (a v)) := by
  refine (FiniteAdelicCharacter.finite_support a).subset fun v hv hz ↦ hv ?_
  change FiniteAdelicCharacter.localCharacter v (a v) = 0 at hz
  change ComplexTraceCharacter.phase (FiniteAdelicCharacter.localCharacter v (a v)) = 1
  rw [hz, ComplexTraceCharacter.phase.map_zero_eq_one]

/-- The complex finite adelic trace character is the product of the actual local characters. -/
theorem finite_product (a : FiniteAdeleRing (𝓞 F) F) :
    ComplexTraceCharacter.phase (FiniteAdelicCharacter.character a) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        ComplexTraceCharacter.trace (CompletedPadicBase.rationalPrime v)
          (v.adicCompletion F) (a v) :=
  phase_finsum _ (FiniteAdelicCharacter.finite_support a)

end NormEuclidean.TraceCharacterProducts
