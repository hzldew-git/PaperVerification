import NormEuclidean.FiniteAdelicCharacter
import NormEuclidean.FiniteSupportFiberSum
import NormEuclidean.RationalCharacterRecombination
import NormEuclidean.CompletedTraceDecomposition

/-!
# The finite adelic character on the diagonal number field

Actual finite places are regrouped over rational primes by a proved
equivalence. Finite support justifies the regrouping. The fixed-prime
trace comparison and rational primary recombination then identify the
character of every principal finite adele with its global trace class.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.GlobalFiniteTraceCharacter

open NumberField IsDedekindDomain Bong.NumberFieldCompletion
open CompletedTensorProduct FiniteAdelicCharacter
open scoped NumberField Classical NormEuclidean.CompletedTensorProduct

variable (F : Type*) [Field F] [NumberField F]

attribute [local instance] CompletedPadicBase.padicAlgebra

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- The genuine finite places, regrouped over their rational prime below. -/
def placeEquiv : (Σ q : HeightOneSpectrum (𝓞 ℚ), Place F q) ≃ HeightOneSpectrum (𝓞 F) :=
  (Equiv.sigmaCongrRight fun q ↦ finitePlaceExtensionEquivAbove (K := ℚ) (L := F) q).trans
    (Equiv.sigmaFiberEquiv (finitePlaceBelow (K := ℚ)))

theorem placeEquiv_apply (q : HeightOneSpectrum (𝓞 ℚ)) (w : Place F q) :
    placeEquiv F ⟨q, w⟩ = prime F q w := rfl

/-- The actual finite adelic trace character of a principal adele is its global trace class. -/
theorem diagonal (x : F) :
    FiniteAdelicCharacter.character (algebraMap F (FiniteAdeleRing (𝓞 F) F) x) =
      (Algebra.trace ℚ F x : RationalPrimaryCharacter.Circle) := by
  let f : HeightOneSpectrum (𝓞 F) → RationalPrimaryCharacter.Circle :=
    fun v ↦ localCharacter v (algebraMap F (v.adicCompletion F) x)
  have hf : Function.HasFiniteSupport f :=
    FiniteAdelicCharacter.finite_support (algebraMap F (FiniteAdeleRing (𝓞 F) F) x)
  calc
    _ = ∑ᶠ v : HeightOneSpectrum (𝓞 F), f v := rfl
    _ = ∑ᶠ z : (Σ q : HeightOneSpectrum (𝓞 ℚ), Place F q), f (placeEquiv F z) :=
      (finsum_comp_equiv (placeEquiv F) (f := f)).symm
    _ = ∑ᶠ q : HeightOneSpectrum (𝓞 ℚ), ∑ w : Place F q, f (prime F q w) :=
      FiniteSupportFiberSum.sigma_sum (fun z ↦ f (placeEquiv F z))
        (hf.comp_of_injective (placeEquiv F).injective)
    _ = ∑ᶠ q : HeightOneSpectrum (𝓞 ℚ),
        RationalPrimaryCharacter.character (CompletedRationalPrime.prime q)
          (Algebra.trace ℚ F x) := by
      congr 1
      funext q
      exact (CompletedTraceDecomposition.trace_character_sum F q x).symm
    _ = ∑ᶠ p : Nat.Primes,
        RationalPrimaryCharacter.character (p : ℕ) (Algebra.trace ℚ F x) :=
      finsum_comp_equiv Rat.HeightOneSpectrum.primesEquiv
        (f := fun p : Nat.Primes ↦ RationalPrimaryCharacter.character (p : ℕ)
          (Algebra.trace ℚ F x))
    _ = _ := RationalCharacterRecombination.character_sum _

end NormEuclidean.GlobalFiniteTraceCharacter
