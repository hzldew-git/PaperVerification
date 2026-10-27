import NormEuclidean.ChapterX.AdicAutomorphism
import NormEuclidean.ChapterX.CompletedExtensionProduct

/-!
# Automorphism transport within actual finite completion fibers

A field automorphism fixing the base field pulls a prime above `p` back
to another prime above `p`. Its completed map commutes with the embeddings
from the base completion, by continuity and density of the base field.
-/

noncomputable section

namespace NormEuclidean.CompletedFiberAutomorphism

open IsDedekindDomain ExtensionIdeleNorm
open scoped NumberField

universe u
variable {K E : Type u} [Field K] [NumberField K]
  [Field E] [NumberField E] [Algebra K E]

/-- Pulling back by an automorphism over `K` leaves the underlying base prime fixed. -/
theorem prime_under_eq (e : E ≃ₐ[K] E) (w : HeightOneSpectrum (𝓞 E)) :
    (AdicAutomorphism.prime e.toRingEquiv w).under (𝓞 K) = w.under (𝓞 K) := by
  apply HeightOneSpectrum.ext_iff.mpr
  apply Ideal.ext
  intro a
  change NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv
    (algebraMap (𝓞 K) (𝓞 E) a) ∈ w.asIdeal ↔ algebraMap (𝓞 K) (𝓞 E) a ∈ w.asIdeal
  have hc : NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv
      (algebraMap (𝓞 K) (𝓞 E) a) = algebraMap (𝓞 K) (𝓞 E) a := by
    apply NumberField.RingOfIntegers.ext
    change e (algebraMap K E (a : K)) = algebraMap K E (a : K)
    exact e.commutes (a : K)
  rw [hc]

/-- The actual prime above `p` pulled back by the automorphism. -/
@[reducible] def prime (e : E ≃ₐ[K] E) (p : HeightOneSpectrum (𝓞 K))
    (w : FinitePlacesAbove (E := E) p) : FinitePlacesAbove (E := E) p :=
  ⟨AdicAutomorphism.prime e.toRingEquiv w.1, (prime_under_eq e w.1).trans w.2⟩

/-- Transport of completion factors respects every base-completed scalar. -/
theorem completionMap_base (e : E ≃ₐ[K] E) (p : HeightOneSpectrum (𝓞 K))
    (w : FinitePlacesAbove (E := E) p) (a : p.adicCompletion K) :
    AdicAutomorphism.completionMap e.toRingEquiv w.1
      (finitePlaceAboveCompletionMap p (prime e p w) a) =
        finitePlaceAboveCompletionMap p w a := by
  have h := (HeightOneSpectrum.denseRange_algebraMap (K := K) p).equalizer
    ((AdicAutomorphism.completionMap_continuous e.toRingEquiv w.1).comp
      (finitePlaceAboveCompletionMap_continuous p (prime e p w)))
    (finitePlaceAboveCompletionMap_continuous p w) (by
      funext x
      change AdicAutomorphism.completionMap e.toRingEquiv w.1
        (finitePlaceAboveCompletionMap p (prime e p w) (x : p.adicCompletion K)) =
          finitePlaceAboveCompletionMap p w (x : p.adicCompletion K)
      rw [finitePlaceAboveCompletionMap_global, finitePlaceAboveCompletionMap_global]
      exact (AdicAutomorphism.completionMap_global e.toRingEquiv w.1
        (algebraMap K E x)).trans (congrArg (algebraMap E (w.1.adicCompletion E))
          (e.commutes x)))
  exact congrFun h a

end NormEuclidean.CompletedFiberAutomorphism
