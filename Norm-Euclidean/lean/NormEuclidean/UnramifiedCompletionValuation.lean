import NormEuclidean.FiniteUnramifiedSquareClasses
import Bong.Dyadic.NumberFieldCompletion

/-!
# Valuations on actual unramified completion maps

The equality of normalized valuations on the base field extends to every
element of its completion by density and continuity. This supplies the
completion comparison required by the dyadic defect argument.
-/

noncomputable section

namespace NormEuclidean.UnramifiedCompletionValuation

open IsDedekindDomain ExtensionIdeleNorm
open scoped NumberField WithZero WithZeroTopology

universe u
variable {K E : Type u} [Field K] [NumberField K]
  [Field E] [NumberField E] [Algebra K E]

/-- The actual map of unramified completions preserves the normalized valuation. -/
theorem valuation_map (p : HeightOneSpectrum (𝓞 K))
    (w : FinitePlacesAbove (E := E) p)
    (hw : Algebra.IsUnramifiedAt (𝓞 K) w.1.asIdeal) (x : p.adicCompletion K) :
    Valued.v (finitePlaceAboveCompletionMap p w x) = Valued.v x := by
  letI : w.1.asIdeal.LiesOver p.asIdeal :=
    ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩
  letI := hw
  have hp : Continuous (Valued.v : p.adicCompletion K → ℤᵐ⁰) :=
    Valued.continuous_valuation_of_surjective (p.valuedAdicCompletion_surjective K)
  have hw' : Continuous (Valued.v : w.1.adicCompletion E → ℤᵐ⁰) :=
    Valued.continuous_valuation_of_surjective (w.1.valuedAdicCompletion_surjective E)
  apply congrFun ((p.denseRange_algebraMap K).equalizer
    (hw'.comp (finitePlaceAboveCompletionMap_continuous p w)) hp ?_) x
  funext a
  change Valued.v (finitePlaceAboveCompletionMap p w (algebraMap K _ a)) =
    Valued.v (algebraMap K (p.adicCompletion K) a)
  calc
    _ = Valued.v ((algebraMap K E a : E) : w.1.adicCompletion E) :=
      congrArg (Valued.v : w.1.adicCompletion E → ℤᵐ⁰)
        (finitePlaceAboveCompletionMap_global p w a)
    _ = w.1.valuation E (algebraMap K E a) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w.1 _
    _ = p.valuation K a := by
      simpa only [FiniteUnramifiedSquareClasses.ramification_index_one p w.1, pow_one] using
        (HeightOneSpectrum.valuation_liesOver E p w.1 a).symm
    _ = _ := (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' p a).symm

/-- The concrete additive orders also agree on every completed scalar. -/
theorem adicOrder_map (p : HeightOneSpectrum (𝓞 K))
    (w : FinitePlacesAbove (E := E) p)
    (hw : Algebra.IsUnramifiedAt (𝓞 K) w.1.asIdeal) (x : p.adicCompletion K) :
    Bong.NumberFieldCompletion.adicOrder w.1 (finitePlaceAboveCompletionMap p w x) =
      Bong.NumberFieldCompletion.adicOrder p x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Bong.NumberFieldCompletion.adicOrder_apply_of_ne_zero p hx,
      Bong.NumberFieldCompletion.adicOrder_apply_of_ne_zero w.1
        (by simpa only [map_zero] using (finitePlaceAboveCompletionMap p w).injective.ne hx),
      valuation_map p w hw]

end NormEuclidean.UnramifiedCompletionValuation
