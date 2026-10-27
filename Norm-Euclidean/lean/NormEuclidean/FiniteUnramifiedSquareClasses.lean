import NormEuclidean.ChapterX.ExtensionNormComponents
import NormEuclidean.ChapterX.QuadraticExtensionNorm
import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Even parameter order from actual unramified finite primes

The hypothesis is mathlib's unramifiedness of the integer-ring extension
at an actual prime above the base prime. The proof uses the ramification
formula for the actual valuations and the square root in the extension.
It applies at dyadic primes as well, but does not assert a dyadic defect bound.
-/

noncomputable section

namespace NormEuclidean.FiniteUnramifiedSquareClasses

open IsDedekindDomain
open scoped NumberField QuadraticAlgebra

universe u
variable {K E : Type u} [Field K] [NumberField K]
  [Field E] [NumberField E] [Algebra K E]

/-- Unramifiedness of the actual integer extension gives ramification index one. -/
theorem ramification_index_one (p : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver p.asIdeal]
    [Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal] :
    p.asIdeal.ramificationIdx' w.asIdeal = 1 := by
  letI := Localization.AtPrime.algebraOfLiesOver p.asIdeal w.asIdeal
  apply (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff w.ne_bot
    (Ideal.map_le_iff_le_comap.mpr (Ideal.over_def w.asIdeal p.asIdeal).le)).mpr
  exact ((Algebra.isUnramifiedAt_iff_map_eq (𝓞 K) p.asIdeal w.asIdeal).mp
    inferInstance).2

/-- A scalar that becomes a square in an unramified extension has even finite order. -/
theorem even_order_of_square (p : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver p.asIdeal]
    [Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal]
    (a : K) (x : E) (hx : x ^ 2 = algebraMap K E a) :
    Even (WithZero.log (p.valuation K a)) := by
  have hv : p.valuation K a = (w.valuation E x) ^ 2 := by
    calc
      _ = w.valuation E (algebraMap K E a) := by
        simpa only [ramification_index_one p w, pow_one] using
          HeightOneSpectrum.valuation_liesOver E p w a
      _ = _ := by rw [← hx, map_pow]
  rw [hv, WithZero.log_pow]
  exact ⟨WithZero.log (w.valuation E x), by simp [two_mul]⟩

/-- One unramified prime above the base prime suffices for a square discriminant parameter. -/
theorem even_order_of_isSquare (p : HeightOneSpectrum (𝓞 K))
    (w : ExtensionIdeleNorm.FinitePlacesAbove (E := E) p)
    (hw : Algebra.IsUnramifiedAt (𝓞 K) w.1.asIdeal)
    (a : K) (ha : IsSquare (algebraMap K E a)) :
    Even (WithZero.log (p.valuation K a)) := by
  letI : w.1.asIdeal.LiesOver p.asIdeal :=
    ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩
  letI := hw
  obtain ⟨x, hx⟩ := ha
  exact even_order_of_square p w.1 a x (by simpa only [pow_two] using hx.symm)

/-- The discriminant parameter has even order at an actual unramified quadratic prime. -/
theorem quadratic_even_order (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 K))
    (hunram : letI := QuadraticExtensionNorm.quadraticExtensionField theta htheta
      letI := QuadraticExtensionNorm.quadraticExtensionNumberField theta htheta
      ∀ w : ExtensionIdeleNorm.FinitePlacesAbove
          (E := QuadraticAlgebra K (theta : K) 0) p,
        Algebra.IsUnramifiedAt (𝓞 K) w.1.asIdeal) :
    Even (WithZero.log (p.valuation K (theta : K))) := by
  letI := QuadraticExtensionNorm.quadraticExtensionField theta htheta
  letI := QuadraticExtensionNorm.quadraticExtensionNumberField theta htheta
  obtain ⟨w⟩ := ExtensionIdeleNorm.finitePlacesAbove_nonempty
    (E := QuadraticAlgebra K (theta : K) 0) p
  apply even_order_of_isSquare p w (hunram w) (theta : K)
  exact ⟨ω, by ext <;> simp⟩

end NormEuclidean.FiniteUnramifiedSquareClasses
