import NormEuclidean.ChapterX.QuadraticSquareDescent

/-!
# Transferring prime square tests down a number-field extension

The map of actual completions preserves squares. At odd places, units
that are squares upstairs can be recognized downstairs by multiplying
them by one fixed nonsquare that remains nonsquare upstairs.
-/

noncomputable section

namespace NormEuclidean.SquarePrimeTransfer

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm
open scoped NumberField

universe u
variable {K E : Type u} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

/-- A nonsquare in a completion upstairs remains nonsquare at its underlying base prime. -/
theorem nonsquare_under (w : HeightOneSpectrum (𝓞 E)) (a : K)
    (ha : ¬ IsSquare (algebraMap E (w.adicCompletion E) (algebraMap K E a))) :
    ¬ IsSquare (algebraMap K ((w.under (𝓞 K)).adicCompletion K) a) := by
  intro h
  apply ha
  let p := w.under (𝓞 K)
  let f := finitePlaceAboveCompletionMap p (⟨w, rfl⟩ : FinitePlacesAbove (E := E) p)
  have hh := h.map f.toMonoidHom
  have he : f (algebraMap K (p.adicCompletion K) a) =
      algebraMap E (w.adicCompletion E) (algebraMap K E a) := by
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply] using
        finitePlaceAboveCompletionMap_global p ⟨w, rfl⟩ a
  exact he ▸ hh

/-- Oddness descends to every prime above an odd prime. -/
theorem odd_above (w : HeightOneSpectrum (𝓞 E))
    (h : (2 : 𝓞 K) ∉ (w.under (𝓞 K)).asIdeal) : (2 : 𝓞 E) ∉ w.asIdeal := by
  intro hw
  apply h
  change algebraMap (𝓞 K) (𝓞 E) (2 : 𝓞 K) ∈ w.asIdeal
  rw [map_ofNat]
  exact hw

/-- If a nonsquare is still nonsquare upstairs, every upstairs square unit
is a downstairs square unit at a good prime. -/
theorem square_under_of_nonsquare (w : HeightOneSpectrum (𝓞 E)) (a b : Kˣ)
    (htwo : (2 : 𝓞 K) ∉ (w.under (𝓞 K)).asIdeal)
    (haunit : (w.under (𝓞 K)).valuation K a.val = 1)
    (hbunit : (w.under (𝓞 K)).valuation K b.val = 1)
    (ha : ¬ IsSquare (algebraMap E (w.adicCompletion E) (algebraMap K E a.val)))
    (hb : IsSquare (algebraMap E (w.adicCompletion E) (algebraMap K E b.val))) :
    IsSquare (Units.map
      (algebraMap K ((w.under (𝓞 K)).adicCompletion K)).toMonoidHom b) := by
  let p := w.under (𝓞 K)
  let A := Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom a
  let B := Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom b
  have hAns : ¬ IsSquare A := by
    intro h
    exact nonsquare_under w a.val ha ((GlobalSquare.unit_square_iff A).mp h)
  by_contra hBns
  have hAu : Valued.v A.val = 1 :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' p a.val).trans haunit
  have hBu : Valued.v B.val = 1 :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' p b.val).trans hbunit
  have hab := QuadraticSquareDescent.nonsquare_unit_product p htwo A B hAu hBu hAns hBns
  have hlocal : IsSquare (algebraMap K (p.adicCompletion K) (a * b).val) := by
    have hh := (GlobalSquare.unit_square_iff (A * B)).mp hab
    change IsSquare (algebraMap K (p.adicCompletion K) a.val *
      algebraMap K (p.adicCompletion K) b.val) at hh
    simpa only [Units.val_mul, map_mul] using hh
  have hup : IsSquare (algebraMap E (w.adicCompletion E) (algebraMap K E (a * b).val)) := by
    by_contra hns
    exact nonsquare_under w (a * b).val hns hlocal
  have hquot := hup.mul hb.inv
  apply ha
  have hb0 : algebraMap E (w.adicCompletion E) (algebraMap K E b.val) ≠ 0 :=
    (map_ne_zero _).mpr ((map_ne_zero _).mpr b.ne_zero)
  simpa only [Units.val_mul, map_mul, mul_inv_cancel_right₀ hb0] using hquot

end NormEuclidean.SquarePrimeTransfer
