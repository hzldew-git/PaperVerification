import TraceEuclidean.OdlyzkoZeroStrip

/-!
# Reflection symmetry of Odlyzko's source-normalized transform

This elementary identity follows from the exact evenness of the compactly
supported test function. It is useful when the zero terms of an explicit
formula are organized in pairs under `s ↦ 1 - s`.
-/

namespace TraceEuclidean

noncomputable section
open MeasureTheory

/-- Odlyzko's transform is symmetric about the center of the critical strip. -/
theorem odlyzkoPhi_one_sub (s : ℂ) :
    odlyzkoPhi (1 - s) = odlyzkoPhi s := by
  unfold odlyzkoPhi
  calc
    (∫ x : ℝ, (odlyzkoF4 x : ℂ) *
        Complex.exp (((1 - s) - (1 / 2 : ℂ)) * (x : ℂ))) =
      ∫ x : ℝ, (odlyzkoF4 (-x) : ℂ) *
        Complex.exp ((s - (1 / 2 : ℂ)) * ((-x : ℝ) : ℂ)) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [odlyzkoF4_even]
      congr 1
      congr 1
      push_cast
      ring
    _ = ∫ x : ℝ, (odlyzkoF4 x : ℂ) *
        Complex.exp ((s - (1 / 2 : ℂ)) * (x : ℂ)) := by
      exact integral_neg_eq_self
        (fun x : ℝ ↦ (odlyzkoF4 x : ℂ) *
          Complex.exp ((s - (1 / 2 : ℂ)) * (x : ℂ))) volume

end
end TraceEuclidean
