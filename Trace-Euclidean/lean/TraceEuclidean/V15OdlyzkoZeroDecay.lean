import TraceEuclidean.V15OdlyzkoZeroStrip
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# Vertical decay of the source zero transform

Riemann-Lebesgue gives vanishing along every fixed vertical line. This is a
qualitative step toward a zero-sum convergence proof; a quantitative decay
rate and a Dedekind-zeta zero count are still needed for that application.
-/

namespace TraceEuclidean

noncomputable section
open Filter FourierTransform
open scoped Topology

/-- The zero transform vanishes at both ends of every fixed vertical line,
written in the Fourier frequency normalization used by mathlib. -/
theorem v15OdlyzkoPhi_tendsto_zero_vertical (a : ℝ) :
    Tendsto (fun w : ℝ ↦
      v15OdlyzkoPhi (((a + 1 / 2 : ℝ) : ℂ) +
        (((-2 * Real.pi * w : ℝ) : ℂ) * Complex.I)))
      (cocompact ℝ) (𝓝 0) := by
  have hEq (w : ℝ) :
      v15OdlyzkoPhi (((a + 1 / 2 : ℝ) : ℂ) +
        (((-2 * Real.pi * w : ℝ) : ℂ) * Complex.I)) =
        𝓕 (v15OdlyzkoTiltedF4 a) w := by
    rw [v15OdlyzkoPhi_eq_fourier]
    simp [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im]
  simpa only [hEq] using Real.zero_at_infty_fourier (v15OdlyzkoTiltedF4 a)

end
end TraceEuclidean
