import TraceEuclidean.OdlyzkoZeroStrip
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
theorem odlyzkoPhi_tendsto_zero_vertical (a : ℝ) :
    Tendsto (fun w : ℝ ↦
      odlyzkoPhi (((a + 1 / 2 : ℝ) : ℂ) +
        (((-2 * Real.pi * w : ℝ) : ℂ) * Complex.I)))
      (cocompact ℝ) (𝓝 0) := by
  have hEq (w : ℝ) :
      odlyzkoPhi (((a + 1 / 2 : ℝ) : ℂ) +
        (((-2 * Real.pi * w : ℝ) : ℂ) * Complex.I)) =
        𝓕 (odlyzkoTiltedF4 a) w := by
    rw [odlyzkoPhi_eq_fourier]
    simp [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im]
  simpa only [hEq] using Real.zero_at_infty_fourier (odlyzkoTiltedF4 a)

end
end TraceEuclidean
