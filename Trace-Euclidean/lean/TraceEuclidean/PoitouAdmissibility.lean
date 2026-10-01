import TraceEuclidean.PoitouDifferenceQuotient

/-!
# Source hypotheses for Poitou's degree-eleven test function

This module packages the analytic side conditions used by Poitou's explicit
formula.  Keeping them in one proposition makes the remaining theorem boundary
precise: the concrete test function is proved admissible, while the general
Dedekind-zeta explicit-formula passage is developed separately.
-/

namespace TraceEuclidean.PoitouKernel

noncomputable section

open MeasureTheory Set FourierTransform
open TraceEuclidean.PoitouDegreeEleven

/-- Source-facing admissibility data for Poitou's scaled test and its complete
hyperbolic-secant kernel. -/
structure PoitouAdmissible (y : ℝ) : Prop where
  y_pos : 0 < y
  scaled_even : ∀ x, poitouScaledTest y (-x) = poitouScaledTest y x
  scaled_nonneg : ∀ x, 0 ≤ poitouScaledTest y x
  scaled_continuous : Continuous (poitouScaledTest y)
  scaled_normalized : poitouScaledTest y 0 = 1
  scaled_integrable : Integrable (poitouScaledTest y) volume
  full_even : ∀ x, poitouFullKernel y (-x) = poitouFullKernel y x
  full_nonneg : ∀ x, 0 ≤ poitouFullKernel y x
  full_continuous : Continuous (poitouFullKernel y)
  full_normalized : poitouFullKernel y 0 = 1
  full_integrable : Integrable (poitouFullKernel y) volume
  full_boundedVariation :
    BoundedVariationOn (poitouFullKernel y) Set.univ
  quotient_continuous : Continuous poitouDifferenceQuotient
  quotient_boundedVariation :
    BoundedVariationOn poitouDifferenceQuotient Set.univ
  fourier_real : ∀ w,
    (𝓕 (poitouFullKernelComplex y) w).im = 0
  fourier_nonneg : ∀ w,
    0 ≤ (𝓕 (poitouFullKernelComplex y) w).re
  endpoint_degree_eleven :
    4 / (11 : ℝ) *
        (∫ x in Set.Ioi (0 : ℝ), poitouScaledTest y x) =
      12 * Real.pi / (55 * Real.sqrt y)

/-- The rational parameter `1351/2000` satisfies every concrete regularity,
positivity, Fourier, and endpoint condition in Poitou's source theorem. -/
theorem poitouY_admissible : PoitouAdmissible poitouY := by
  have hy : 0 < poitouY := by norm_num [poitouY]
  exact
    { y_pos := hy
      scaled_even := poitouScaledTest_even poitouY
      scaled_nonneg := poitouScaledTest_nonneg poitouY
      scaled_continuous := poitouScaledTest_continuous poitouY
      scaled_normalized := poitouScaledTest_zero poitouY
      scaled_integrable := poitouScaledTest_integrable hy
      full_even := poitouFullKernel_even poitouY
      full_nonneg := poitouFullKernel_nonneg poitouY
      full_continuous := poitouFullKernel_continuous poitouY
      full_normalized := poitouFullKernel_zero poitouY
      full_integrable := poitouFullKernel_integrable hy
      full_boundedVariation := poitouFullKernel_boundedVariation hy.le
      quotient_continuous := poitouDifferenceQuotient_continuous
      quotient_boundedVariation := poitouDifferenceQuotient_boundedVariation
      fourier_real := poitouFullKernel_fourier_im_eq_zero hy
      fourier_nonneg := poitouFullKernel_fourier_re_nonneg hy
      endpoint_degree_eleven := by
        convert poitouEndpointCorrection 11 hy using 1 <;> norm_num }

end

end TraceEuclidean.PoitouKernel
