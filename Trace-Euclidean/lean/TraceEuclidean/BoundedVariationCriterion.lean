import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.EMetricSpace.BoundedVariation

open Set MeasureTheory intervalIntegral

/-- A globally differentiable real function has bounded variation when its
derivative admits a nonnegative integrable majorant. -/
theorem boundedVariationOn_univ_of_integrable_deriv_bound
    {f B : ℝ → ℝ}
    (hfc : Continuous f)
    (hfd : Differentiable ℝ f)
    (hB0 : ∀ x, 0 ≤ B x)
    (hderiv : ∀ x, ‖deriv f x‖ ≤ B x)
    (hBi : Integrable B) :
    BoundedVariationOn f Set.univ := by
  suffices hvar : eVariationOn f Set.univ ≤ ENNReal.ofReal (∫ x, B x) by
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvar
  rw [eVariationOn]
  apply iSup_le
  rintro ⟨n, u, hu, hu_mem⟩
  have hstep (i : ℕ) :
      dist (f (u (i + 1))) (f (u i)) ≤
        ∫ x in u i..u (i + 1), B x := by
    have hui : u i ≤ u (i + 1) := hu (Nat.le_succ i)
    rw [dist_eq_norm]
    exact norm_sub_le_integral_of_norm_deriv_le_of_le hui
      hfc.continuousOn hfd.differentiableOn
      (Filter.Eventually.of_forall fun x _ ↦ hderiv x)
      hBi.intervalIntegrable
  calc
    (∑ i ∈ Finset.range n,
        edist (f (u (i + 1))) (f (u i))) =
        ENNReal.ofReal
          (∑ i ∈ Finset.range n,
            dist (f (u (i + 1))) (f (u i))) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ dist_nonneg)]
      simp only [edist_dist]
    _ ≤ ENNReal.ofReal
          (∑ i ∈ Finset.range n,
            ∫ x in u i..u (i + 1), B x) := by
      exact ENNReal.ofReal_le_ofReal
        (Finset.sum_le_sum fun i _ ↦ hstep i)
    _ = ENNReal.ofReal (∫ x in u 0..u n, B x) := by
      rw [intervalIntegral.sum_integral_adjacent_intervals]
      intro k hk
      exact hBi.intervalIntegrable
    _ ≤ ENNReal.ofReal (∫ x, B x) := by
      apply ENNReal.ofReal_le_ofReal
      rw [intervalIntegral.integral_of_le (hu (Nat.zero_le n))]
      exact setIntegral_le_integral hBi
        (Filter.Eventually.of_forall hB0)

theorem boundedVariationOn_of_integrable_deriv_bound
    {f B : ℝ → ℝ} {s : Set ℝ}
    (hfc : Continuous f)
    (hfd : ∀ a ∈ s, ∀ b ∈ s,
      DifferentiableOn ℝ f (Ioo a b))
    (hmem : ∀ a ∈ s, ∀ b ∈ s, Ioo a b ⊆ s)
    (hne : ∀ a ∈ s, ∀ b ∈ s, ∀ x ∈ Ioo a b, x ≠ 0)
    (hB0 : ∀ x, 0 ≤ B x)
    (hderiv : ∀ x, x ∈ s → x ≠ 0 → ‖deriv f x‖ ≤ B x)
    (hBi : Integrable B) :
    BoundedVariationOn f s := by
  suffices hvar : eVariationOn f s ≤ ENNReal.ofReal (∫ x, B x) by
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvar
  rw [eVariationOn]
  apply iSup_le
  rintro ⟨n, u, hu, hu_mem⟩
  have hstep (i : ℕ) :
      dist (f (u (i + 1))) (f (u i)) ≤
        ∫ x in u i..u (i + 1), B x := by
    have hui : u i ≤ u (i + 1) := hu (Nat.le_succ i)
    rw [dist_eq_norm]
    exact norm_sub_le_integral_of_norm_deriv_le_of_le hui
      hfc.continuousOn (hfd (u i) (hu_mem i) (u (i + 1)) (hu_mem (i + 1)))
      (Filter.Eventually.of_forall fun x hx ↦ by
        exact hderiv x
          (hmem (u i) (hu_mem i) (u (i + 1)) (hu_mem (i + 1)) hx)
          (hne (u i) (hu_mem i) (u (i + 1)) (hu_mem (i + 1)) x hx))
      hBi.intervalIntegrable
  calc
    (∑ i ∈ Finset.range n,
        edist (f (u (i + 1))) (f (u i))) =
        ENNReal.ofReal
          (∑ i ∈ Finset.range n,
            dist (f (u (i + 1))) (f (u i))) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ dist_nonneg)]
      simp only [edist_dist]
    _ ≤ ENNReal.ofReal
          (∑ i ∈ Finset.range n,
            ∫ x in u i..u (i + 1), B x) := by
      exact ENNReal.ofReal_le_ofReal
        (Finset.sum_le_sum fun i _ ↦ hstep i)
    _ = ENNReal.ofReal (∫ x in u 0..u n, B x) := by
      rw [intervalIntegral.sum_integral_adjacent_intervals]
      intro k hk
      exact hBi.intervalIntegrable
    _ ≤ ENNReal.ofReal (∫ x, B x) := by
      apply ENNReal.ofReal_le_ofReal
      rw [intervalIntegral.integral_of_le (hu (Nat.zero_le n))]
      exact setIntegral_le_integral hBi
        (Filter.Eventually.of_forall hB0)
