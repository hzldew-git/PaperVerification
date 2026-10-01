import TraceEuclidean.OdlyzkoNumericalSinh
import TraceEuclidean.OdlyzkoNumericalCosh

namespace TraceEuclidean.OdlyzkoNumerical

open MeasureTheory LeanCert.Core LeanCert.Engine
open LeanCert.Validity.IntegrationDyadic
open LeanCert.Validity.RangeDyadic
open LeanCert.Validity.TrapezoidalDyadic

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section

private theorem scalarB_strict :
    (16593 / 1000 : ℝ) <
      8 * Real.pi * Real.exp ((5772151 / 10000000 : ℝ) - 992204 / 1000000) := by
  let y : ℝ := 4149889 / 10000000
  let U : ℝ :=
    (∑ m ∈ Finset.range 4, y ^ m / m.factorial) +
      y ^ 4 * 5 / ((Nat.factorial 4 : ℝ) * 4)
  have hy0 : 0 ≤ y := by norm_num [y]
  have hy1 : y ≤ 1 := by norm_num [y]
  have hexp : Real.exp y ≤ U := by
    dsimp [U]
    convert Real.exp_bound' hy0 hy1 (n := 4) (by norm_num) using 1 <;> norm_num
  have hpi : (3141592 / 1000000 : ℝ) < Real.pi := by
    convert Real.pi_gt_d6 using 1 <;> norm_num
  have hnum : (16593 / 1000 : ℝ) * U < 8 * (3141592 / 1000000 : ℝ) := by
    norm_num [U, y, Finset.sum_range_succ, Nat.factorial]
  rw [show (5772151 / 10000000 : ℝ) - 992204 / 1000000 = -y by norm_num [y],
    Real.exp_neg]
  rw [show 8 * Real.pi * (Real.exp y)⁻¹ = (8 * Real.pi) / Real.exp y by
    simp [div_eq_mul_inv, mul_assoc]]
  apply (lt_div_iff₀ (Real.exp_pos y)).2
  calc
    (16593 / 1000 : ℝ) * Real.exp y ≤ (16593 / 1000 : ℝ) * U := by gcongr
    _ < 8 * (3141592 / 1000000 : ℝ) := hnum
    _ < 8 * Real.pi := by gcongr

private theorem scalarA_strict :
    (36347 / 1000 : ℝ) <
      8 * Real.pi * Real.exp (Real.pi / 2 + 5772151 / 10000000 - 1778877 / 1000000) := by
  let x : ℝ := 3691341 / 10000000
  let P : ℝ := ∑ m ∈ Finset.range 5, x ^ m / m.factorial
  have hx0 : 0 ≤ x := by norm_num [x]
  have hpoly : P ≤ Real.exp x := by
    simpa [P] using Real.sum_le_exp_of_nonneg hx0 5
  have hpi : (3141592 / 1000000 : ℝ) < Real.pi := by
    convert Real.pi_gt_d6 using 1 <;> norm_num
  have hx : x ≤ Real.pi / 2 + (5772151 / 10000000 : ℝ) - 1778877 / 1000000 := by
    dsimp [x]
    linarith
  have hnum : (36347 / 1000 : ℝ) < 8 * (3141592 / 1000000 : ℝ) * P := by
    norm_num [P, x, Finset.sum_range_succ, Nat.factorial]
  calc
    (36347 / 1000 : ℝ) < 8 * (3141592 / 1000000 : ℝ) * P := hnum
    _ ≤ 8 * (3141592 / 1000000 : ℝ) * Real.exp x := by gcongr
    _ ≤ 8 * (3141592 / 1000000 : ℝ) *
        Real.exp (Real.pi / 2 + 5772151 / 10000000 - 1778877 / 1000000) := by
      gcongr
    _ < 8 * Real.pi *
        Real.exp (Real.pi / 2 + 5772151 / 10000000 - 1778877 / 1000000) := by
      gcongr

/-- Full sinh integral, including the removable origin and infinite tail. -/
theorem sinhIntegral_upper : odlyzkoSinhIntegral ≤ 992204 / 1000000 := by
  let f : ℝ → ℝ := fun x ↦ (1 - odlyzkoF4 x) / (2 * Real.sinh (x / 2))
  have htailInt : IntegrableOn f (Set.Ioi 8) :=
    odlyzkoSinhIntegrand_integrableOn.mono_set
      (fun x hx ↦ lt_trans (by norm_num : (0 : ℝ) < 8) hx)
  have hsplit :
      (∫ x in (0 : ℝ)..(8 : ℝ), f x) + (∫ x in Set.Ioi (8 : ℝ), f x) =
        ∫ x in Set.Ioi (0 : ℝ), f x :=
    intervalIntegral.integral_interval_add_Ioi odlyzkoSinhIntegrand_integrableOn htailInt
  have h0e : IntervalIntegrable f volume 0 (1 / 5) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1 / 5)]
    exact odlyzkoSinhIntegrand_integrableOn.mono_set Set.Ioc_subset_Ioi_self
  have he8 : IntervalIntegrable f volume (1 / 5) 8 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (1 / 5 : ℝ) ≤ 8)]
    exact odlyzkoSinhIntegrand_integrableOn.mono_set
      (fun x hx ↦ lt_trans (by norm_num : (0 : ℝ) < 1 / 5) hx.1)
  have htail : (∫ x in Set.Ioi (8 : ℝ), f x) ≤
      (2000 / 999) * (18316 / 1000000 : ℝ) :=
    odlyzkoSinhIntegral_tail_le.trans
      (mul_le_mul_of_nonneg_left odlyzkoExpNegFour_le (by norm_num))
  change (∫ x in Set.Ioi (0 : ℝ), f x) ≤ 992204 / 1000000
  rw [← hsplit, ← intervalIntegral.integral_add_adjacent_intervals h0e he8]
  linarith [odlyzkoSinhIntegral_zero_fifth_le, sinh_core_upper, htail]

/-- Full cosh integral, including the infinite tail. -/
theorem coshIntegral_upper : odlyzkoCoshIntegral ≤ 786673 / 1000000 := by
  let f : ℝ → ℝ := fun x ↦ (1 - odlyzkoF4 x) / (2 * Real.cosh (x / 2))
  have htailInt : IntegrableOn f (Set.Ioi 8) :=
    odlyzkoCoshIntegrand_integrableOn.mono_set
      (fun x hx ↦ lt_trans (by norm_num : (0 : ℝ) < 8) hx)
  have hsplit :
      (∫ x in (0 : ℝ)..(8 : ℝ), f x) + (∫ x in Set.Ioi (8 : ℝ), f x) =
        ∫ x in Set.Ioi (0 : ℝ), f x :=
    intervalIntegral.integral_interval_add_Ioi odlyzkoCoshIntegrand_integrableOn htailInt
  have htail : (∫ x in Set.Ioi (8 : ℝ), f x) ≤
      2 * (18316 / 1000000 : ℝ) :=
    odlyzkoCoshIntegral_tail_le.trans
      (mul_le_mul_of_nonneg_left odlyzkoExpNegFour_le (by norm_num))
  change (∫ x in Set.Ioi (0 : ℝ), f x) ≤ 786673 / 1000000
  rw [← hsplit]
  linarith [cosh_core_upper, htail]

theorem archLogB_strict :
    Real.log (16593 / 1000 : ℝ) < odlyzkoArchLogB := by
  have hγ := EulerMascheroni.gamma_lower
  have harg :
      (5772151 / 10000000 : ℝ) - 992204 / 1000000 ≤
        Real.eulerMascheroniConstant - odlyzkoSinhIntegral := by
    linarith [sinhIntegral_upper]
  have hexp := Real.exp_le_exp.mpr harg
  have hscalar : (16593 / 1000 : ℝ) <
      8 * Real.pi * Real.exp
        (Real.eulerMascheroniConstant - odlyzkoSinhIntegral) :=
    scalarB_strict.trans_le (mul_le_mul_of_nonneg_left hexp (by positivity))
  unfold odlyzkoArchLogB
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 16593 / 1000)).2
  have heq :
      Real.exp (Real.eulerMascheroniConstant + Real.log (8 * Real.pi) -
        odlyzkoSinhIntegral) =
        8 * Real.pi * Real.exp
          (Real.eulerMascheroniConstant - odlyzkoSinhIntegral) := by
    rw [show Real.eulerMascheroniConstant + Real.log (8 * Real.pi) -
      odlyzkoSinhIntegral =
      (Real.eulerMascheroniConstant - odlyzkoSinhIntegral) +
        Real.log (8 * Real.pi) by ring, Real.exp_add,
      Real.exp_log (by positivity : 0 < 8 * Real.pi)]
    ring
  rwa [heq]

theorem archLogA_strict :
    Real.log (36347 / 1000 : ℝ) < odlyzkoArchLogA := by
  have hγ := EulerMascheroni.gamma_lower
  have harg :
      Real.pi / 2 + (5772151 / 10000000 : ℝ) - 1778877 / 1000000 ≤
        Real.pi / 2 + Real.eulerMascheroniConstant -
          odlyzkoSinhIntegral - odlyzkoCoshIntegral := by
    linarith [sinhIntegral_upper, coshIntegral_upper]
  have hexp := Real.exp_le_exp.mpr harg
  have hscalar : (36347 / 1000 : ℝ) <
      8 * Real.pi * Real.exp
        (Real.pi / 2 + Real.eulerMascheroniConstant -
          odlyzkoSinhIntegral - odlyzkoCoshIntegral) :=
    scalarA_strict.trans_le (mul_le_mul_of_nonneg_left hexp (by positivity))
  unfold odlyzkoArchLogA odlyzkoArchLogB
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 36347 / 1000)).2
  have heq :
      Real.exp (Real.pi / 2 +
        (Real.eulerMascheroniConstant + Real.log (8 * Real.pi) -
          odlyzkoSinhIntegral) - odlyzkoCoshIntegral) =
        8 * Real.pi * Real.exp
          (Real.pi / 2 + Real.eulerMascheroniConstant -
            odlyzkoSinhIntegral - odlyzkoCoshIntegral) := by
    rw [show Real.pi / 2 +
      (Real.eulerMascheroniConstant + Real.log (8 * Real.pi) -
        odlyzkoSinhIntegral) - odlyzkoCoshIntegral =
      (Real.pi / 2 + Real.eulerMascheroniConstant -
        odlyzkoSinhIntegral - odlyzkoCoshIntegral) +
        Real.log (8 * Real.pi) by ring, Real.exp_add,
      Real.exp_log (by positivity : 0 < 8 * Real.pi)]
    ring
  rwa [heq]

/-- The source-normalized strict archimedean constants for Table 4, `b = 4`. -/
theorem abIntegralCertificate : OdlyzkoABIntegralCertificate :=
  odlyzkoABIntegralCertificate_of_strictBounds archLogA_strict archLogB_strict

end
end TraceEuclidean.OdlyzkoNumerical
