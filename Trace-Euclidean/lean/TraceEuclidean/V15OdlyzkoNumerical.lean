import TraceEuclidean.V15OdlyzkoExplicitFormulaReduction
import LeanCert.Validity.IntegrationDyadic
import LeanCert.Examples.EulerMascheroniBounds
import LeanCert.Validity.Dyadic

/-!
# Certified numerical bounds for Odlyzko's `b = 4` kernel

The finite interval bounds below are checked using LeanCert's dyadic interval
integrator. The origin and infinite tails are bounded analytically in
`V15OdlyzkoExplicitFormulaReduction`.
-/

namespace TraceEuclidean.V15OdlyzkoNumerical

open MeasureTheory LeanCert.Core LeanCert.Engine
open LeanCert.Validity.IntegrationDyadic

-- The certified 131072-cell and 65536-cell checks exceed the default elaboration budget.
set_option maxHeartbeats 0

private def q (r : ℚ) : Expr := .const r
private def xExpr : Expr := .var 0
private def pi : Expr := .namedConst .pi
private def t : Expr := .div xExpr (q 4)
private def angle : Expr := .mul pi t
private def h : Expr :=
  .add
    (.div (.mul (.add (q 2) (.neg t))
      (.add (q 1) (.div (.cos angle) (q 2)))) (q 3))
    (.div (.sin angle) (.mul (q 2) pi))
private def numerator : Expr := .add (.cosh (.div xExpr (q 2))) (.neg h)
private def sinhIntegrand : Expr := .div numerator (.sinh xExpr)
private def coshIntegrand : Expr := .div numerator (.add (q 1) (.cosh xExpr))

private def sinhCore : IntervalRat := ⟨1 / 100, 8, by norm_num⟩
private def coshCore : IntervalRat := ⟨0, 8, by norm_num⟩

noncomputable section

private theorem eval_h (x : ℝ) :
    Expr.eval (fun _ ↦ x) h = v15OdlyzkoHCore (x / 4) := by
  simp [h, q, t, angle, pi, xExpr, Expr.eval, Expr.div,
    MathConst.toReal, v15OdlyzkoHCore]
  ring

private theorem eval_sinhIntegrand (x : ℝ) (hx0 : 0 ≤ x) (hx8 : x ≤ 8) :
    Expr.eval (fun _ ↦ x) sinhIntegrand =
      (1 - v15OdlyzkoF4 x) / (2 * Real.sinh (x / 2)) := by
  have ht0 : 0 ≤ x / 4 := by positivity
  have ht2 : x / 4 ≤ 2 := by linarith
  have hH : v15OdlyzkoH (x / 4) = v15OdlyzkoHCore (x / 4) := by
    simp [v15OdlyzkoH, abs_of_nonneg ht0, ht2]
  by_cases hx : x = 0
  · subst x
    simp [sinhIntegrand, numerator, eval_h, Expr.eval, Expr.div,
      xExpr, q, v15OdlyzkoHCore, v15OdlyzkoF4_zero]
  have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
  rw [v15OdlyzkoSinhIntegrand_eq x hxpos, hH]
  simp [sinhIntegrand, numerator, eval_h, Expr.eval, Expr.div,
    xExpr, q, div_eq_mul_inv, sub_eq_add_neg]

private theorem eval_coshIntegrand (x : ℝ) (hx0 : 0 ≤ x) (hx8 : x ≤ 8) :
    Expr.eval (fun _ ↦ x) coshIntegrand =
      (1 - v15OdlyzkoF4 x) / (2 * Real.cosh (x / 2)) := by
  have ht0 : 0 ≤ x / 4 := by positivity
  have ht2 : x / 4 ≤ 2 := by linarith
  have hH : v15OdlyzkoH (x / 4) = v15OdlyzkoHCore (x / 4) := by
    simp [v15OdlyzkoH, abs_of_nonneg ht0, ht2]
  rw [v15OdlyzkoCoshIntegrand_eq x, hH]
  simp [coshIntegrand, numerator, eval_h, Expr.eval, Expr.div,
    xExpr, q, div_eq_mul_inv, sub_eq_add_neg]

/-- Certified upper enclosure for the nonsingular part of the sinh integral. -/
theorem sinh_core_upper :
    (∫ x in (1 / 100 : ℝ)..(8 : ℝ),
      (1 - v15OdlyzkoF4 x) / (2 * Real.sinh (x / 2))) ≤
      95551 / 100000 := by
  let f : ℝ → ℝ := fun x ↦ (1 - v15OdlyzkoF4 x) / (2 * Real.sinh (x / 2))
  let g : ℝ → ℝ := fun x ↦ Expr.eval (fun _ ↦ x) sinhIntegrand
  have hf : IntervalIntegrable f volume (1 / 100) 8 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (1 / 100 : ℝ) ≤ 8)]
    exact v15OdlyzkoSinhIntegrand_integrableOn.mono_set
      (fun x hx ↦ lt_trans (by norm_num : (0 : ℝ) < 1 / 100) hx.1)
  have hg : IntervalIntegrable g volume (1 / 100) 8 := by
    apply hf.congr_uIoo
    intro x hx
    have hx' : x ∈ Set.Ioo (1 / 100 : ℝ) 8 := by
      simpa only [Set.uIoo_of_le (by norm_num : (1 / 100 : ℝ) ≤ 8)] using hx
    exact (eval_sinhIntegrand x (by linarith [hx'.1]) hx'.2.le).symm
  have hcheck : checkIntegralBoundsDyadicFull sinhIntegrand sinhCore
      131072 (-1) (95551 / 100000) DyadicConfig.highPrecision = true := by
    native_decide
  have hbound := (integral_bounds_of_check_dyadic sinhIntegrand sinhCore
    131072 (by norm_num) (-1) (95551 / 100000) DyadicConfig.highPrecision
    (by norm_num [DyadicConfig.highPrecision]) hcheck
    (by simpa [g, sinhCore] using hg)).2
  have heq : ∫ x in (1 / 100 : ℝ)..(8 : ℝ), f x =
      ∫ x in (1 / 100 : ℝ)..(8 : ℝ), g x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Set.Icc (1 / 100 : ℝ) 8 := by
      simpa only [Set.uIcc_of_le (by norm_num : (1 / 100 : ℝ) ≤ 8)] using hx
    exact (eval_sinhIntegrand x (by linarith [hx'.1]) hx'.2).symm
  change (∫ x in (1 / 100 : ℝ)..(8 : ℝ), f x) ≤ 95551 / 100000
  rw [heq]
  simpa [g, sinhCore] using hbound

/-- Certified upper enclosure for the compact part of the cosh integral. -/
theorem cosh_core_upper :
    (∫ x in (0 : ℝ)..(8 : ℝ),
      (1 - v15OdlyzkoF4 x) / (2 * Real.cosh (x / 2))) ≤
      750041 / 1000000 := by
  let f : ℝ → ℝ := fun x ↦ (1 - v15OdlyzkoF4 x) / (2 * Real.cosh (x / 2))
  let g : ℝ → ℝ := fun x ↦ Expr.eval (fun _ ↦ x) coshIntegrand
  have hf : IntervalIntegrable f volume 0 8 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 8)]
    exact v15OdlyzkoCoshIntegrand_integrableOn.mono_set Set.Ioc_subset_Ioi_self
  have hg : IntervalIntegrable g volume 0 8 := by
    apply hf.congr_uIoo
    intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) 8 := by
      simpa [Set.uIoo_of_le (by norm_num : (0 : ℝ) ≤ 8)] using hx
    exact (eval_coshIntegrand x hx'.1.le hx'.2.le).symm
  have hcheck : checkIntegralBoundsDyadicFull coshIntegrand coshCore
      65536 (-1) (750041 / 1000000) DyadicConfig.highPrecision = true := by
    native_decide
  have hbound := (integral_bounds_of_check_dyadic coshIntegrand coshCore
    65536 (by norm_num) (-1) (750041 / 1000000) DyadicConfig.highPrecision
    (by norm_num [DyadicConfig.highPrecision]) hcheck
    (by simpa [g, coshCore] using hg)).2
  have heq : ∫ x in (0 : ℝ)..(8 : ℝ), f x =
      ∫ x in (0 : ℝ)..(8 : ℝ), g x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 8 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 8)] using hx
    exact (eval_coshIntegrand x hx'.1 hx'.2).symm
  change (∫ x in (0 : ℝ)..(8 : ℝ), f x) ≤ 750041 / 1000000
  rw [heq]
  simpa [g, coshCore] using hbound

end

private def scalarB : Expr :=
  .mul (.mul (q 8) pi)
    (.exp (.add (q (5772151 / 10000000)) (.neg (q (992204 / 1000000)))))

private def scalarA : Expr :=
  .mul (.mul (q 8) pi)
    (.exp (.add (.add (.div pi (q 2)) (q (5772151 / 10000000)))
      (.neg (q (1778877 / 1000000)))))

noncomputable section

private theorem scalarB_strict :
    (16593 / 1000 : ℝ) <
      8 * Real.pi * Real.exp ((5772151 / 10000000 : ℝ) - 992204 / 1000000) := by
  have hcheck : LeanCert.Validity.checkStrictLowerBoundDyadicChecked scalarB
      0 0 (by norm_num) (16593 / 1000) (-80) 20 = true := by
    native_decide
  have h := LeanCert.Validity.verify_strict_lower_bound_dyadic_checked scalarB
    0 0 (by norm_num) (16593 / 1000) (-80) 20 (by norm_num) hcheck
    (0 : ℝ) (by norm_num)
  simpa [scalarB, q, pi, Expr.eval, MathConst.toReal, sub_eq_add_neg,
    mul_assoc] using h

private theorem scalarA_strict :
    (36347 / 1000 : ℝ) <
      8 * Real.pi * Real.exp (Real.pi / 2 + 5772151 / 10000000 - 1778877 / 1000000) := by
  have hcheck : LeanCert.Validity.checkStrictLowerBoundDyadicChecked scalarA
      0 0 (by norm_num) (36347 / 1000) (-80) 20 = true := by
    native_decide
  have h := LeanCert.Validity.verify_strict_lower_bound_dyadic_checked scalarA
    0 0 (by norm_num) (36347 / 1000) (-80) 20 (by norm_num) hcheck
    (0 : ℝ) (by norm_num)
  simpa [scalarA, q, pi, Expr.eval, Expr.div, MathConst.toReal,
    sub_eq_add_neg, add_assoc, mul_assoc, div_eq_mul_inv] using h

/-- Full sinh integral, including the removable origin and infinite tail. -/
theorem sinhIntegral_upper : v15OdlyzkoSinhIntegral ≤ 992204 / 1000000 := by
  let f : ℝ → ℝ := fun x ↦ (1 - v15OdlyzkoF4 x) / (2 * Real.sinh (x / 2))
  have htailInt : IntegrableOn f (Set.Ioi 8) :=
    v15OdlyzkoSinhIntegrand_integrableOn.mono_set
      (fun x hx ↦ lt_trans (by norm_num : (0 : ℝ) < 8) hx)
  have hsplit :
      (∫ x in (0 : ℝ)..(8 : ℝ), f x) + (∫ x in Set.Ioi (8 : ℝ), f x) =
        ∫ x in Set.Ioi (0 : ℝ), f x :=
    intervalIntegral.integral_interval_add_Ioi v15OdlyzkoSinhIntegrand_integrableOn htailInt
  have h0e : IntervalIntegrable f volume 0 (1 / 100) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1 / 100)]
    exact v15OdlyzkoSinhIntegrand_integrableOn.mono_set Set.Ioc_subset_Ioi_self
  have he8 : IntervalIntegrable f volume (1 / 100) 8 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (1 / 100 : ℝ) ≤ 8)]
    exact v15OdlyzkoSinhIntegrand_integrableOn.mono_set
      (fun x hx ↦ lt_trans (by norm_num : (0 : ℝ) < 1 / 100) hx.1)
  have htail : (∫ x in Set.Ioi (8 : ℝ), f x) ≤
      (2000 / 999) * (18316 / 1000000 : ℝ) :=
    v15OdlyzkoSinhIntegral_tail_le.trans
      (mul_le_mul_of_nonneg_left v15OdlyzkoExpNegFour_le (by norm_num))
  change (∫ x in Set.Ioi (0 : ℝ), f x) ≤ 992204 / 1000000
  rw [← hsplit, ← intervalIntegral.integral_add_adjacent_intervals h0e he8]
  linarith [v15OdlyzkoSinhIntegral_zero_hundredth_le, sinh_core_upper, htail]

/-- Full cosh integral, including the infinite tail. -/
theorem coshIntegral_upper : v15OdlyzkoCoshIntegral ≤ 786673 / 1000000 := by
  let f : ℝ → ℝ := fun x ↦ (1 - v15OdlyzkoF4 x) / (2 * Real.cosh (x / 2))
  have htailInt : IntegrableOn f (Set.Ioi 8) :=
    v15OdlyzkoCoshIntegrand_integrableOn.mono_set
      (fun x hx ↦ lt_trans (by norm_num : (0 : ℝ) < 8) hx)
  have hsplit :
      (∫ x in (0 : ℝ)..(8 : ℝ), f x) + (∫ x in Set.Ioi (8 : ℝ), f x) =
        ∫ x in Set.Ioi (0 : ℝ), f x :=
    intervalIntegral.integral_interval_add_Ioi v15OdlyzkoCoshIntegrand_integrableOn htailInt
  have htail : (∫ x in Set.Ioi (8 : ℝ), f x) ≤
      2 * (18316 / 1000000 : ℝ) :=
    v15OdlyzkoCoshIntegral_tail_le.trans
      (mul_le_mul_of_nonneg_left v15OdlyzkoExpNegFour_le (by norm_num))
  change (∫ x in Set.Ioi (0 : ℝ), f x) ≤ 786673 / 1000000
  rw [← hsplit]
  linarith [cosh_core_upper, htail]

theorem archLogB_strict :
    Real.log (16593 / 1000 : ℝ) < v15OdlyzkoArchLogB := by
  have hγ := EulerMascheroni.gamma_lower
  have harg :
      (5772151 / 10000000 : ℝ) - 992204 / 1000000 ≤
        Real.eulerMascheroniConstant - v15OdlyzkoSinhIntegral := by
    linarith [sinhIntegral_upper]
  have hexp := Real.exp_le_exp.mpr harg
  have hscalar : (16593 / 1000 : ℝ) <
      8 * Real.pi * Real.exp
        (Real.eulerMascheroniConstant - v15OdlyzkoSinhIntegral) :=
    scalarB_strict.trans_le (mul_le_mul_of_nonneg_left hexp (by positivity))
  unfold v15OdlyzkoArchLogB
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 16593 / 1000)).2
  have heq :
      Real.exp (Real.eulerMascheroniConstant + Real.log (8 * Real.pi) -
        v15OdlyzkoSinhIntegral) =
        8 * Real.pi * Real.exp
          (Real.eulerMascheroniConstant - v15OdlyzkoSinhIntegral) := by
    rw [show Real.eulerMascheroniConstant + Real.log (8 * Real.pi) -
      v15OdlyzkoSinhIntegral =
      (Real.eulerMascheroniConstant - v15OdlyzkoSinhIntegral) +
        Real.log (8 * Real.pi) by ring, Real.exp_add,
      Real.exp_log (by positivity : 0 < 8 * Real.pi)]
    ring
  rwa [heq]

theorem archLogA_strict :
    Real.log (36347 / 1000 : ℝ) < v15OdlyzkoArchLogA := by
  have hγ := EulerMascheroni.gamma_lower
  have harg :
      Real.pi / 2 + (5772151 / 10000000 : ℝ) - 1778877 / 1000000 ≤
        Real.pi / 2 + Real.eulerMascheroniConstant -
          v15OdlyzkoSinhIntegral - v15OdlyzkoCoshIntegral := by
    linarith [sinhIntegral_upper, coshIntegral_upper]
  have hexp := Real.exp_le_exp.mpr harg
  have hscalar : (36347 / 1000 : ℝ) <
      8 * Real.pi * Real.exp
        (Real.pi / 2 + Real.eulerMascheroniConstant -
          v15OdlyzkoSinhIntegral - v15OdlyzkoCoshIntegral) :=
    scalarA_strict.trans_le (mul_le_mul_of_nonneg_left hexp (by positivity))
  unfold v15OdlyzkoArchLogA v15OdlyzkoArchLogB
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 36347 / 1000)).2
  have heq :
      Real.exp (Real.pi / 2 +
        (Real.eulerMascheroniConstant + Real.log (8 * Real.pi) -
          v15OdlyzkoSinhIntegral) - v15OdlyzkoCoshIntegral) =
        8 * Real.pi * Real.exp
          (Real.pi / 2 + Real.eulerMascheroniConstant -
            v15OdlyzkoSinhIntegral - v15OdlyzkoCoshIntegral) := by
    rw [show Real.pi / 2 +
      (Real.eulerMascheroniConstant + Real.log (8 * Real.pi) -
        v15OdlyzkoSinhIntegral) - v15OdlyzkoCoshIntegral =
      (Real.pi / 2 + Real.eulerMascheroniConstant -
        v15OdlyzkoSinhIntegral - v15OdlyzkoCoshIntegral) +
        Real.log (8 * Real.pi) by ring, Real.exp_add,
      Real.exp_log (by positivity : 0 < 8 * Real.pi)]
    ring
  rwa [heq]

/-- The source-normalized strict archimedean constants for Table 4, `b = 4`. -/
theorem abIntegralCertificate : V15OdlyzkoABIntegralCertificate :=
  v15OdlyzkoABIntegralCertificate_of_strictBounds archLogA_strict archLogB_strict

end
end TraceEuclidean.V15OdlyzkoNumerical
