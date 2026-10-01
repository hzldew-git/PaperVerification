import TraceEuclidean.OdlyzkoNumericalSinhFarDerivative

namespace TraceEuclidean.OdlyzkoNumerical

open MeasureTheory LeanCert.Core LeanCert.Engine
open LeanCert.Validity.IntegrationDyadic
open LeanCert.Validity.RangeDyadic
open LeanCert.Validity.TrapezoidalDyadic

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section

theorem sinh_core_far_upper :
    (∫ x in (4 : ℝ)..(8 : ℝ),
      (1 - odlyzkoF4 x) / (2 * Real.sinh (x / 2))) ≤ 232976 / 1000000 := by
  have hc2open : ContDiffOn ℝ 2 farSinhFunction (Set.Ioi 0) := by
    change ContDiffOn ℝ 2 (fun x ↦ Expr.eval (fun _ ↦ x) farSinhIntegrand) (Set.Ioi 0)
    exact Expr.contDiffOn_eval farSinh_diffSupported 2 (fun x hx ↦ farSinh_regular hx)
  have h45araw := expr_bisected_piece_upper_of_open
    (e := farSinhIntegrand) (P := Certificate.unitFourFourHalf)
    (L := Certificate.unitFourFourHalfA) (R := Certificate.unitFourFourHalfB)
    (N := 20) (M := 1 / 4)
    (targetL := 31134358249 / 1000000000000)
    (targetR := 27720941751 / 1000000000000)
    (cfg := Certificate.quadrature19Depth14) (s := Set.Ioi 0)
    (by norm_num [Certificate.unitFourFourHalfA])
    (by norm_num [Certificate.unitFourFourHalfB])
    (by norm_num [Certificate.unitFourFourHalfA, Certificate.unitFourFourHalf])
    (by norm_num [Certificate.unitFourFourHalfA, Certificate.unitFourFourHalfB])
    (by norm_num [Certificate.unitFourFourHalfB, Certificate.unitFourFourHalf]) isOpen_Ioi
    (by intro x hx; norm_num [Certificate.unitFourFourHalf] at hx ⊢; linarith)
    hc2open
    (by
      intro x hx
      change |iteratedDeriv 2 farSinhFunction x| ≤ ((1 / 4 : ℚ) : ℝ)
      exact farSinhSecond_fourFive_bound x (by
          norm_num [Certificate.unitFourFourHalf, Certificate.unitFourFive] at hx ⊢
          constructor <;> linarith [hx.1, hx.2]))
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.quadrature19Depth14])
    (by exact Certificate.sinhFarFourFourHalfAQuadrature)
    (by exact Certificate.sinhFarFourFourHalfBQuadrature)
  have h45a : (∫ x in (4 : ℝ)..(9 / 2 : ℝ), farSinhFunction x) ≤
      588553 / 10000000 := by
    convert h45araw using 1 <;>
      norm_num [Certificate.unitFourFourHalf, farSinhFunction]
  have h45braw := expr_bisected_piece_upper_of_open
    (e := farSinhIntegrand) (P := Certificate.unitFourHalfFive)
    (L := Certificate.unitFourHalfFiveA) (R := Certificate.unitFourHalfFiveB)
    (N := 20) (M := 1 / 4)
    (targetL := 24609795413 / 1000000000000)
    (targetR := 21802904587 / 1000000000000)
    (cfg := Certificate.quadrature19Depth14) (s := Set.Ioi 0)
    (by norm_num [Certificate.unitFourHalfFiveA])
    (by norm_num [Certificate.unitFourHalfFiveB])
    (by norm_num [Certificate.unitFourHalfFiveA, Certificate.unitFourHalfFive])
    (by norm_num [Certificate.unitFourHalfFiveA, Certificate.unitFourHalfFiveB])
    (by norm_num [Certificate.unitFourHalfFiveB, Certificate.unitFourHalfFive]) isOpen_Ioi
    (by intro x hx; norm_num [Certificate.unitFourHalfFive] at hx ⊢; linarith)
    hc2open
    (by
      intro x hx
      change |iteratedDeriv 2 farSinhFunction x| ≤ ((1 / 4 : ℚ) : ℝ)
      exact farSinhSecond_fourFive_bound x (by
          norm_num [Certificate.unitFourHalfFive, Certificate.unitFourFive] at hx ⊢
          constructor <;> linarith [hx.1, hx.2]))
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.quadrature19Depth14])
    (by exact Certificate.sinhFarFourHalfFiveAQuadrature)
    (by exact Certificate.sinhFarFourHalfFiveBQuadrature)
  have h45b : (∫ x in (9 / 2 : ℝ)..(5 : ℝ), farSinhFunction x) ≤
      464127 / 10000000 := by
    convert h45braw using 1 <;>
      norm_num [Certificate.unitFourHalfFive, farSinhFunction]
  have hi45a : IntervalIntegrable farSinhFunction volume (4 : ℝ) (9 / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (4 : ℝ) ≤ 9 / 2)]
    exact hc2open.continuousOn.mono
      (fun x hx ↦ lt_of_lt_of_le (by norm_num) hx.1)
  have hi45b : IntervalIntegrable farSinhFunction volume (9 / 2 : ℝ) 5 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (9 / 2 : ℝ) ≤ 5)]
    exact hc2open.continuousOn.mono
      (fun x hx ↦ lt_of_lt_of_le (by norm_num) hx.1)
  have h45 : (∫ x in (4 : ℝ)..(5 : ℝ), farSinhFunction x) ≤ 105268 / 1000000 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi45a hi45b]
    linarith
  have h56araw := expr_bisected_piece_upper_of_open
    (e := farSinhIntegrand) (P := Certificate.unitFiveFiveHalf)
    (L := Certificate.unitFiveFiveHalfA) (R := Certificate.unitFiveFiveHalfB)
    (N := 20) (M := 1 / 4)
    (targetL := 19285622439 / 1000000000000)
    (targetR := 17042777561 / 1000000000000)
    (cfg := Certificate.quadrature20Depth14) (s := Set.Ioi 0)
    (by norm_num [Certificate.unitFiveFiveHalfA])
    (by norm_num [Certificate.unitFiveFiveHalfB])
    (by norm_num [Certificate.unitFiveFiveHalfA, Certificate.unitFiveFiveHalf])
    (by norm_num [Certificate.unitFiveFiveHalfA, Certificate.unitFiveFiveHalfB])
    (by norm_num [Certificate.unitFiveFiveHalfB, Certificate.unitFiveFiveHalf]) isOpen_Ioi
    (by intro x hx; norm_num [Certificate.unitFiveFiveHalf] at hx ⊢; linarith)
    hc2open
    (by
      intro x hx
      change |iteratedDeriv 2 farSinhFunction x| ≤ ((1 / 4 : ℚ) : ℝ)
      exact farSinhSecond_fiveSix_bound x (by
          norm_num [Certificate.unitFiveFiveHalf, Certificate.unitFiveSix] at hx ⊢
          constructor <;> linarith [hx.1, hx.2]))
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.quadrature20Depth14])
    (by exact Certificate.sinhFarFiveFiveHalfAQuadrature)
    (by exact Certificate.sinhFarFiveFiveHalfBQuadrature)
  have h56a : (∫ x in (5 : ℝ)..(11 / 2 : ℝ), farSinhFunction x) ≤
      363284 / 10000000 := by
    convert h56araw using 1 <;>
      norm_num [Certificate.unitFiveFiveHalf, farSinhFunction]
  have h56braw := expr_bisected_piece_upper_of_open
    (e := farSinhIntegrand) (P := Certificate.unitFiveHalfSix)
    (L := Certificate.unitFiveHalfSixA) (R := Certificate.unitFiveHalfSixB)
    (N := 20) (M := 1 / 4)
    (targetL := 15049055419 / 1000000000000)
    (targetR := 13284544581 / 1000000000000)
    (cfg := Certificate.quadrature20Depth14) (s := Set.Ioi 0)
    (by norm_num [Certificate.unitFiveHalfSixA])
    (by norm_num [Certificate.unitFiveHalfSixB])
    (by norm_num [Certificate.unitFiveHalfSixA, Certificate.unitFiveHalfSix])
    (by norm_num [Certificate.unitFiveHalfSixA, Certificate.unitFiveHalfSixB])
    (by norm_num [Certificate.unitFiveHalfSixB, Certificate.unitFiveHalfSix]) isOpen_Ioi
    (by intro x hx; norm_num [Certificate.unitFiveHalfSix] at hx ⊢; linarith)
    hc2open
    (by
      intro x hx
      change |iteratedDeriv 2 farSinhFunction x| ≤ ((1 / 4 : ℚ) : ℝ)
      exact farSinhSecond_fiveSix_bound x (by
          norm_num [Certificate.unitFiveHalfSix, Certificate.unitFiveSix] at hx ⊢
          constructor <;> linarith [hx.1, hx.2]))
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.quadrature20Depth14])
    (by exact Certificate.sinhFarFiveHalfSixAQuadrature)
    (by exact Certificate.sinhFarFiveHalfSixBQuadrature)
  have h56b : (∫ x in (11 / 2 : ℝ)..(6 : ℝ), farSinhFunction x) ≤
      283336 / 10000000 := by
    convert h56braw using 1 <;>
      norm_num [Certificate.unitFiveHalfSix, farSinhFunction]
  have hi56a : IntervalIntegrable farSinhFunction volume (5 : ℝ) (11 / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (5 : ℝ) ≤ 11 / 2)]
    exact hc2open.continuousOn.mono
      (fun x hx ↦ lt_of_lt_of_le (by norm_num) hx.1)
  have hi56b : IntervalIntegrable farSinhFunction volume (11 / 2 : ℝ) 6 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (11 / 2 : ℝ) ≤ 6)]
    exact hc2open.continuousOn.mono
      (fun x hx ↦ lt_of_lt_of_le (by norm_num) hx.1)
  have h56 : (∫ x in (5 : ℝ)..(6 : ℝ), farSinhFunction x) ≤ 64662 / 1000000 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi56a hi56b]
    linarith
  have h67araw := expr_bisected_piece_upper_of_open
    (e := farSinhIntegrand) (P := Certificate.unitSixSixHalf)
    (L := Certificate.unitSixSixHalfA) (R := Certificate.unitSixSixHalfB)
    (N := 20) (M := 1 / 4)
    (targetL := 11722532115 / 1000000000000)
    (targetR := 10344767885 / 1000000000000)
    (cfg := Certificate.quadrature20Depth14) (s := Set.Ioi 0)
    (by norm_num [Certificate.unitSixSixHalfA])
    (by norm_num [Certificate.unitSixSixHalfB])
    (by norm_num [Certificate.unitSixSixHalfA, Certificate.unitSixSixHalf])
    (by norm_num [Certificate.unitSixSixHalfA, Certificate.unitSixSixHalfB])
    (by norm_num [Certificate.unitSixSixHalfB, Certificate.unitSixSixHalf]) isOpen_Ioi
    (by intro x hx; norm_num [Certificate.unitSixSixHalf] at hx ⊢; linarith)
    hc2open
    (by
      intro x hx
      change |iteratedDeriv 2 farSinhFunction x| ≤ ((1 / 4 : ℚ) : ℝ)
      exact farSinhSecond_sixSeven_bound x (by
          norm_num [Certificate.unitSixSixHalf, Certificate.unitSixSeven] at hx ⊢
          constructor <;> linarith [hx.1, hx.2]))
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.quadrature20Depth14])
    (by exact Certificate.sinhFarSixSixHalfAQuadrature)
    (by exact Certificate.sinhFarSixSixHalfBQuadrature)
  have h67a : (∫ x in (6 : ℝ)..(13 / 2 : ℝ), farSinhFunction x) ≤
      220673 / 10000000 := by
    convert h67araw using 1 <;>
      norm_num [Certificate.unitSixSixHalf, farSinhFunction]
  have h67braw := expr_bisected_piece_upper_of_open
    (e := farSinhIntegrand) (P := Certificate.unitSixHalfSeven)
    (L := Certificate.unitSixHalfSevenA) (R := Certificate.unitSixHalfSevenB)
    (N := 20) (M := 1 / 4)
    (targetL := 9127071700 / 1000000000000)
    (targetR := 8054628300 / 1000000000000)
    (cfg := Certificate.quadrature20Depth14) (s := Set.Ioi 0)
    (by norm_num [Certificate.unitSixHalfSevenA])
    (by norm_num [Certificate.unitSixHalfSevenB])
    (by norm_num [Certificate.unitSixHalfSevenA, Certificate.unitSixHalfSeven])
    (by norm_num [Certificate.unitSixHalfSevenA, Certificate.unitSixHalfSevenB])
    (by norm_num [Certificate.unitSixHalfSevenB, Certificate.unitSixHalfSeven]) isOpen_Ioi
    (by intro x hx; norm_num [Certificate.unitSixHalfSeven] at hx ⊢; linarith)
    hc2open
    (by
      intro x hx
      change |iteratedDeriv 2 farSinhFunction x| ≤ ((1 / 4 : ℚ) : ℝ)
      exact farSinhSecond_sixSeven_bound x (by
          norm_num [Certificate.unitSixHalfSeven, Certificate.unitSixSeven] at hx ⊢
          constructor <;> linarith [hx.1, hx.2]))
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.quadrature20Depth14])
    (by exact Certificate.sinhFarSixHalfSevenAQuadrature)
    (by exact Certificate.sinhFarSixHalfSevenBQuadrature)
  have h67b : (∫ x in (13 / 2 : ℝ)..(7 : ℝ), farSinhFunction x) ≤
      171817 / 10000000 := by
    convert h67braw using 1 <;>
      norm_num [Certificate.unitSixHalfSeven, farSinhFunction]
  have hi67a : IntervalIntegrable farSinhFunction volume (6 : ℝ) (13 / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (6 : ℝ) ≤ 13 / 2)]
    exact hc2open.continuousOn.mono
      (fun x hx ↦ lt_of_lt_of_le (by norm_num) hx.1)
  have hi67b : IntervalIntegrable farSinhFunction volume (13 / 2 : ℝ) 7 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (13 / 2 : ℝ) ≤ 7)]
    exact hc2open.continuousOn.mono
      (fun x hx ↦ lt_of_lt_of_le (by norm_num) hx.1)
  have h67 : (∫ x in (6 : ℝ)..(7 : ℝ), farSinhFunction x) ≤ 39249 / 1000000 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi67a hi67b]
    linarith
  have h78raw := expr_bisected_piece_upper_of_open
    (e := farSinhIntegrand) (P := Certificate.unitSevenEight)
    (L := Certificate.unitSevenEightA) (R := Certificate.unitSevenEightB)
    (N := 32) (M := 1 / 4)
    (targetL := 13378734391 / 1000000000000)
    (targetR := 10418265609 / 1000000000000)
    (cfg := Certificate.quadrature20Depth14) (s := Set.Ioi 0)
    (by norm_num [Certificate.unitSevenEightA])
    (by norm_num [Certificate.unitSevenEightB])
    (by norm_num [Certificate.unitSevenEightA, Certificate.unitSevenEight])
    (by norm_num [Certificate.unitSevenEightA, Certificate.unitSevenEightB])
    (by norm_num [Certificate.unitSevenEightB, Certificate.unitSevenEight]) isOpen_Ioi
    (by intro x hx; norm_num [Certificate.unitSevenEight] at hx ⊢; linarith)
    hc2open
    (by
      intro x hx
      change |iteratedDeriv 2 farSinhFunction x| ≤ ((1 / 4 : ℚ) : ℝ)
      exact farSinhSecond_sevenEight_bound x hx)
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.quadrature20Depth14])
    (by exact Certificate.sinhFarSevenEightAQuadrature)
    (by exact Certificate.sinhFarSevenEightBQuadrature)
  have h78 : (∫ x in (7 : ℝ)..(8 : ℝ), farSinhFunction x) ≤ 23797 / 1000000 := by
    convert h78raw using 1 <;>
      norm_num [Certificate.unitSevenEight, farSinhFunction]
  have hcont : ContinuousOn farSinhFunction (Set.Icc (4 : ℝ) 8) :=
    hc2open.continuousOn.mono (fun x hx ↦ lt_of_lt_of_le (by norm_num) hx.1)
  have hi45 : IntervalIntegrable farSinhFunction volume (4 : ℝ) 5 := hi45a.trans hi45b
  have hi56 : IntervalIntegrable farSinhFunction volume (5 : ℝ) 6 := hi56a.trans hi56b
  have hi67 : IntervalIntegrable farSinhFunction volume (6 : ℝ) 7 := hi67a.trans hi67b
  have hi78 : IntervalIntegrable farSinhFunction volume (7 : ℝ) 8 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (7 : ℝ) ≤ 8)]
    exact hcont.mono (by intro x hx; constructor <;> linarith [hx.1, hx.2])
  have h46 : (∫ x in (4 : ℝ)..(6 : ℝ), farSinhFunction x) ≤ 169930 / 1000000 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi45 hi56]
    linarith
  have h68 : (∫ x in (6 : ℝ)..(8 : ℝ), farSinhFunction x) ≤ 63046 / 1000000 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi67 hi78]
    linarith
  have hg : (∫ x in (4 : ℝ)..(8 : ℝ), farSinhFunction x) ≤ 232976 / 1000000 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi45.trans hi56) (hi67.trans hi78)]
    linarith
  calc
    (∫ x in (4 : ℝ)..(8 : ℝ),
        (1 - odlyzkoF4 x) / (2 * Real.sinh (x / 2))) =
        ∫ x in (4 : ℝ)..(8 : ℝ), farSinhFunction x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Set.Icc (4 : ℝ) 8 := by
        rw [Set.uIcc_of_le (by norm_num : (4 : ℝ) ≤ 8)] at hx
        exact hx
      exact (eval_farSinhIntegrand x (lt_of_lt_of_le (by norm_num) hx'.1) hx'.2).symm
    _ ≤ 232976 / 1000000 := hg


end
end TraceEuclidean.OdlyzkoNumerical
