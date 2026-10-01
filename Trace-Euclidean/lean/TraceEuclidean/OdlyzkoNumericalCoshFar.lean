import TraceEuclidean.OdlyzkoNumericalCoshFarDerivative

namespace TraceEuclidean.OdlyzkoNumerical

open MeasureTheory LeanCert.Core LeanCert.Engine
open LeanCert.Validity.IntegrationDyadic
open LeanCert.Validity.RangeDyadic
open LeanCert.Validity.TrapezoidalDyadic

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section

theorem cosh_core_far_upper :
    (∫ x in (4 : ℝ)..(8 : ℝ),
      (1 - odlyzkoF4 x) / (2 * Real.cosh (x / 2))) ≤ 229754 / 1000000 := by
  have hc2open : ContDiffOn ℝ 2 farCoshFunction Set.univ := by
    change ContDiffOn ℝ 2 (fun x ↦ Expr.eval (fun _ ↦ x) farCoshIntegrand) Set.univ
    exact Expr.contDiffOn_eval farCosh_diffSupported 2 (fun x _ ↦ farCosh_regular x)
  have h45raw := expr_bisected_piece_upper_of_open
    (e := farCoshIntegrand) (P := Certificate.unitFourFive)
    (L := Certificate.unitFourFiveA) (R := Certificate.unitFourFiveB)
    (N := 32) (M := 1 / 4)
    (targetL := 57167554897 / 1000000000000)
    (targetR := 45601445103 / 1000000000000)
    (cfg := Certificate.quadrature19Depth14) (s := Set.univ)
    (by norm_num [Certificate.unitFourFiveA])
    (by norm_num [Certificate.unitFourFiveB])
    (by norm_num [Certificate.unitFourFiveA, Certificate.unitFourFive])
    (by norm_num [Certificate.unitFourFiveA, Certificate.unitFourFiveB])
    (by norm_num [Certificate.unitFourFiveB, Certificate.unitFourFive]) isOpen_univ (by simp)
    hc2open
    (by
      intro x hx
      change |iteratedDeriv 2 farCoshFunction x| ≤ ((1 / 4 : ℚ) : ℝ)
      exact farCoshSecond_fourFive_bound x hx)
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.quadrature19Depth14])
    (by exact Certificate.coshFarFourFiveAQuadrature)
    (by exact Certificate.coshFarFourFiveBQuadrature)
  have h45 : (∫ x in (4 : ℝ)..(5 : ℝ), farCoshFunction x) ≤ 102769 / 1000000 := by
    convert h45raw using 1 <;>
      norm_num [Certificate.unitFourFive, farCoshFunction]
  have h56raw := expr_bisected_piece_upper_of_open
    (e := farCoshIntegrand) (P := Certificate.unitFiveSix)
    (L := Certificate.unitFiveSixA) (R := Certificate.unitFiveSixB)
    (N := 32) (M := 1 / 4)
    (targetL := 35941394668 / 1000000000000)
    (targetR := 28150605332 / 1000000000000)
    (cfg := Certificate.quadrature20Depth14) (s := Set.univ)
    (by norm_num [Certificate.unitFiveSixA])
    (by norm_num [Certificate.unitFiveSixB])
    (by norm_num [Certificate.unitFiveSixA, Certificate.unitFiveSix])
    (by norm_num [Certificate.unitFiveSixA, Certificate.unitFiveSixB])
    (by norm_num [Certificate.unitFiveSixB, Certificate.unitFiveSix]) isOpen_univ (by simp)
    hc2open
    (by
      intro x hx
      change |iteratedDeriv 2 farCoshFunction x| ≤ ((1 / 4 : ℚ) : ℝ)
      exact farCoshSecond_fiveSix_bound x hx)
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.quadrature20Depth14])
    (by exact Certificate.coshFarFiveSixAQuadrature)
    (by exact Certificate.coshFarFiveSixBQuadrature)
  have h56 : (∫ x in (5 : ℝ)..(6 : ℝ), farCoshFunction x) ≤ 64092 / 1000000 := by
    convert h56raw using 1 <;>
      norm_num [Certificate.unitFiveSix, farCoshFunction]
  have h67raw := expr_bisected_piece_upper_of_open
    (e := farCoshIntegrand) (P := Certificate.unitSixSeven)
    (L := Certificate.unitSixSevenA) (R := Certificate.unitSixSevenB)
    (N := 32) (M := 1 / 4)
    (targetL := 21981130045 / 1000000000000)
    (targetR := 17141869955 / 1000000000000)
    (cfg := Certificate.quadrature19Depth14) (s := Set.univ)
    (by norm_num [Certificate.unitSixSevenA])
    (by norm_num [Certificate.unitSixSevenB])
    (by norm_num [Certificate.unitSixSevenA, Certificate.unitSixSeven])
    (by norm_num [Certificate.unitSixSevenA, Certificate.unitSixSevenB])
    (by norm_num [Certificate.unitSixSevenB, Certificate.unitSixSeven]) isOpen_univ (by simp)
    hc2open
    (by
      intro x hx
      change |iteratedDeriv 2 farCoshFunction x| ≤ ((1 / 4 : ℚ) : ℝ)
      exact farCoshSecond_sixSeven_bound x hx)
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.quadrature19Depth14])
    (by exact Certificate.coshFarSixSevenAQuadrature)
    (by exact Certificate.coshFarSixSevenBQuadrature)
  have h67 : (∫ x in (6 : ℝ)..(7 : ℝ), farCoshFunction x) ≤ 39123 / 1000000 := by
    convert h67raw using 1 <;>
      norm_num [Certificate.unitSixSeven, farCoshFunction]
  have h78raw := expr_bisected_piece_upper_of_open
    (e := farCoshIntegrand) (P := Certificate.unitSevenEight)
    (L := Certificate.unitSevenEightA) (R := Certificate.unitSevenEightB)
    (N := 32) (M := 1 / 4)
    (targetL := 13359839719 / 1000000000000)
    (targetR := 10410160281 / 1000000000000)
    (cfg := Certificate.quadrature19Depth14) (s := Set.univ)
    (by norm_num [Certificate.unitSevenEightA])
    (by norm_num [Certificate.unitSevenEightB])
    (by norm_num [Certificate.unitSevenEightA, Certificate.unitSevenEight])
    (by norm_num [Certificate.unitSevenEightA, Certificate.unitSevenEightB])
    (by norm_num [Certificate.unitSevenEightB, Certificate.unitSevenEight]) isOpen_univ (by simp)
    hc2open
    (by
      intro x hx
      change |iteratedDeriv 2 farCoshFunction x| ≤ ((1 / 4 : ℚ) : ℝ)
      exact farCoshSecond_sevenEight_bound x hx)
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.quadrature19Depth14])
    (by exact Certificate.coshFarSevenEightAQuadrature)
    (by exact Certificate.coshFarSevenEightBQuadrature)
  have h78 : (∫ x in (7 : ℝ)..(8 : ℝ), farCoshFunction x) ≤ 23770 / 1000000 := by
    convert h78raw using 1 <;>
      norm_num [Certificate.unitSevenEight, farCoshFunction]
  have hcont : ContinuousOn farCoshFunction (Set.Icc (4 : ℝ) 8) :=
    hc2open.continuousOn.mono (by simp)
  have hi45 : IntervalIntegrable farCoshFunction volume (4 : ℝ) 5 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (4 : ℝ) ≤ 5)]
    exact hcont.mono (by intro x hx; constructor <;> linarith [hx.1, hx.2])
  have hi56 : IntervalIntegrable farCoshFunction volume (5 : ℝ) 6 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (5 : ℝ) ≤ 6)]
    exact hcont.mono (by intro x hx; constructor <;> linarith [hx.1, hx.2])
  have hi67 : IntervalIntegrable farCoshFunction volume (6 : ℝ) 7 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (6 : ℝ) ≤ 7)]
    exact hcont.mono (by intro x hx; constructor <;> linarith [hx.1, hx.2])
  have hi78 : IntervalIntegrable farCoshFunction volume (7 : ℝ) 8 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (7 : ℝ) ≤ 8)]
    exact hcont.mono (by intro x hx; constructor <;> linarith [hx.1, hx.2])
  have h46 : (∫ x in (4 : ℝ)..(6 : ℝ), farCoshFunction x) ≤ 166861 / 1000000 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi45 hi56]
    linarith
  have h68 : (∫ x in (6 : ℝ)..(8 : ℝ), farCoshFunction x) ≤ 62893 / 1000000 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi67 hi78]
    linarith
  have hg : (∫ x in (4 : ℝ)..(8 : ℝ), farCoshFunction x) ≤ 229754 / 1000000 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi45.trans hi56) (hi67.trans hi78)]
    linarith
  calc
    (∫ x in (4 : ℝ)..(8 : ℝ),
        (1 - odlyzkoF4 x) / (2 * Real.cosh (x / 2))) =
        ∫ x in (4 : ℝ)..(8 : ℝ), farCoshFunction x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Set.Icc (4 : ℝ) 8 := by
        rw [Set.uIcc_of_le (by norm_num : (4 : ℝ) ≤ 8)] at hx
        exact hx
      exact (eval_farCoshIntegrand x (by linarith [hx'.1]) hx'.2).symm
    _ ≤ 229754 / 1000000 := hg

end
end TraceEuclidean.OdlyzkoNumerical
