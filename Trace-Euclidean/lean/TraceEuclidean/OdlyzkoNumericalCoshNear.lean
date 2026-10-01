import TraceEuclidean.OdlyzkoNumericalCoshNearDerivative

namespace TraceEuclidean.OdlyzkoNumerical

open MeasureTheory LeanCert.Core LeanCert.Engine
open LeanCert.Validity.IntegrationDyadic
open LeanCert.Validity.RangeDyadic
open LeanCert.Validity.TrapezoidalDyadic

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section

theorem cosh_core_near_upper :
    (∫ x in (0 : ℝ)..(4 : ℝ),
      (1 - odlyzkoF4 x) / (2 * Real.cosh (x / 2))) ≤ 520275 / 1000000 := by
  have hc2open : ContDiffOn ℝ 2 stableCoshFunction Set.univ := by
    change ContDiffOn ℝ 2 (fun x ↦ Expr.eval (fun _ ↦ x) stableCoshIntegrand) Set.univ
    exact Expr.contDiffOn_eval stableCosh_diffSupported 2
      (fun x _ ↦ stableCosh_regular x)
  have h01araw := expr_bisected_piece_upper_of_open
    (e := stableCoshIntegrand) (P := Certificate.unitZeroHalf)
    (L := Certificate.unitZeroHalfA) (R := Certificate.unitZeroHalfB)
    (N := 32) (M := 1)
    (targetL := 589502356 / 1000000000000)
    (targetR := 3980107644 / 1000000000000)
    (cfg := Certificate.quadrature20Depth8) (s := Set.univ)
    (by norm_num [Certificate.unitZeroHalfA])
    (by norm_num [Certificate.unitZeroHalfB])
    (by norm_num [Certificate.unitZeroHalfA, Certificate.unitZeroHalf])
    (by norm_num [Certificate.unitZeroHalfA, Certificate.unitZeroHalfB])
    (by norm_num [Certificate.unitZeroHalfB, Certificate.unitZeroHalf]) isOpen_univ (by simp)
    hc2open
    (by
      intro x hx
      change |iteratedDeriv 2 stableCoshFunction x| ≤ ((1 : ℚ) : ℝ)
      exact stableCoshSecond_zeroOne_bound x (by
          norm_num [Certificate.unitZeroHalf, Certificate.unitZeroOne] at hx ⊢
          constructor <;> linarith [hx.1, hx.2]))
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.quadrature20Depth8])
    (by exact Certificate.coshNearZeroHalfAQuadrature)
    (by exact Certificate.coshNearZeroHalfBQuadrature)
  have h01a : (∫ x in (0 : ℝ)..(1 / 2 : ℝ), stableCoshFunction x) ≤
      456961 / 100000000 := by
    convert h01araw using 1 <;>
      norm_num [Certificate.unitZeroHalf, stableCoshFunction]
  have h01braw := expr_bisected_piece_upper_of_open
    (e := stableCoshIntegrand) (P := Certificate.unitHalfOne)
    (L := Certificate.unitHalfOneA) (R := Certificate.unitHalfOneB)
    (N := 32) (M := 1)
    (targetL := 10134713105 / 1000000000000)
    (targetR := 17986676895 / 1000000000000)
    (cfg := Certificate.quadrature20Depth8) (s := Set.univ)
    (by norm_num [Certificate.unitHalfOneA])
    (by norm_num [Certificate.unitHalfOneB])
    (by norm_num [Certificate.unitHalfOneA, Certificate.unitHalfOne])
    (by norm_num [Certificate.unitHalfOneA, Certificate.unitHalfOneB])
    (by norm_num [Certificate.unitHalfOneB, Certificate.unitHalfOne]) isOpen_univ (by simp)
    hc2open
    (by
      intro x hx
      change |iteratedDeriv 2 stableCoshFunction x| ≤ ((1 : ℚ) : ℝ)
      exact stableCoshSecond_zeroOne_bound x (by
          norm_num [Certificate.unitHalfOne, Certificate.unitZeroOne] at hx ⊢
          constructor <;> linarith [hx.1, hx.2]))
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.quadrature20Depth8])
    (by exact Certificate.coshNearHalfOneAQuadrature)
    (by exact Certificate.coshNearHalfOneBQuadrature)
  have h01b : (∫ x in (1 / 2 : ℝ)..(1 : ℝ), stableCoshFunction x) ≤
      2812139 / 100000000 := by
    convert h01braw using 1 <;>
      norm_num [Certificate.unitHalfOne, stableCoshFunction]
  have hi01a : IntervalIntegrable stableCoshFunction volume (0 : ℝ) (1 / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact hc2open.continuousOn.mono (by simp)
  have hi01b : IntervalIntegrable stableCoshFunction volume (1 / 2 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    exact hc2open.continuousOn.mono (by simp)
  have h01 : (∫ x in (0 : ℝ)..(1 : ℝ), stableCoshFunction x) ≤ 32691 / 1000000 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi01a hi01b]
    linarith
  have h12raw := expr_bisected_piece_upper_of_open
    (e := stableCoshIntegrand) (P := Certificate.unitOneTwo)
    (L := Certificate.unitOneTwoA) (R := Certificate.unitOneTwoB)
    (N := 32) (M := 1 / 4)
    (targetL := 60343446832 / 1000000000000)
    (targetR := 85145553168 / 1000000000000)
    (cfg := Certificate.quadrature20Depth10) (s := Set.univ)
    (by norm_num [Certificate.unitOneTwoA])
    (by norm_num [Certificate.unitOneTwoB])
    (by norm_num [Certificate.unitOneTwoA, Certificate.unitOneTwo])
    (by norm_num [Certificate.unitOneTwoA, Certificate.unitOneTwoB])
    (by norm_num [Certificate.unitOneTwoB, Certificate.unitOneTwo]) isOpen_univ (by simp)
    hc2open
    (by
      intro x hx
      change |iteratedDeriv 2 stableCoshFunction x| ≤ ((1 / 4 : ℚ) : ℝ)
      exact stableCoshSecond_oneTwo_bound x hx)
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.quadrature20Depth10])
    (by exact Certificate.coshNearOneTwoAQuadrature)
    (by exact Certificate.coshNearOneTwoBQuadrature)
  have h12 : (∫ x in (1 : ℝ)..(2 : ℝ), stableCoshFunction x) ≤ 145489 / 1000000 := by
    convert h12raw using 1 <;>
      norm_num [Certificate.unitOneTwo, stableCoshFunction]
  have h23raw := expr_bisected_piece_upper_of_open
    (e := stableCoshIntegrand) (P := Certificate.unitTwoThree)
    (L := Certificate.unitTwoThreeA) (R := Certificate.unitTwoThreeB)
    (N := 32) (M := 1 / 4)
    (targetL := 95540846389 / 1000000000000)
    (targetR := 93195153611 / 1000000000000)
    (cfg := Certificate.quadrature20Depth12) (s := Set.univ)
    (by norm_num [Certificate.unitTwoThreeA])
    (by norm_num [Certificate.unitTwoThreeB])
    (by norm_num [Certificate.unitTwoThreeA, Certificate.unitTwoThree])
    (by norm_num [Certificate.unitTwoThreeA, Certificate.unitTwoThreeB])
    (by norm_num [Certificate.unitTwoThreeB, Certificate.unitTwoThree]) isOpen_univ (by simp)
    hc2open
    (by
      intro x hx
      change |iteratedDeriv 2 stableCoshFunction x| ≤ ((1 / 4 : ℚ) : ℝ)
      exact stableCoshSecond_twoThree_bound x hx)
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.quadrature20Depth12])
    (by exact Certificate.coshNearTwoThreeAQuadrature)
    (by exact Certificate.coshNearTwoThreeBQuadrature)
  have h23 : (∫ x in (2 : ℝ)..(3 : ℝ), stableCoshFunction x) ≤ 188736 / 1000000 := by
    convert h23raw using 1 <;>
      norm_num [Certificate.unitTwoThree, stableCoshFunction]
  have h34raw := expr_bisected_piece_upper_of_open
    (e := stableCoshIntegrand) (P := Certificate.unitThreeFour)
    (L := Certificate.unitThreeFourA) (R := Certificate.unitThreeFourB)
    (N := 32) (M := 1 / 4)
    (targetL := 83180757862 / 1000000000000)
    (targetR := 70178242138 / 1000000000000)
    (cfg := Certificate.quadrature20Depth13) (s := Set.univ)
    (by norm_num [Certificate.unitThreeFourA])
    (by norm_num [Certificate.unitThreeFourB])
    (by norm_num [Certificate.unitThreeFourA, Certificate.unitThreeFour])
    (by norm_num [Certificate.unitThreeFourA, Certificate.unitThreeFourB])
    (by norm_num [Certificate.unitThreeFourB, Certificate.unitThreeFour]) isOpen_univ (by simp)
    hc2open
    (by
      intro x hx
      change |iteratedDeriv 2 stableCoshFunction x| ≤ ((1 / 4 : ℚ) : ℝ)
      exact stableCoshSecond_threeFour_bound x hx)
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.quadrature20Depth13])
    (by exact Certificate.coshNearThreeFourAQuadrature)
    (by exact Certificate.coshNearThreeFourBQuadrature)
  have h34 : (∫ x in (3 : ℝ)..(4 : ℝ), stableCoshFunction x) ≤ 153359 / 1000000 := by
    convert h34raw using 1 <;>
      norm_num [Certificate.unitThreeFour, stableCoshFunction]
  have hcont : ContinuousOn stableCoshFunction (Set.Icc (0 : ℝ) 4) :=
    hc2open.continuousOn.mono (by simp)
  have hi01 : IntervalIntegrable stableCoshFunction volume (0 : ℝ) 1 :=
    hi01a.trans hi01b
  have hi12 : IntervalIntegrable stableCoshFunction volume (1 : ℝ) 2 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
    exact hcont.mono (by intro x hx; constructor <;> linarith [hx.1, hx.2])
  have hi23 : IntervalIntegrable stableCoshFunction volume (2 : ℝ) 3 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)]
    exact hcont.mono (by intro x hx; constructor <;> linarith [hx.1, hx.2])
  have hi34 : IntervalIntegrable stableCoshFunction volume (3 : ℝ) 4 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 4)]
    exact hcont.mono (by intro x hx; constructor <;> linarith [hx.1, hx.2])
  have h02 : (∫ x in (0 : ℝ)..(2 : ℝ), stableCoshFunction x) ≤ 178180 / 1000000 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi01 hi12]
    linarith
  have h24 : (∫ x in (2 : ℝ)..(4 : ℝ), stableCoshFunction x) ≤ 342095 / 1000000 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi23 hi34]
    linarith
  have hg : (∫ x in (0 : ℝ)..(4 : ℝ), stableCoshFunction x) ≤ 520275 / 1000000 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi01.trans hi12) (hi23.trans hi34)]
    linarith
  calc
    (∫ x in (0 : ℝ)..(4 : ℝ),
        (1 - odlyzkoF4 x) / (2 * Real.cosh (x / 2))) =
        ∫ x in (0 : ℝ)..(4 : ℝ), stableCoshFunction x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Set.Icc (0 : ℝ) 4 := by
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 4)] at hx
        exact hx
      exact (eval_stableCoshIntegrand x hx'.1 (by linarith [hx'.2])).symm
    _ ≤ 520275 / 1000000 := hg

end
end TraceEuclidean.OdlyzkoNumerical
