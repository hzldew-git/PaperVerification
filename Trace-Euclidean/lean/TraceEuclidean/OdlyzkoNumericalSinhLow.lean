import TraceEuclidean.OdlyzkoNumericalBase

namespace TraceEuclidean.OdlyzkoNumerical

open MeasureTheory LeanCert.Core LeanCert.Engine
open LeanCert.Validity.IntegrationDyadic
open LeanCert.Validity.RangeDyadic
open LeanCert.Validity.TrapezoidalDyadic

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section

theorem sinh_core_low_upper :
    (∫ x in (1 / 5 : ℝ)..(1 / 2 : ℝ),
      (1 - odlyzkoF4 x) / (2 * Real.sinh (x / 2))) ≤ 23318 / 1000000 := by
  have hc2open : ContDiffOn ℝ 2 stableSinhFunction (Set.Ioi 0) := by
    change ContDiffOn ℝ 2 (fun x ↦ Expr.eval (fun _ ↦ x) stableSinhIntegrand) (Set.Ioi 0)
    exact Expr.contDiffOn_eval stableSinh_diffSupported 2
      (fun x hx ↦ stableSinh_regular hx)
  have h1raw := expr_piece_upper_of_open
    (e := stableSinhIntegrand) (I := Certificate.sinhCoreLowOne)
    (N := 32) (M := 2) (target := 4017 / 1000000)
    (cfg := Certificate.fastLowQuadratureConfig) (s := Set.Ioi 0)
    (by norm_num [Certificate.sinhCoreLowOne]) isOpen_Ioi
    (by
      intro x hx
      norm_num [Certificate.sinhCoreLowOne] at hx ⊢
      linarith)
    hc2open
    (by
      intro x hx
      exact stableSinhSecond_low_bound x (by
        norm_num [Certificate.sinhCoreLowOne] at hx ⊢
        constructor <;> linarith [hx.1, hx.2]))
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.fastLowQuadratureConfig])
    (by exact Certificate.lowSinhOneQuadrature)
  have h1 : (∫ x in (1 / 5 : ℝ)..(11 / 40 : ℝ), stableSinhFunction x) ≤
      4017 / 1000000 := by
    simpa [Certificate.sinhCoreLowOne, stableSinhFunction] using h1raw
  have h2raw := expr_piece_upper_of_open
    (e := stableSinhIntegrand) (I := Certificate.sinhCoreLowTwo)
    (N := 32) (M := 2) (target := 5247 / 1000000)
    (cfg := Certificate.fastLowQuadratureConfig) (s := Set.Ioi 0)
    (by norm_num [Certificate.sinhCoreLowTwo]) isOpen_Ioi
    (by
      intro x hx
      norm_num [Certificate.sinhCoreLowTwo] at hx ⊢
      linarith)
    hc2open
    (by
      intro x hx
      exact stableSinhSecond_low_bound x (by
        norm_num [Certificate.sinhCoreLowTwo] at hx ⊢
        constructor <;> linarith [hx.1, hx.2]))
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.fastLowQuadratureConfig])
    (by exact Certificate.lowSinhTwoQuadrature)
  have h2 : (∫ x in (11 / 40 : ℝ)..(7 / 20 : ℝ), stableSinhFunction x) ≤
      5247 / 1000000 := by
    simpa [Certificate.sinhCoreLowTwo, stableSinhFunction] using h2raw
  have h3raw := expr_piece_upper_of_open
    (e := stableSinhIntegrand) (I := Certificate.sinhCoreLowThree)
    (N := 32) (M := 2) (target := 6446 / 1000000)
    (cfg := Certificate.fastLowQuadratureConfig) (s := Set.Ioi 0)
    (by norm_num [Certificate.sinhCoreLowThree]) isOpen_Ioi
    (by
      intro x hx
      norm_num [Certificate.sinhCoreLowThree] at hx ⊢
      linarith)
    hc2open
    (by
      intro x hx
      exact stableSinhSecond_low_bound x (by
        norm_num [Certificate.sinhCoreLowThree] at hx ⊢
        constructor <;> linarith [hx.1, hx.2]))
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.fastLowQuadratureConfig])
    (by exact Certificate.lowSinhThreeQuadrature)
  have h3 : (∫ x in (7 / 20 : ℝ)..(17 / 40 : ℝ), stableSinhFunction x) ≤
      6446 / 1000000 := by
    simpa [Certificate.sinhCoreLowThree, stableSinhFunction] using h3raw
  have h4raw := expr_piece_upper_of_open
    (e := stableSinhIntegrand) (I := Certificate.sinhCoreLowFour)
    (N := 32) (M := 2) (target := 7608 / 1000000)
    (cfg := Certificate.fastLowQuadratureConfig) (s := Set.Ioi 0)
    (by norm_num [Certificate.sinhCoreLowFour]) isOpen_Ioi
    (by
      intro x hx
      norm_num [Certificate.sinhCoreLowFour] at hx ⊢
      linarith)
    hc2open
    (by
      intro x hx
      exact stableSinhSecond_low_bound x (by
        norm_num [Certificate.sinhCoreLowFour] at hx ⊢
        constructor <;> linarith [hx.1, hx.2]))
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.fastLowQuadratureConfig])
    (by exact Certificate.lowSinhFourQuadrature)
  have h4 : (∫ x in (17 / 40 : ℝ)..(1 / 2 : ℝ), stableSinhFunction x) ≤
      7608 / 1000000 := by
    simpa [Certificate.sinhCoreLowFour, stableSinhFunction] using h4raw
  have hi1 : IntervalIntegrable stableSinhFunction volume (1 / 5 : ℝ) (11 / 40) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (1 / 5 : ℝ) ≤ 11 / 40)]
    exact hc2open.continuousOn.mono
      (fun x hx ↦ lt_of_lt_of_le (by norm_num) hx.1)
  have hi2 : IntervalIntegrable stableSinhFunction volume (11 / 40 : ℝ) (7 / 20) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (11 / 40 : ℝ) ≤ 7 / 20)]
    exact hc2open.continuousOn.mono
      (fun x hx ↦ lt_of_lt_of_le (by norm_num) hx.1)
  have hi3 : IntervalIntegrable stableSinhFunction volume (7 / 20 : ℝ) (17 / 40) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (7 / 20 : ℝ) ≤ 17 / 40)]
    exact hc2open.continuousOn.mono
      (fun x hx ↦ lt_of_lt_of_le (by norm_num) hx.1)
  have hi4 : IntervalIntegrable stableSinhFunction volume (17 / 40 : ℝ) (1 / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (17 / 40 : ℝ) ≤ 1 / 2)]
    exact hc2open.continuousOn.mono
      (fun x hx ↦ lt_of_lt_of_le (by norm_num) hx.1)
  have h12 : (∫ x in (1 / 5 : ℝ)..(7 / 20 : ℝ), stableSinhFunction x) ≤
      9264 / 1000000 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
    linarith
  have h34 : (∫ x in (7 / 20 : ℝ)..(1 / 2 : ℝ), stableSinhFunction x) ≤
      14054 / 1000000 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi3 hi4]
    linarith
  have hg : (∫ x in (1 / 5 : ℝ)..(1 / 2 : ℝ), stableSinhFunction x) ≤
      23318 / 1000000 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi1.trans hi2) (hi3.trans hi4)]
    linarith
  calc
    (∫ x in (1 / 5 : ℝ)..(1 / 2 : ℝ),
        (1 - odlyzkoF4 x) / (2 * Real.sinh (x / 2))) =
        ∫ x in (1 / 5 : ℝ)..(1 / 2 : ℝ), stableSinhFunction x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Set.Icc (1 / 5 : ℝ) (1 / 2) := by
        rw [Set.uIcc_of_le (by norm_num : (1 / 5 : ℝ) ≤ 1 / 2)] at hx
        exact hx
      exact (eval_stableSinhIntegrand x (lt_of_lt_of_le (by norm_num) hx'.1)
        (by linarith [hx'.2])).symm
    _ ≤ 23318 / 1000000 := hg


end
end TraceEuclidean.OdlyzkoNumerical
