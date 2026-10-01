import TraceEuclidean.OdlyzkoNumericalSinhMiddleOneDerivative

namespace TraceEuclidean.OdlyzkoNumerical

open MeasureTheory LeanCert.Core LeanCert.Engine
open LeanCert.Validity.IntegrationDyadic
open LeanCert.Validity.RangeDyadic
open LeanCert.Validity.TrapezoidalDyadic

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section

theorem sinh_middle_one_left_upper :
    (∫ x in (1 / 2 : ℝ)..(13 / 12 : ℝ), stableSinhFunction x) ≤ 931324 / 10000000 := by
  have hc2open : ContDiffOn ℝ 2 stableSinhFunction (Set.Ioi 0) := by
    change ContDiffOn ℝ 2 (fun x ↦ Expr.eval (fun _ ↦ x) stableSinhIntegrand) (Set.Ioi 0)
    exact Expr.contDiffOn_eval stableSinh_diffSupported 2
      (fun x hx ↦ stableSinh_regular hx)
  have hraw := expr_bisected_piece_upper_of_open
    (e := stableSinhIntegrand) (P := Certificate.sinhMiddleOneLeft)
    (L := Certificate.sinhMiddleOneLeftA) (R := Certificate.sinhMiddleOneLeftB)
    (N := 32) (M := 1)
    (targetL := 39754772652 / 1000000000000)
    (targetR := 53377627348 / 1000000000000)
    (cfg := Certificate.quadrature20Depth10) (s := Set.Ioi 0)
    (by norm_num [Certificate.sinhMiddleOneLeftA])
    (by norm_num [Certificate.sinhMiddleOneLeftB])
    (by norm_num [Certificate.sinhMiddleOneLeftA, Certificate.sinhMiddleOneLeft])
    (by norm_num [Certificate.sinhMiddleOneLeftA, Certificate.sinhMiddleOneLeftB])
    (by norm_num [Certificate.sinhMiddleOneLeftB, Certificate.sinhMiddleOneLeft])
    isOpen_Ioi
    (by
      intro x hx
      norm_num [Certificate.sinhMiddleOneLeft] at hx ⊢
      linarith)
    hc2open
    (by
      intro x hx
      change |iteratedDeriv 2 stableSinhFunction x| ≤ ((1 : ℚ) : ℝ)
      exact stableSinhSecond_middleOne_bound x (by
          norm_num [Certificate.sinhMiddleOneLeft, Certificate.sinhMiddleOne] at hx ⊢
          constructor <;> linarith [hx.1, hx.2]))
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.quadrature20Depth10])
    (by exact Certificate.sinhMiddleOneLeftAQuadrature)
    (by exact Certificate.sinhMiddleOneLeftBQuadrature)
  convert hraw using 1 <;>
    norm_num [Certificate.sinhMiddleOneLeft, stableSinhFunction]

end
end TraceEuclidean.OdlyzkoNumerical
