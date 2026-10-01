import TraceEuclidean.OdlyzkoNumericalSinhMiddleOneDerivative

namespace TraceEuclidean.OdlyzkoNumerical

open MeasureTheory LeanCert.Core LeanCert.Engine
open LeanCert.Validity.IntegrationDyadic
open LeanCert.Validity.RangeDyadic
open LeanCert.Validity.TrapezoidalDyadic

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section

theorem sinh_middle_one_right_upper :
    (∫ x in (13 / 12 : ℝ)..(5 / 3 : ℝ), stableSinhFunction x) ≤ 1320886 / 10000000 := by
  have hc2open : ContDiffOn ℝ 2 stableSinhFunction (Set.Ioi 0) := by
    change ContDiffOn ℝ 2 (fun x ↦ Expr.eval (fun _ ↦ x) stableSinhIntegrand) (Set.Ioi 0)
    exact Expr.contDiffOn_eval stableSinh_diffSupported 2
      (fun x hx ↦ stableSinh_regular hx)
  have hraw := expr_bisected_piece_upper_of_open
    (e := stableSinhIntegrand) (P := Certificate.sinhMiddleOneRight)
    (L := Certificate.sinhMiddleOneRightA) (R := Certificate.sinhMiddleOneRightB)
    (N := 32) (M := 1)
    (targetL := 63139624987 / 1000000000000)
    (targetR := 68948975013 / 1000000000000)
    (cfg := Certificate.quadrature20Depth10) (s := Set.Ioi 0)
    (by norm_num [Certificate.sinhMiddleOneRightA])
    (by norm_num [Certificate.sinhMiddleOneRightB])
    (by norm_num [Certificate.sinhMiddleOneRightA, Certificate.sinhMiddleOneRight])
    (by norm_num [Certificate.sinhMiddleOneRightA, Certificate.sinhMiddleOneRightB])
    (by norm_num [Certificate.sinhMiddleOneRightB, Certificate.sinhMiddleOneRight]) isOpen_Ioi
    (by
      intro x hx
      norm_num [Certificate.sinhMiddleOneRight] at hx ⊢
      linarith)
    hc2open
    (by
      intro x hx
      change |iteratedDeriv 2 stableSinhFunction x| ≤ ((1 : ℚ) : ℝ)
      exact stableSinhSecond_middleOne_bound x (by
          norm_num [Certificate.sinhMiddleOneRight, Certificate.sinhMiddleOne] at hx ⊢
          constructor <;> linarith [hx.1, hx.2]))
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.quadrature20Depth10])
    (by exact Certificate.sinhMiddleOneRightAQuadrature)
    (by exact Certificate.sinhMiddleOneRightBQuadrature)
  convert hraw using 1 <;>
    norm_num [Certificate.sinhMiddleOneRight, stableSinhFunction]

end
end TraceEuclidean.OdlyzkoNumerical
