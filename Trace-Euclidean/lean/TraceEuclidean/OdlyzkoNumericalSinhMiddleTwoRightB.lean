import TraceEuclidean.OdlyzkoNumericalSinhMiddleTwoDerivative

namespace TraceEuclidean.OdlyzkoNumerical

open MeasureTheory LeanCert.Core LeanCert.Engine
open LeanCert.Validity.IntegrationDyadic
open LeanCert.Validity.RangeDyadic
open LeanCert.Validity.TrapezoidalDyadic

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section

theorem sinh_middle_two_right_b_upper :
    (∫ x in (61 / 24 : ℝ)..(17 / 6 : ℝ), stableSinhFunction x) ≤ 63048188663 / 1000000000000 := by
  have hc2open : ContDiffOn ℝ 2 stableSinhFunction (Set.Ioi 0) := by
    change ContDiffOn ℝ 2 (fun x ↦ Expr.eval (fun _ ↦ x) stableSinhIntegrand) (Set.Ioi 0)
    exact Expr.contDiffOn_eval stableSinh_diffSupported 2
      (fun x hx ↦ stableSinh_regular hx)
  have hraw := expr_piece_upper_of_open
    (e := stableSinhIntegrand) (I := Certificate.sinhMiddleTwoRightB)
    (N := 24) (M := 1 / 2) (target := 63048188663 / 1000000000000)
    (cfg := Certificate.quadrature20Depth12) (s := Set.Ioi 0)
    (by norm_num [Certificate.sinhMiddleTwoRightB]) isOpen_Ioi
    (by
      intro x hx
      norm_num [Certificate.sinhMiddleTwoRightB] at hx ⊢
      linarith)
    hc2open
    (by
      intro x hx
      change |iteratedDeriv 2 stableSinhFunction x| ≤ ((1 / 2 : ℚ) : ℝ)
      exact stableSinhSecond_middleTwo_bound x (by
        norm_num [Certificate.sinhMiddleTwoRightB, Certificate.sinhMiddleTwo] at hx ⊢
        constructor <;> linarith [hx.1, hx.2]))
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.quadrature20Depth12])
    (by exact Certificate.sinhMiddleTwoRightBQuadrature)
  convert hraw using 1 <;>
    norm_num [Certificate.sinhMiddleTwoRightB, stableSinhFunction]

end
end TraceEuclidean.OdlyzkoNumerical
