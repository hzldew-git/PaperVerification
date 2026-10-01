import TraceEuclidean.OdlyzkoExplicitFormulaReduction
import TraceEuclidean.OdlyzkoNumericalCertLowRange
import TraceEuclidean.OdlyzkoNumericalCertLowSinhQuad
import TraceEuclidean.OdlyzkoNumericalPieceCertificates
import TraceEuclidean.OdlyzkoNumericalPieceRanges
import LeanCert.Validity.IntegrationDyadic
import LeanCert.Examples.EulerMascheroniLowerBounds
import LeanCert.Validity.Dyadic
import LeanCert.Validity.RangeDyadic
import LeanCert.Validity.TrapezoidalDyadic
import LeanCert.Core.ExprDerivative
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Certified numerical bounds for Odlyzko's `b = 4` kernel

The finite interval bounds below are checked using LeanCert's dyadic interval
integrator. The origin and infinite tails are bounded analytically in
`OdlyzkoExplicitFormulaReduction`.
-/

namespace TraceEuclidean.OdlyzkoNumerical

open MeasureTheory LeanCert.Core LeanCert.Engine
open LeanCert.Validity.IntegrationDyadic
open LeanCert.Validity.RangeDyadic
open LeanCert.Validity.TrapezoidalDyadic

-- The analytic bridge proofs exceed the default elaboration budget.
set_option maxHeartbeats 0

def q (r : ℚ) : Expr := .const r
def xExpr : Expr := .var 0
def pi : Expr := .namedConst .pi
def t : Expr := .div xExpr (q 4)
def angle : Expr := .mul pi t
def h : Expr :=
  .add
    (.div (.mul (.add (q 2) (.neg t))
      (.add (q 1) (.div (.cos angle) (q 2)))) (q 3))
    (.div (.sin angle) (.mul (q 2) pi))
def numerator : Expr := .add (.cosh (.div xExpr (q 2))) (.neg h)
def sinhIntegrand : Expr := .div numerator (.sinh xExpr)
def coshIntegrand : Expr := .div numerator (.add (q 1) (.cosh xExpr))

/-- Cancellation-free form of `cosh (x/2) - H(x/4)`. -/
def stableNumerator : Expr :=
  .add
    (.mul (q 2) (.mul (.sinh (.div xExpr (q 4))) (.sinh (.div xExpr (q 4)))))
    (.add
      (.div (.mul (.add (q 2) (.neg t))
        (.add (q 1) (.neg (.cos angle)))) (q 6))
      (.div (.add angle (.neg (.sin angle))) (.mul (q 2) pi)))

def stableSinhDenominator : Expr := .sinh xExpr
def stableCoshDenominator : Expr := .add (q 1) (.cosh xExpr)
def stableSinhIntegrand : Expr :=
  .div stableNumerator stableSinhDenominator
def stableCoshIntegrand : Expr :=
  .div stableNumerator stableCoshDenominator

noncomputable def stableSinhFunction (x : ℝ) : ℝ :=
  Expr.eval (fun _ ↦ x) stableSinhIntegrand

noncomputable def stableCoshFunction (x : ℝ) : ℝ :=
  Expr.eval (fun _ ↦ x) stableCoshIntegrand

def stableSinhSecond : Expr :=
  Expr.quotientSecond stableNumerator stableSinhDenominator
def stableCoshSecond : Expr :=
  Expr.quotientSecond stableNumerator stableCoshDenominator

/-- On `[4, 8]`, separate the dominant reciprocal hyperbolic term from the
compactly supported correction.  This avoids interval cancellation. -/
def halfX : Expr := .div xExpr (q 2)
def farSinhFirstDenominator : Expr := .mul (q 2) (.sinh halfX)
def farCoshFirstDenominator : Expr := .mul (q 2) (.cosh halfX)
def farSinhIntegrand : Expr :=
  .add (.div (q 1) farSinhFirstDenominator)
    (.neg (.div h stableSinhDenominator))
def farCoshIntegrand : Expr :=
  .add (.div (q 1) farCoshFirstDenominator)
    (.neg (.div h stableCoshDenominator))
def farSinhSecond : Expr :=
  .add (Expr.quotientSecond (q 1) farSinhFirstDenominator)
    (.neg (Expr.quotientSecond h stableSinhDenominator))
def farCoshSecond : Expr :=
  .add (Expr.quotientSecond (q 1) farCoshFirstDenominator)
    (.neg (Expr.quotientSecond h stableCoshDenominator))

noncomputable def farSinhFunction (x : ℝ) : ℝ :=
  Expr.eval (fun _ ↦ x) farSinhIntegrand

noncomputable def farCoshFunction (x : ℝ) : ℝ :=
  Expr.eval (fun _ ↦ x) farCoshIntegrand

def sinhCoreLow : IntervalRat := ⟨1 / 5, 1 / 2, by norm_num⟩
def rangeConfig : DyadicConfig := { precision := -16, taylorDepth := 4 }
def lowQuadratureConfig : DyadicConfig := { precision := -21, taylorDepth := 10 }

set_option maxRecDepth 1000000

noncomputable section

theorem eval_h (x : ℝ) :
    Expr.eval (fun _ ↦ x) h = odlyzkoHCore (x / 4) := by
  simp [h, q, t, angle, pi, xExpr, Expr.eval, Expr.div,
    MathConst.toReal, odlyzkoHCore]
  ring

theorem eval_stableNumerator (x : ℝ) :
    Expr.eval (fun _ ↦ x) stableNumerator =
      Real.cosh (x / 2) - odlyzkoHCore (x / 4) := by
  have hcosh : 2 * Real.sinh (x / 4) ^ 2 = Real.cosh (x / 2) - 1 := by
    rw [show x / 2 = 2 * (x / 4) by ring, Real.cosh_two_mul,
      Real.cosh_sq]
    ring
  simp [stableNumerator, q, t, angle, pi, xExpr, Expr.div,
    Expr.eval, MathConst.toReal]
  rw [show x * (4 : ℝ)⁻¹ = x / 4 by ring]
  rw [show 2 * (Real.sinh (x / 4) * Real.sinh (x / 4)) =
    2 * Real.sinh (x / 4) ^ 2 by ring, hcosh]
  unfold odlyzkoHCore
  field_simp [Real.pi_ne_zero]
  ring

theorem stableSinh_diffSupported : Expr.DiffSupported stableSinhIntegrand := by
  simp only [stableSinhIntegrand, stableSinhDenominator, stableNumerator, q, t, angle,
    pi, xExpr, Expr.div]
  aesop

theorem stableCosh_diffSupported : Expr.DiffSupported stableCoshIntegrand := by
  simp only [stableCoshIntegrand, stableCoshDenominator, stableNumerator, q, t, angle,
    pi, xExpr, Expr.div]
  aesop

theorem farSinh_diffSupported : Expr.DiffSupported farSinhIntegrand := by
  simp only [farSinhIntegrand, farSinhFirstDenominator, stableSinhDenominator, halfX,
    h, q, t, angle, pi, xExpr, Expr.div]
  aesop

theorem farCosh_diffSupported : Expr.DiffSupported farCoshIntegrand := by
  simp only [farCoshIntegrand, farCoshFirstDenominator, stableCoshDenominator, halfX,
    h, q, t, angle, pi, xExpr, Expr.div]
  aesop

theorem stableSinh_regular {x : ℝ} (hx : 0 < x) :
    Expr.RegularAt stableSinhIntegrand x := by
  have hsinh : Real.sinh x ≠ 0 := (Real.sinh_pos_iff.mpr hx).ne'
  have hpi : MathConst.pi.toReal ≠ 0 := by
    change Real.pi ≠ 0
    exact Real.pi_ne_zero
  simp [stableSinhIntegrand, stableSinhDenominator, stableNumerator, q, t, angle, pi, xExpr,
    Expr.div, Expr.RegularAt, Expr.eval, hsinh, hpi]

theorem stableCosh_regular (x : ℝ) :
    Expr.RegularAt stableCoshIntegrand x := by
  have hcosh : 0 < 1 + Real.cosh x := by positivity
  have hpi : MathConst.pi.toReal ≠ 0 := by
    change Real.pi ≠ 0
    exact Real.pi_ne_zero
  simp [stableCoshIntegrand, stableCoshDenominator, stableNumerator, q, t, angle, pi, xExpr,
    Expr.div, Expr.RegularAt, Expr.eval, hpi, hcosh.ne']

theorem farSinh_regular {x : ℝ} (hx : 0 < x) :
    Expr.RegularAt farSinhIntegrand x := by
  have hsinh : Real.sinh x ≠ 0 := (Real.sinh_pos_iff.mpr hx).ne'
  have hsinhHalf : Real.sinh (x / 2) ≠ 0 := by
    exact (Real.sinh_pos_iff.mpr (by positivity)).ne'
  have hpi : MathConst.pi.toReal ≠ 0 := by
    change Real.pi ≠ 0
    exact Real.pi_ne_zero
  simp [farSinhIntegrand, farSinhFirstDenominator, stableSinhDenominator, halfX,
    h, q, t, angle, pi, xExpr, Expr.div, Expr.RegularAt, Expr.eval,
    hsinh, hsinhHalf, hpi, hx.ne']

theorem farCosh_regular (x : ℝ) : Expr.RegularAt farCoshIntegrand x := by
  have hcoshHalf : Real.cosh (x * (2 : ℝ)⁻¹) ≠ 0 := (Real.cosh_pos _).ne'
  have hcosh : 0 < 1 + Real.cosh x := by positivity
  have hpi : MathConst.pi.toReal ≠ 0 := by
    change Real.pi ≠ 0
    exact Real.pi_ne_zero
  simp [farCoshIntegrand, farCoshFirstDenominator, stableCoshDenominator, halfX,
    h, q, t, angle, pi, xExpr, Expr.div, Expr.RegularAt, Expr.eval,
    hcoshHalf, hcosh.ne', hpi]

theorem eval_stableSinhIntegrand (x : ℝ) (hx0 : 0 < x) (hx8 : x ≤ 8) :
    Expr.eval (fun _ ↦ x) stableSinhIntegrand =
      (1 - odlyzkoF4 x) / (2 * Real.sinh (x / 2)) := by
  have ht0 : 0 ≤ x / 4 := by positivity
  have ht2 : x / 4 ≤ 2 := by linarith
  have hH : odlyzkoH (x / 4) = odlyzkoHCore (x / 4) := by
    simp [odlyzkoH, abs_of_nonneg ht0, ht2]
  rw [odlyzkoSinhIntegrand_eq x hx0, hH]
  simp only [stableSinhIntegrand, stableSinhDenominator, Expr.div, Expr.eval_mul, Expr.eval_inv,
    Expr.eval_sinh, Expr.eval_var, xExpr, eval_stableNumerator]
  rfl

theorem eval_stableCoshIntegrand (x : ℝ) (hx0 : 0 ≤ x) (hx8 : x ≤ 8) :
    Expr.eval (fun _ ↦ x) stableCoshIntegrand =
      (1 - odlyzkoF4 x) / (2 * Real.cosh (x / 2)) := by
  have ht0 : 0 ≤ x / 4 := by positivity
  have ht2 : x / 4 ≤ 2 := by linarith
  have hH : odlyzkoH (x / 4) = odlyzkoHCore (x / 4) := by
    simp [odlyzkoH, abs_of_nonneg ht0, ht2]
  rw [odlyzkoCoshIntegrand_eq x, hH]
  simp only [stableCoshIntegrand, stableCoshDenominator, Expr.div, Expr.eval_mul, Expr.eval_inv,
    Expr.eval_add, Expr.eval_const, Expr.eval_cosh, Expr.eval_var, xExpr,
    eval_stableNumerator]
  simp [q, div_eq_mul_inv]

theorem eval_farSinhIntegrand (x : ℝ) (hx0 : 0 < x) (hx8 : x ≤ 8) :
    Expr.eval (fun _ ↦ x) farSinhIntegrand =
      (1 - odlyzkoF4 x) / (2 * Real.sinh (x / 2)) := by
  have ht0 : 0 ≤ x / 4 := by positivity
  have ht2 : x / 4 ≤ 2 := by linarith
  have hH : odlyzkoH (x / 4) = odlyzkoHCore (x / 4) := by
    simp [odlyzkoH, abs_of_nonneg ht0, ht2]
  have hsinhHalf : Real.sinh (x / 2) ≠ 0 := by positivity
  have hsinh : Real.sinh x ≠ 0 := by positivity
  have hsinhDouble : Real.sinh x =
      2 * Real.sinh (x / 2) * Real.cosh (x / 2) := by
    calc
      Real.sinh x = Real.sinh (2 * (x / 2)) := by congr 1 <;> ring
      _ = 2 * Real.sinh (x / 2) * Real.cosh (x / 2) := Real.sinh_two_mul _
  rw [odlyzkoSinhIntegrand_eq x hx0, hH]
  simp [farSinhIntegrand, farSinhFirstDenominator, stableSinhDenominator,
    halfX, q, xExpr, Expr.div, Expr.eval, eval_h]
  rw [hsinhDouble]
  field_simp
  ring

theorem eval_farCoshIntegrand (x : ℝ) (hx0 : 0 ≤ x) (hx8 : x ≤ 8) :
    Expr.eval (fun _ ↦ x) farCoshIntegrand =
      (1 - odlyzkoF4 x) / (2 * Real.cosh (x / 2)) := by
  have ht0 : 0 ≤ x / 4 := by positivity
  have ht2 : x / 4 ≤ 2 := by linarith
  have hH : odlyzkoH (x / 4) = odlyzkoHCore (x / 4) := by
    simp [odlyzkoH, abs_of_nonneg ht0, ht2]
  have hcoshHalf : Real.cosh (x / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have hden : 1 + Real.cosh x =
      2 * Real.cosh (x / 2) * Real.cosh (x / 2) := by
    calc
      1 + Real.cosh x = 1 + Real.cosh (2 * (x / 2)) := by congr 2 <;> ring
      _ = 1 + (Real.cosh (x / 2) ^ 2 + Real.sinh (x / 2) ^ 2) := by
        rw [Real.cosh_two_mul]
      _ = 2 * Real.cosh (x / 2) * Real.cosh (x / 2) := by
        nlinarith [Real.cosh_sq_sub_sinh_sq (x / 2)]
  rw [odlyzkoCoshIntegrand_eq x, hH]
  simp [farCoshIntegrand, farCoshFirstDenominator, stableCoshDenominator,
    halfX, q, xExpr, Expr.div, Expr.eval, eval_h]
  rw [hden]
  field_simp
  ring

theorem eval_stableSinhSecond_eq (x : ℝ) (hx : 0 < x) :
    Expr.eval (fun _ ↦ x)
        (Expr.formalDeriv (Expr.formalDeriv stableSinhIntegrand)) =
      Expr.eval (fun _ ↦ x) stableSinhSecond := by
  have hd : Expr.eval (fun _ ↦ x) stableSinhDenominator ≠ 0 := by
    simp [stableSinhDenominator, xExpr, Real.sinh_ne_zero, hx.ne']
  simpa only [stableSinhIntegrand, stableSinhSecond] using
    Expr.eval_formalDeriv_two_div_eq_quotientSecond
      stableNumerator stableSinhDenominator x hd

theorem eval_stableCoshSecond_eq (x : ℝ) :
    Expr.eval (fun _ ↦ x)
        (Expr.formalDeriv (Expr.formalDeriv stableCoshIntegrand)) =
      Expr.eval (fun _ ↦ x) stableCoshSecond := by
  have hd : Expr.eval (fun _ ↦ x) stableCoshDenominator ≠ 0 := by
    have hpos : 0 < 1 + Real.cosh x := by positivity
    simpa [stableCoshDenominator, q, xExpr, Expr.eval] using hpos.ne'
  simpa only [stableCoshIntegrand, stableCoshSecond] using
    Expr.eval_formalDeriv_two_div_eq_quotientSecond
      stableNumerator stableCoshDenominator x hd

theorem eval_farSinhSecond_eq (x : ℝ) (hx : 0 < x) :
    Expr.eval (fun _ ↦ x)
        (Expr.formalDeriv (Expr.formalDeriv farSinhIntegrand)) =
      Expr.eval (fun _ ↦ x) farSinhSecond := by
  have hd1 : Expr.eval (fun _ ↦ x) farSinhFirstDenominator ≠ 0 := by
    simp [farSinhFirstDenominator, halfX, q, xExpr, Expr.eval]
    exact hx.ne'
  have hd2 : Expr.eval (fun _ ↦ x) stableSinhDenominator ≠ 0 := by
    simp [stableSinhDenominator, xExpr, Expr.eval]
    positivity
  calc
    Expr.eval (fun _ ↦ x)
        (Expr.formalDeriv (Expr.formalDeriv farSinhIntegrand)) =
        Expr.eval (fun _ ↦ x)
            (Expr.formalDeriv (Expr.formalDeriv (.div (q 1) farSinhFirstDenominator))) -
          Expr.eval (fun _ ↦ x)
            (Expr.formalDeriv (Expr.formalDeriv (.div h stableSinhDenominator))) := by
              rfl
    _ = Expr.eval (fun _ ↦ x)
          (Expr.quotientSecond (q 1) farSinhFirstDenominator) -
        Expr.eval (fun _ ↦ x)
          (Expr.quotientSecond h stableSinhDenominator) := by
            rw [Expr.eval_formalDeriv_two_div_eq_quotientSecond _ _ x hd1,
              Expr.eval_formalDeriv_two_div_eq_quotientSecond _ _ x hd2]
    _ = Expr.eval (fun _ ↦ x) farSinhSecond := by rfl

theorem eval_farCoshSecond_eq (x : ℝ) :
    Expr.eval (fun _ ↦ x)
        (Expr.formalDeriv (Expr.formalDeriv farCoshIntegrand)) =
      Expr.eval (fun _ ↦ x) farCoshSecond := by
  have hd1 : Expr.eval (fun _ ↦ x) farCoshFirstDenominator ≠ 0 := by
    simp [farCoshFirstDenominator, halfX, q, xExpr, Expr.eval]
    positivity
  have hd2 : Expr.eval (fun _ ↦ x) stableCoshDenominator ≠ 0 := by
    have hpos : 0 < 1 + Real.cosh x := by positivity
    simpa [stableCoshDenominator, q, xExpr, Expr.eval] using hpos.ne'
  calc
    Expr.eval (fun _ ↦ x)
        (Expr.formalDeriv (Expr.formalDeriv farCoshIntegrand)) =
        Expr.eval (fun _ ↦ x)
            (Expr.formalDeriv (Expr.formalDeriv (.div (q 1) farCoshFirstDenominator))) -
          Expr.eval (fun _ ↦ x)
            (Expr.formalDeriv (Expr.formalDeriv (.div h stableCoshDenominator))) := by
              rfl
    _ = Expr.eval (fun _ ↦ x)
          (Expr.quotientSecond (q 1) farCoshFirstDenominator) -
        Expr.eval (fun _ ↦ x)
          (Expr.quotientSecond h stableCoshDenominator) := by
            rw [Expr.eval_formalDeriv_two_div_eq_quotientSecond _ _ x hd1,
              Expr.eval_formalDeriv_two_div_eq_quotientSecond _ _ x hd2]
    _ = Expr.eval (fun _ ↦ x) farCoshSecond := by rfl

theorem eval_sinhIntegrand (x : ℝ) (hx0 : 0 ≤ x) (hx8 : x ≤ 8) :
    Expr.eval (fun _ ↦ x) sinhIntegrand =
      (1 - odlyzkoF4 x) / (2 * Real.sinh (x / 2)) := by
  have ht0 : 0 ≤ x / 4 := by positivity
  have ht2 : x / 4 ≤ 2 := by linarith
  have hH : odlyzkoH (x / 4) = odlyzkoHCore (x / 4) := by
    simp [odlyzkoH, abs_of_nonneg ht0, ht2]
  by_cases hx : x = 0
  · subst x
    simp [sinhIntegrand, numerator, eval_h, Expr.eval, Expr.div,
      xExpr, q, odlyzkoHCore, odlyzkoF4_zero]
  have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
  rw [odlyzkoSinhIntegrand_eq x hxpos, hH]
  simp [sinhIntegrand, numerator, eval_h, Expr.eval, Expr.div,
    xExpr, q, div_eq_mul_inv, sub_eq_add_neg]

theorem eval_coshIntegrand (x : ℝ) (hx0 : 0 ≤ x) (hx8 : x ≤ 8) :
    Expr.eval (fun _ ↦ x) coshIntegrand =
      (1 - odlyzkoF4 x) / (2 * Real.cosh (x / 2)) := by
  have ht0 : 0 ≤ x / 4 := by positivity
  have ht2 : x / 4 ≤ 2 := by linarith
  have hH : odlyzkoH (x / 4) = odlyzkoHCore (x / 4) := by
    simp [odlyzkoH, abs_of_nonneg ht0, ht2]
  rw [odlyzkoCoshIntegrand_eq x, hH]
  simp [coshIntegrand, numerator, eval_h, Expr.eval, Expr.div,
    xExpr, q, div_eq_mul_inv, sub_eq_add_neg]

theorem stableSinhSecond_low_bound (x : ℝ)
    (hx : x ∈ Set.Icc (1 / 5 : ℝ) (1 / 2)) :
    |iteratedDeriv 2 stableSinhFunction x| ≤ 2 := by
  change |iteratedDeriv 2 (fun y => Expr.eval (fun _ ↦ y) stableSinhIntegrand) x| ≤ 2
  have hcheck : checkRangeDyadicListFull stableSinhSecond
      (uniformPartition sinhCoreLow 16 (by norm_num)) sinhCoreLow
      (-2) 2 rangeConfig = true := by
    exact Certificate.lowSinhRange
  have hb := range_bounds_of_check_dyadic_list stableSinhSecond
    (uniformPartition sinhCoreLow 16 (by norm_num)) sinhCoreLow
    (-2) 2 rangeConfig (by norm_num [rangeConfig]) hcheck x
    (by simpa [sinhCoreLow] using hx)
  rw [Expr.iteratedDeriv_two_eval_eq stableSinh_diffSupported isOpen_Ioi
    (show x ∈ Set.Ioi (0 : ℝ) by exact lt_of_lt_of_le (by norm_num) hx.1)
    (fun y hy ↦ stableSinh_regular hy)]
  rw [eval_stableSinhSecond_eq x (lt_of_lt_of_le (by norm_num) hx.1)]
  rw [abs_le]
  norm_num at hb ⊢
  exact hb

theorem iteratedDerivWithin_two_abs_le_of_open {f : ℝ → ℝ}
    {a b M : ℝ} (hab : a < b) {s : Set ℝ} (hs : IsOpen s)
    (hsub : Set.Icc a b ⊆ s) (hf : ContDiffOn ℝ 2 f s)
    (hbound : ∀ x ∈ Set.Icc a b, |iteratedDeriv 2 f x| ≤ M)
    (hM : 0 ≤ M) :
    ∀ x, |iteratedDerivWithin 2 f (Set.Icc a b) x| ≤ M := by
  intro x
  by_cases hx : x ∈ Set.Icc a b
  · rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) ?_ hx]
    · exact hbound x hx
    · exact (hf x (hsub hx)).contDiffAt (hs.mem_nhds (hsub hx))
  · have hxclosure : x ∉ closure (Set.Icc a b) := by
      simpa only [closure_Icc] using hx
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDerivWithin_succ,
      derivWithin_zero_of_notMem_closure hxclosure, abs_zero]
    exact hM

theorem expr_integral_le_of_trapezoidal_check
    (e : Expr) (I : IntervalRat) (N : ℕ) (M target : ℚ) (cfg : DyadicConfig)
    (hN : 0 < N)
    (hc2 : ContDiffOn ℝ 2 (fun x : ℝ ↦ Expr.eval (fun _ ↦ x) e)
      (Set.uIcc (I.lo : ℝ) (I.hi : ℝ)))
    (hsecond : ∀ x,
      |iteratedDerivWithin 2 (fun y : ℝ ↦ Expr.eval (fun _ ↦ y) e)
        (Set.uIcc (I.lo : ℝ) (I.hi : ℝ)) x| ≤ (M : ℝ))
    (hprec : cfg.precision ≤ 0)
    (hcheck : checkTrapezoidalUpperDyadicFull e I N M target cfg = true) :
    (∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ ↦ x) e) ≤ (target : ℝ) := by
  have herr := trapezoidal_error_le_of_c2 hc2 hsecond hN
  have hcert := trapezoidal_integral_add_error_le_of_check
    e I N hN M target cfg hprec hcheck
  have hdiff : 0 ≤ (I.hi : ℝ) - I.lo := by
    exact sub_nonneg.mpr (by exact_mod_cast I.le)
  have hwidth : |(I.hi : ℝ) - I.lo| = (I.width : ℝ) := by
    rw [abs_of_nonneg hdiff]
    norm_num [IntervalRat.width]
  unfold trapezoidal_error at herr
  rw [hwidth] at herr
  have herrLower := (abs_le.mp herr).1
  linarith

theorem stableSinhSecond_bound_of_list
    (I : IntervalRat) (cells : List IntervalRat) (lower upper M : ℚ)
    (cfg : DyadicConfig) (hlo : -M ≤ lower) (hhi : upper ≤ M)
    (hpos : 0 < I.lo) (hprec : cfg.precision ≤ 0)
    (hcheck : checkRangeDyadicListFull stableSinhSecond cells I lower upper cfg = true)
    (x : ℝ) (hx : x ∈ Set.Icc (I.lo : ℝ) I.hi) :
    |iteratedDeriv 2 stableSinhFunction x| ≤ (M : ℝ) := by
  change |iteratedDeriv 2 (fun y ↦ Expr.eval (fun _ ↦ y) stableSinhIntegrand) x| ≤
    (M : ℝ)
  have hb := range_bounds_of_check_dyadic_list stableSinhSecond
    cells I lower upper cfg hprec hcheck x hx
  rw [Expr.iteratedDeriv_two_eval_eq stableSinh_diffSupported isOpen_Ioi
    (show x ∈ Set.Ioi (0 : ℝ) by exact lt_of_lt_of_le (by exact_mod_cast hpos) hx.1)
    (fun y hy ↦ stableSinh_regular hy)]
  rw [eval_stableSinhSecond_eq x
    (lt_of_lt_of_le (by exact_mod_cast hpos) hx.1), abs_le]
  have hloReal : -(M : ℝ) ≤ (lower : ℝ) := by exact_mod_cast hlo
  have hhiReal : (upper : ℝ) ≤ (M : ℝ) := by exact_mod_cast hhi
  constructor
  · exact hloReal.trans hb.1
  · exact hb.2.trans hhiReal

theorem stableSinhSecond_bound_of_range
    (I : IntervalRat) (parts : ℕ) (M : ℚ) (cfg : DyadicConfig)
    (hparts : 0 < parts) (hpos : 0 < I.lo) (hprec : cfg.precision ≤ 0)
    (hcheck : checkRangeDyadicListFull stableSinhSecond
      (uniformPartition I parts hparts) I (-M) M cfg = true)
    (x : ℝ) (hx : x ∈ Set.Icc (I.lo : ℝ) I.hi) :
    |iteratedDeriv 2 stableSinhFunction x| ≤ (M : ℝ) :=
  stableSinhSecond_bound_of_list I (uniformPartition I parts hparts) (-M) M M cfg
    le_rfl le_rfl hpos hprec hcheck x hx

theorem farSinhSecond_bound_of_list
    (I : IntervalRat) (cells : List IntervalRat) (lower upper M : ℚ)
    (cfg : DyadicConfig) (hlo : -M ≤ lower) (hhi : upper ≤ M)
    (hpos : 0 < I.lo) (hprec : cfg.precision ≤ 0)
    (hcheck : checkRangeDyadicListFull farSinhSecond cells I lower upper cfg = true)
    (x : ℝ) (hx : x ∈ Set.Icc (I.lo : ℝ) I.hi) :
    |iteratedDeriv 2 farSinhFunction x| ≤ (M : ℝ) := by
  change |iteratedDeriv 2 (fun y ↦ Expr.eval (fun _ ↦ y) farSinhIntegrand) x| ≤ (M : ℝ)
  have hb := range_bounds_of_check_dyadic_list farSinhSecond
    cells I lower upper cfg hprec hcheck x hx
  rw [Expr.iteratedDeriv_two_eval_eq farSinh_diffSupported isOpen_Ioi
    (show x ∈ Set.Ioi (0 : ℝ) by exact lt_of_lt_of_le (by exact_mod_cast hpos) hx.1)
    (fun y hy ↦ farSinh_regular hy)]
  rw [eval_farSinhSecond_eq x
    (lt_of_lt_of_le (by exact_mod_cast hpos) hx.1), abs_le]
  have hloReal : -(M : ℝ) ≤ (lower : ℝ) := by exact_mod_cast hlo
  have hhiReal : (upper : ℝ) ≤ (M : ℝ) := by exact_mod_cast hhi
  constructor
  · exact hloReal.trans hb.1
  · exact hb.2.trans hhiReal

theorem farSinhSecond_bound_of_range
    (I : IntervalRat) (parts : ℕ) (M : ℚ) (cfg : DyadicConfig)
    (hparts : 0 < parts) (hpos : 0 < I.lo) (hprec : cfg.precision ≤ 0)
    (hcheck : checkRangeDyadicListFull farSinhSecond
      (uniformPartition I parts hparts) I (-M) M cfg = true)
    (x : ℝ) (hx : x ∈ Set.Icc (I.lo : ℝ) I.hi) :
    |iteratedDeriv 2 farSinhFunction x| ≤ (M : ℝ) :=
  farSinhSecond_bound_of_list I (uniformPartition I parts hparts) (-M) M M cfg
    le_rfl le_rfl hpos hprec hcheck x hx

theorem stableCoshSecond_bound_of_list
    (I : IntervalRat) (cells : List IntervalRat) (lower upper M : ℚ)
    (cfg : DyadicConfig) (hlo : -M ≤ lower) (hhi : upper ≤ M)
    (hprec : cfg.precision ≤ 0)
    (hcheck : checkRangeDyadicListFull stableCoshSecond cells I lower upper cfg = true)
    (x : ℝ) (hx : x ∈ Set.Icc (I.lo : ℝ) I.hi) :
    |iteratedDeriv 2 stableCoshFunction x| ≤ (M : ℝ) := by
  change |iteratedDeriv 2 (fun y ↦ Expr.eval (fun _ ↦ y) stableCoshIntegrand) x| ≤
    (M : ℝ)
  have hb := range_bounds_of_check_dyadic_list stableCoshSecond
    cells I lower upper cfg hprec hcheck x hx
  rw [Expr.iteratedDeriv_two_eval_eq stableCosh_diffSupported isOpen_univ
    (Set.mem_univ x) (fun y _ ↦ stableCosh_regular y)]
  rw [eval_stableCoshSecond_eq x, abs_le]
  have hloReal : -(M : ℝ) ≤ (lower : ℝ) := by exact_mod_cast hlo
  have hhiReal : (upper : ℝ) ≤ (M : ℝ) := by exact_mod_cast hhi
  constructor
  · exact hloReal.trans hb.1
  · exact hb.2.trans hhiReal

theorem stableCoshSecond_bound_of_range
    (I : IntervalRat) (parts : ℕ) (M : ℚ) (cfg : DyadicConfig)
    (hparts : 0 < parts) (hprec : cfg.precision ≤ 0)
    (hcheck : checkRangeDyadicListFull stableCoshSecond
      (uniformPartition I parts hparts) I (-M) M cfg = true)
    (x : ℝ) (hx : x ∈ Set.Icc (I.lo : ℝ) I.hi) :
    |iteratedDeriv 2 stableCoshFunction x| ≤ (M : ℝ) :=
  stableCoshSecond_bound_of_list I (uniformPartition I parts hparts) (-M) M M cfg
    le_rfl le_rfl hprec hcheck x hx

theorem farCoshSecond_bound_of_list
    (I : IntervalRat) (cells : List IntervalRat) (lower upper M : ℚ)
    (cfg : DyadicConfig) (hlo : -M ≤ lower) (hhi : upper ≤ M)
    (hprec : cfg.precision ≤ 0)
    (hcheck : checkRangeDyadicListFull farCoshSecond cells I lower upper cfg = true)
    (x : ℝ) (hx : x ∈ Set.Icc (I.lo : ℝ) I.hi) :
    |iteratedDeriv 2 farCoshFunction x| ≤ (M : ℝ) := by
  change |iteratedDeriv 2 (fun y ↦ Expr.eval (fun _ ↦ y) farCoshIntegrand) x| ≤ (M : ℝ)
  have hb := range_bounds_of_check_dyadic_list farCoshSecond
    cells I lower upper cfg hprec hcheck x hx
  rw [Expr.iteratedDeriv_two_eval_eq farCosh_diffSupported isOpen_univ
    (Set.mem_univ x) (fun y _ ↦ farCosh_regular y)]
  rw [eval_farCoshSecond_eq x, abs_le]
  have hloReal : -(M : ℝ) ≤ (lower : ℝ) := by exact_mod_cast hlo
  have hhiReal : (upper : ℝ) ≤ (M : ℝ) := by exact_mod_cast hhi
  constructor
  · exact hloReal.trans hb.1
  · exact hb.2.trans hhiReal

theorem farCoshSecond_bound_of_range
    (I : IntervalRat) (parts : ℕ) (M : ℚ) (cfg : DyadicConfig)
    (hparts : 0 < parts) (hprec : cfg.precision ≤ 0)
    (hcheck : checkRangeDyadicListFull farCoshSecond
      (uniformPartition I parts hparts) I (-M) M cfg = true)
    (x : ℝ) (hx : x ∈ Set.Icc (I.lo : ℝ) I.hi) :
    |iteratedDeriv 2 farCoshFunction x| ≤ (M : ℝ) :=
  farCoshSecond_bound_of_list I (uniformPartition I parts hparts) (-M) M M cfg
    le_rfl le_rfl hprec hcheck x hx

theorem expr_piece_upper_of_open
    (e : Expr) (I : IntervalRat) (N : ℕ) (M target : ℚ) (cfg : DyadicConfig)
    (s : Set ℝ) (hlt : I.lo < I.hi) (hs : IsOpen s)
    (hsub : Set.Icc (I.lo : ℝ) I.hi ⊆ s)
    (hc2open : ContDiffOn ℝ 2 (fun x : ℝ ↦ Expr.eval (fun _ ↦ x) e) s)
    (hbound : ∀ x ∈ Set.Icc (I.lo : ℝ) I.hi,
      |iteratedDeriv 2 (fun y : ℝ ↦ Expr.eval (fun _ ↦ y) e) x| ≤ (M : ℝ))
    (hM : 0 ≤ M) (hN : 0 < N) (hprec : cfg.precision ≤ 0)
    (hcheck : checkTrapezoidalUpperDyadicFull e I N M target cfg = true) :
    (∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ ↦ x) e) ≤ (target : ℝ) := by
  have hltReal : (I.lo : ℝ) < I.hi := by exact_mod_cast hlt
  have hleReal : (I.lo : ℝ) ≤ I.hi := hltReal.le
  have hc2I : ContDiffOn ℝ 2 (fun x : ℝ ↦ Expr.eval (fun _ ↦ x) e)
      (Set.Icc (I.lo : ℝ) I.hi) := hc2open.mono hsub
  have hwithin := iteratedDerivWithin_two_abs_le_of_open
    (f := fun x : ℝ ↦ Expr.eval (fun _ ↦ x) e)
    (a := (I.lo : ℝ)) (b := (I.hi : ℝ)) (M := (M : ℝ))
    hltReal hs hsub hc2open hbound (by exact_mod_cast hM)
  have hc2u : ContDiffOn ℝ 2 (fun x : ℝ ↦ Expr.eval (fun _ ↦ x) e)
      (Set.uIcc (I.lo : ℝ) I.hi) := by
    rw [Set.uIcc_of_le hleReal]
    exact hc2I
  have hwithinu : ∀ x,
      |iteratedDerivWithin 2 (fun y : ℝ ↦ Expr.eval (fun _ ↦ y) e)
        (Set.uIcc (I.lo : ℝ) I.hi) x| ≤ (M : ℝ) := by
    rw [Set.uIcc_of_le hleReal]
    exact hwithin
  exact expr_integral_le_of_trapezoidal_check
    e I N M target cfg hN hc2u hwithinu hprec hcheck

/-- Combine two separately checked halves of one trapezoidal interval.  The
separate Boolean certificates keep kernel reduction small, while the analytic
proof below joins the two interval integrals. -/
theorem expr_bisected_piece_upper_of_open
    (e : Expr) (P L R : IntervalRat) (N : ℕ) (M targetL targetR : ℚ)
    (cfg : DyadicConfig) (s : Set ℝ)
    (hLlt : L.lo < L.hi) (hRlt : R.lo < R.hi)
    (hlo : L.lo = P.lo) (hmid : L.hi = R.lo) (hhi : R.hi = P.hi)
    (hs : IsOpen s) (hPsub : Set.Icc (P.lo : ℝ) P.hi ⊆ s)
    (hc2open : ContDiffOn ℝ 2 (fun x : ℝ ↦ Expr.eval (fun _ ↦ x) e) s)
    (hbound : ∀ x ∈ Set.Icc (P.lo : ℝ) P.hi,
      |iteratedDeriv 2 (fun y : ℝ ↦ Expr.eval (fun _ ↦ y) e) x| ≤ (M : ℝ))
    (hM : 0 ≤ M) (hN : 0 < N) (hprec : cfg.precision ≤ 0)
    (hcheckL : checkTrapezoidalUpperDyadicFull e L N M targetL cfg = true)
    (hcheckR : checkTrapezoidalUpperDyadicFull e R N M targetR cfg = true) :
    (∫ x in (P.lo : ℝ)..(P.hi : ℝ), Expr.eval (fun _ ↦ x) e) ≤
      ((targetL + targetR : ℚ) : ℝ) := by
  have hloReal : (L.lo : ℝ) = P.lo := by exact_mod_cast hlo
  have hmidReal : (L.hi : ℝ) = R.lo := by exact_mod_cast hmid
  have hhiReal : (R.hi : ℝ) = P.hi := by exact_mod_cast hhi
  have hLltReal : (L.lo : ℝ) < L.hi := by exact_mod_cast hLlt
  have hRltReal : (R.lo : ℝ) < R.hi := by exact_mod_cast hRlt
  have hLsub : Set.Icc (L.lo : ℝ) L.hi ⊆ Set.Icc (P.lo : ℝ) P.hi := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hRsub : Set.Icc (R.lo : ℝ) R.hi ⊆ Set.Icc (P.lo : ℝ) P.hi := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hleft := expr_piece_upper_of_open e L N M targetL cfg s hLlt hs
    (fun _ hx ↦ hPsub (hLsub hx)) hc2open
    (fun x hx ↦ hbound x (hLsub hx)) hM hN hprec hcheckL
  have hright := expr_piece_upper_of_open e R N M targetR cfg s hRlt hs
    (fun _ hx ↦ hPsub (hRsub hx)) hc2open
    (fun x hx ↦ hbound x (hRsub hx)) hM hN hprec hcheckR
  have hLle : (L.lo : ℝ) ≤ L.hi := by exact_mod_cast hLlt.le
  have hRle : (R.lo : ℝ) ≤ R.hi := by exact_mod_cast hRlt.le
  have hiL : IntervalIntegrable (fun x : ℝ ↦ Expr.eval (fun _ ↦ x) e)
      volume (L.lo : ℝ) L.hi := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hLle]
    exact hc2open.continuousOn.mono (fun _ hx ↦ hPsub (hLsub hx))
  have hiR : IntervalIntegrable (fun x : ℝ ↦ Expr.eval (fun _ ↦ x) e)
      volume (R.lo : ℝ) R.hi := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hRle]
    exact hc2open.continuousOn.mono (fun _ hx ↦ hPsub (hRsub hx))
  have hiR' : IntervalIntegrable (fun x : ℝ ↦ Expr.eval (fun _ ↦ x) e)
      volume (L.hi : ℝ) R.hi := by
    simpa [hmidReal] using hiR
  have hright' :
      (∫ x in (L.hi : ℝ)..(R.hi : ℝ), Expr.eval (fun _ ↦ x) e) ≤
        (targetR : ℝ) := by
    simpa [hmidReal] using hright
  rw [← hloReal, ← hhiReal,
    ← intervalIntegral.integral_add_adjacent_intervals hiL hiR']
  norm_num at hleft hright' ⊢
  linarith


end
end TraceEuclidean.OdlyzkoNumerical
