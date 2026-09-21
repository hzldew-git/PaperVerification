import TraceEuclidean.V15AdmissibleTables
import TraceEuclidean.V15FinitenessAssembly
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Real.Pi.Bounds

/-!
The analytic quantity used for the finite rank--degree tables in Section 4 of
the frozen Trace-Euclidean v15 input.  This module turns the Gamma expression
into an exact factorial expression and then encloses it between rational
bounds.  The cited root-discriminant estimates remain external inputs; all
subsequent analytic and finite arithmetic is checked by Lean.
-/

namespace TraceEuclidean

noncomputable section

/-- The exact discriminant minima used in degrees `1, ..., 9`. -/
def v15MinimumDiscriminant : ℕ → ℕ
  | 1 => 1
  | 2 => 5
  | 3 => 49
  | 4 => 725
  | 5 => 14641
  | 6 => 300125
  | 7 => 20134393
  | 8 => 282300416
  | 9 => 9685993193
  | _ => 1

/-- The algebraic part of `β_d^(nd)`, before the exponential correction in
degrees at least twelve. -/
def v15AlgebraicBetaPower (n d : ℕ) : ℝ :=
  if d ≤ 9 then (v15MinimumDiscriminant d : ℝ) ^ n
  else if d = 10 then (14 : ℝ) ^ (n * d)
  else if d = 11 then (14083 / 1000 : ℝ) ^ (n * d)
  else (36347 / 1000 : ℝ) ^ (n * d)

/-- The exact power `β_d^(nd)` corresponding to the piecewise `β_d` in
Section 4. -/
def v15BetaPower (n d : ℕ) : ℝ :=
  if 12 ≤ d then
    v15AlgebraicBetaPower n d *
      Real.exp (-(10667 / 1000 : ℝ) * n)
  else v15AlgebraicBetaPower n d

/-- The manuscript's analytic quantity
`H(n,d) = (πd)^(nd) / (Γ(nd/2+1)^2 β_d^(nd))`. -/
def v15AnalyticH (n d : ℕ) : ℝ :=
  euclideanUnitBallVolume (n * d) ^ (2 : ℕ) *
    (d : ℝ) ^ (n * d) / v15BetaPower n d

/-- The exponent of `π` after evaluating the half-integral Gamma value. -/
def v15PiExponent (m : ℕ) : ℕ :=
  if Even m then m else m - 1

/-- The rational coefficient in the square of the unit-ball volume after
evaluating the Gamma value. -/
def v15UnitBallSquareCoefficient (m : ℕ) : ℝ :=
  if Even m then
    1 / ((m / 2).factorial : ℝ) ^ (2 : ℕ)
  else
    (2 : ℝ) ^ (2 * (m / 2 + 1)) /
      ((m.doubleFactorial : ℕ) : ℝ) ^ (2 : ℕ)

private theorem pi_rpow_half_sq (m : ℕ) :
    (Real.pi ^ ((m : ℝ) / 2)) ^ (2 : ℕ) = Real.pi ^ m := by
  calc
    (Real.pi ^ ((m : ℝ) / 2)) ^ (2 : ℕ) =
        (Real.pi ^ ((m : ℝ) / 2)) ^ (2 : ℝ) := by
          exact (Real.rpow_two _).symm
    _ = Real.pi ^ (((m : ℝ) / 2) * 2) := by
      rw [Real.rpow_mul Real.pi_pos.le]
    _ = Real.pi ^ (m : ℝ) := by congr 1 <;> ring
    _ = Real.pi ^ m := Real.rpow_natCast Real.pi m

/-- Exact evaluation of `U_m^2`; the odd-dimensional branch uses the
half-integral Gamma formula and the odd double factorial. -/
theorem v15_unitBallVolume_sq_closed (m : ℕ) :
    euclideanUnitBallVolume m ^ (2 : ℕ) =
      v15UnitBallSquareCoefficient m * Real.pi ^ v15PiExponent m := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · have harg : (((2 * k : ℕ) : ℝ) / 2 + 1) = (k : ℝ) + 1 := by
      push_cast
      ring
    have heven : Even (2 * k) := even_two_mul k
    have hdiv : (2 * k) / 2 = k := by omega
    have hfac : (k.factorial : ℝ) ≠ 0 := by positivity
    unfold euclideanUnitBallVolume v15UnitBallSquareCoefficient v15PiExponent
    simp only [heven, if_true]
    rw [hdiv]
    rw [harg, Real.Gamma_nat_eq_factorial, div_pow, pi_rpow_half_sq]
    field_simp
  · have hodd : ¬ Even (2 * k + 1) := k.not_even_two_mul_add_one
    have hdiv : (2 * k + 1) / 2 = k := by omega
    have hsub : 2 * k + 1 - 1 = 2 * k := by omega
    have harg : (((2 * k + 1 : ℕ) : ℝ) / 2 + 1) =
        (k : ℝ) + 1 + 1 / 2 := by
      push_cast
      ring
    have hdf : ((((2 * k + 1).doubleFactorial : ℕ) : ℝ)) ≠ 0 := by
      positivity
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hsqrt : Real.sqrt Real.pi ^ (2 : ℕ) = Real.pi := by
      exact Real.sq_sqrt Real.pi_pos.le
    unfold euclideanUnitBallVolume v15UnitBallSquareCoefficient v15PiExponent
    simp only [hodd, if_false]
    rw [hdiv, hsub]
    rw [harg, Real.Gamma_nat_add_one_add_half, div_pow, pi_rpow_half_sq,
      div_pow, mul_pow, hsqrt]
    field_simp
    have htwo : ((2 : ℝ) ^ (k + 1)) ^ 2 =
        ((2 : ℝ) ^ 2) ^ (k + 1) := by
      calc
        ((2 : ℝ) ^ (k + 1)) ^ 2 = 2 ^ ((k + 1) * 2) :=
          (pow_mul 2 (k + 1) 2).symm
        _ = 2 ^ (2 * (k + 1)) := by congr 1 <;> omega
        _ = ((2 : ℝ) ^ 2) ^ (k + 1) := pow_mul 2 2 (k + 1)
    have hpipow : Real.pi ^ (2 * k + 1) =
        Real.pi * Real.pi ^ (2 * k) := by
      rw [pow_succ]
      ring
    rw [htwo, hpipow]
    simp only [pow_mul]
    ring

/-- The exponential correction which occurs after expanding the Table 4
root-discriminant bound in degrees at least twelve. -/
def v15ExponentialCorrection (n d : ℕ) : ℝ :=
  if 12 ≤ d then Real.exp ((10667 / 1000 : ℝ) * n) else 1

/-- The factorial form of `v15AnalyticH`. -/
def v15ClosedH (n d : ℕ) : ℝ :=
  (v15UnitBallSquareCoefficient (n * d) * (d : ℝ) ^ (n * d) /
      v15AlgebraicBetaPower n d) *
    Real.pi ^ v15PiExponent (n * d) * v15ExponentialCorrection n d

theorem v15AlgebraicBetaPower_pos (n d : ℕ) :
    0 < v15AlgebraicBetaPower n d := by
  unfold v15AlgebraicBetaPower
  split_ifs with hd9 hd10 hd11
  · have hdisc : 0 < v15MinimumDiscriminant d := by
      interval_cases d <;> norm_num [v15MinimumDiscriminant]
    positivity
  all_goals positivity

/-- The Gamma definition of `H(n,d)` and its factorial form agree exactly. -/
theorem v15AnalyticH_eq_closed (n d : ℕ) :
    v15AnalyticH n d = v15ClosedH n d := by
  rw [v15AnalyticH, v15_unitBallVolume_sq_closed]
  unfold v15ClosedH v15BetaPower v15ExponentialCorrection
  by_cases hd : 12 ≤ d
  · simp only [hd, if_true]
    have hneg : -(10667 / 1000 : ℝ) * (n : ℝ) =
        -((10667 / 1000 : ℝ) * n) := by ring
    rw [hneg]
    rw [Real.exp_neg]
    have hA := (v15AlgebraicBetaPower_pos n d).ne'
    have hE := Real.exp_ne_zero ((10667 / 1000 : ℝ) * n)
    field_simp
  · simp only [hd, if_false]
    ring

/-- A compact Archimedean lower bound sufficient for every table decision. -/
def v15PiLower : ℝ := 333 / 106

/-- A compact Archimedean upper bound sufficient for every table decision. -/
def v15PiUpper : ℝ := 355 / 113

/-- A rational upper bound for `exp(10.667)`. -/
def v15ExpUpper : ℝ := (21 / 10) ^ (15 : ℕ)

private theorem v15_pi_lower_lt : v15PiLower < Real.pi := by
  unfold v15PiLower
  linarith [Real.pi_gt_d20]

private theorem v15_pi_lt_upper : Real.pi < v15PiUpper := by
  unfold v15PiUpper
  linarith [Real.pi_lt_d20]

private theorem v15_exp_small_lt :
    Real.exp (10667 / 15000 : ℝ) < 21 / 10 := by
  have h := Real.exp_bound' (x := (10667 / 15000 : ℝ))
    (by norm_num) (by norm_num) (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem v15_exp_lt_upper :
    Real.exp (10667 / 1000 : ℝ) < v15ExpUpper := by
  have hpow := pow_lt_pow_left₀ v15_exp_small_lt (Real.exp_nonneg _)
    (by norm_num : (15 : ℕ) ≠ 0)
  rw [← Real.exp_nat_mul] at hpow
  have harg : (↑(15 : ℕ) : ℝ) * (10667 / 15000 : ℝ) =
      10667 / 1000 := by norm_num
  simpa only [v15ExpUpper, harg] using hpow

/-- The rational coefficient multiplying the powers of `π` and `exp`. -/
def v15HCoefficient (n d : ℕ) : ℝ :=
  v15UnitBallSquareCoefficient (n * d) * (d : ℝ) ^ (n * d) /
    v15AlgebraicBetaPower n d

def v15HLower (n d : ℕ) : ℝ :=
  v15HCoefficient n d * v15PiLower ^ v15PiExponent (n * d)

def v15HUpper (n d : ℕ) : ℝ :=
  v15HCoefficient n d * v15PiUpper ^ v15PiExponent (n * d) *
    (if 12 ≤ d then v15ExpUpper ^ n else 1)

private theorem v15UnitBallSquareCoefficient_pos (m : ℕ) :
    0 < v15UnitBallSquareCoefficient m := by
  unfold v15UnitBallSquareCoefficient
  split_ifs <;> positivity

private theorem v15HCoefficient_nonneg (n d : ℕ) :
    0 ≤ v15HCoefficient n d := by
  unfold v15HCoefficient
  exact div_nonneg
    (mul_nonneg (v15UnitBallSquareCoefficient_pos _).le (by positivity))
    (v15AlgebraicBetaPower_pos n d).le

private theorem v15_exponentialCorrection_one_le (n d : ℕ) :
    1 ≤ v15ExponentialCorrection n d := by
  unfold v15ExponentialCorrection
  split_ifs
  · apply Real.one_le_exp
    positivity
  · exact le_rfl

private theorem v15_exponentialCorrection_le_upper (n d : ℕ) :
    v15ExponentialCorrection n d ≤
      (if 12 ≤ d then v15ExpUpper ^ n else 1) := by
  unfold v15ExponentialCorrection
  split_ifs
  · have hpow := pow_le_pow_left₀ (Real.exp_nonneg _)
      v15_exp_lt_upper.le n
    rw [← Real.exp_nat_mul] at hpow
    simpa only [Nat.cast_ofNat, mul_comm] using hpow
  · exact le_rfl

/-- The two compact rational expressions enclose the exact analytic
quantity on every natural rank--degree pair. -/
theorem v15HLower_le_analyticH_le_upper (n d : ℕ) :
    v15HLower n d ≤ v15AnalyticH n d ∧
      v15AnalyticH n d ≤ v15HUpper n d := by
  rw [v15AnalyticH_eq_closed]
  have hC := v15HCoefficient_nonneg n d
  have hPiLowerNonneg : 0 ≤ v15PiLower := by
    norm_num [v15PiLower]
  have hPiUpperNonneg : 0 ≤ v15PiUpper := by
    norm_num [v15PiUpper]
  have hPiL : v15PiLower ^ v15PiExponent (n * d) ≤
      Real.pi ^ v15PiExponent (n * d) :=
    pow_le_pow_left₀ hPiLowerNonneg v15_pi_lower_lt.le _
  have hPiU : Real.pi ^ v15PiExponent (n * d) ≤
      v15PiUpper ^ v15PiExponent (n * d) :=
    pow_le_pow_left₀ Real.pi_pos.le v15_pi_lt_upper.le _
  have hExpL := v15_exponentialCorrection_one_le n d
  have hExpU := v15_exponentialCorrection_le_upper n d
  change
    v15HCoefficient n d * v15PiLower ^ v15PiExponent (n * d) ≤
        v15HCoefficient n d * Real.pi ^ v15PiExponent (n * d) *
          v15ExponentialCorrection n d ∧
      v15HCoefficient n d * Real.pi ^ v15PiExponent (n * d) *
          v15ExponentialCorrection n d ≤
        v15HCoefficient n d * v15PiUpper ^ v15PiExponent (n * d) *
          (if 12 ≤ d then v15ExpUpper ^ n else 1)
  constructor
  · calc
      v15HCoefficient n d * v15PiLower ^ v15PiExponent (n * d) ≤
          v15HCoefficient n d * Real.pi ^ v15PiExponent (n * d) :=
        mul_le_mul_of_nonneg_left hPiL hC
      _ = v15HCoefficient n d * Real.pi ^ v15PiExponent (n * d) * 1 := by ring
      _ ≤ v15HCoefficient n d * Real.pi ^ v15PiExponent (n * d) *
          v15ExponentialCorrection n d :=
        mul_le_mul_of_nonneg_left hExpL (mul_nonneg hC (by positivity))
  · calc
      v15HCoefficient n d * Real.pi ^ v15PiExponent (n * d) *
          v15ExponentialCorrection n d ≤
        v15HCoefficient n d * v15PiUpper ^ v15PiExponent (n * d) *
          v15ExponentialCorrection n d :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hPiU hC) (by positivity)
      _ ≤ v15HCoefficient n d * v15PiUpper ^ v15PiExponent (n * d) *
          (if 12 ≤ d then v15ExpUpper ^ n else 1) :=
        mul_le_mul_of_nonneg_left hExpU
          (mul_nonneg hC (pow_nonneg hPiUpperNonneg _))

/-- A form of `H` convenient for the coarse Stirling estimate. -/
theorem v15AnalyticH_eq_algebraic (n d : ℕ) :
    v15AnalyticH n d =
      (euclideanUnitBallVolume (n * d) ^ (2 : ℕ) *
          (d : ℝ) ^ (n * d) / v15AlgebraicBetaPower n d) *
        v15ExponentialCorrection n d := by
  unfold v15AnalyticH v15BetaPower v15ExponentialCorrection
  by_cases hd : 12 ≤ d
  · simp only [hd, if_true]
    have hneg : -(10667 / 1000 : ℝ) * (n : ℝ) =
        -((10667 / 1000 : ℝ) * n) := by ring
    rw [hneg, Real.exp_neg]
    have hA := (v15AlgebraicBetaPower_pos n d).ne'
    have hE := Real.exp_ne_zero ((10667 / 1000 : ℝ) * n)
    field_simp
  · simp only [hd, if_false]
    ring

private theorem v15_two_pi_e_lt_eighteen :
    2 * Real.pi * Real.exp 1 < 18 := by
  have hpi : Real.pi < (22 / 7 : ℝ) := by
    linarith [Real.pi_lt_d4]
  have he : Real.exp 1 < (11 / 4 : ℝ) := by
    linarith [Real.exp_one_lt_d9]
  nlinarith [Real.pi_pos, Real.exp_pos (1 : ℝ)]

private theorem v15_four_pi_e_lt_thirtyfive :
    4 * Real.pi * Real.exp 1 < 35 := by
  have hpi : Real.pi < (22 / 7 : ℝ) := by
    linarith [Real.pi_lt_d4]
  have he : Real.exp 1 < (11 / 4 : ℝ) := by
    linarith [Real.exp_one_lt_d9]
  nlinarith [Real.pi_pos, Real.exp_pos (1 : ℝ)]

/-- A small rational upper bound used to discharge most classic table cells
without expanding a large factorial. -/
def v15ClassicCoarseUpper (n d : ℕ) : ℝ :=
  ((18 : ℝ) / n) ^ (n * d) / v15AlgebraicBetaPower n d *
    (if 12 ≤ d then v15ExpUpper ^ n else 1)

/-- A small rational upper bound for the scale-two integral condition. -/
def v15IntegralCoarseUpper (n d : ℕ) : ℝ :=
  ((35 : ℝ) / n) ^ (n * d) / v15AlgebraicBetaPower n d *
    (if 12 ≤ d then v15ExpUpper ^ n else 1)

/-- The degree-sized factor whose `n`-th power is the algebraic denominator. -/
def v15AlgebraicBetaDegree (d : ℕ) : ℝ :=
  if d ≤ 9 then (v15MinimumDiscriminant d : ℝ)
  else if d = 10 then (14 : ℝ) ^ d
  else if d = 11 then (14083 / 1000 : ℝ) ^ d
  else (36347 / 1000 : ℝ) ^ d

theorem v15AlgebraicBetaPower_eq_degree_pow (n d : ℕ) :
    v15AlgebraicBetaPower n d = v15AlgebraicBetaDegree d ^ n := by
  unfold v15AlgebraicBetaPower v15AlgebraicBetaDegree
  by_cases hd9 : d ≤ 9
  · simp only [hd9, if_true]
  by_cases hd10 : d = 10
  · subst d
    simp
    simpa [Nat.mul_comm] using (pow_mul (14 : ℝ) 10 n)
  by_cases hd11 : d = 11
  · subst d
    simp
    simpa [Nat.mul_comm] using (pow_mul (14083 / 1000 : ℝ) 11 n)
  · simp only [hd9, hd10, hd11, if_false]
    simpa [Nat.mul_comm] using (pow_mul (36347 / 1000 : ℝ) d n)

/-- The single-rank factor underlying the classic coarse upper bound. -/
def v15ClassicCoarseRoot (n d : ℕ) : ℝ :=
  ((18 : ℝ) / n) ^ d / v15AlgebraicBetaDegree d *
    (if 12 ≤ d then v15ExpUpper else 1)

/-- The single-rank factor underlying the integral coarse upper bound. -/
def v15IntegralCoarseRoot (n d : ℕ) : ℝ :=
  ((35 : ℝ) / n) ^ d / v15AlgebraicBetaDegree d *
    (if 12 ≤ d then v15ExpUpper else 1)

private theorem v15_coarse_correction_eq_pow (n d : ℕ) :
    (if 12 ≤ d then v15ExpUpper ^ n else 1) =
      (if 12 ≤ d then v15ExpUpper else 1) ^ n := by
  split_ifs <;> simp

theorem v15ClassicCoarseUpper_eq_root_pow (n d : ℕ) :
    v15ClassicCoarseUpper n d = v15ClassicCoarseRoot n d ^ n := by
  unfold v15ClassicCoarseUpper v15ClassicCoarseRoot
  rw [v15AlgebraicBetaPower_eq_degree_pow,
    v15_coarse_correction_eq_pow]
  conv_rhs => rw [mul_pow, div_pow]
  have hpow : ((18 : ℝ) / n) ^ (n * d) =
      (((18 : ℝ) / n) ^ d) ^ n := by
    simpa [Nat.mul_comm] using (pow_mul ((18 : ℝ) / n) d n)
  rw [hpow]

theorem v15IntegralCoarseUpper_eq_root_pow (n d : ℕ) :
    v15IntegralCoarseUpper n d = v15IntegralCoarseRoot n d ^ n := by
  unfold v15IntegralCoarseUpper v15IntegralCoarseRoot
  rw [v15AlgebraicBetaPower_eq_degree_pow,
    v15_coarse_correction_eq_pow]
  conv_rhs => rw [mul_pow, div_pow]
  have hpow : ((35 : ℝ) / n) ^ (n * d) =
      (((35 : ℝ) / n) ^ d) ^ n := by
    simpa [Nat.mul_comm] using (pow_mul ((35 : ℝ) / n) d n)
  rw [hpow]

private theorem v15AlgebraicBetaDegree_pos (d : ℕ) :
    0 < v15AlgebraicBetaDegree d := by
  unfold v15AlgebraicBetaDegree
  split_ifs with hd9 hd10 hd11
  · have hdisc : 0 < v15MinimumDiscriminant d := by
      interval_cases d <;> norm_num [v15MinimumDiscriminant]
    positivity
  all_goals positivity

private theorem v15ClassicCoarseRoot_nonneg (n d : ℕ) :
    0 ≤ v15ClassicCoarseRoot n d := by
  unfold v15ClassicCoarseRoot
  exact mul_nonneg
    (div_nonneg (pow_nonneg (by positivity) _)
      (v15AlgebraicBetaDegree_pos d).le)
    (by split_ifs <;> norm_num [v15ExpUpper])

private theorem v15IntegralCoarseRoot_nonneg (n d : ℕ) :
    0 ≤ v15IntegralCoarseRoot n d := by
  unfold v15IntegralCoarseRoot
  exact mul_nonneg
    (div_nonneg (pow_nonneg (by positivity) _)
      (v15AlgebraicBetaDegree_pos d).le)
    (by split_ifs <;> norm_num [v15ExpUpper])

theorem v15ClassicCoarseUpper_lt_one_of_root_lt (n d : ℕ)
    (hn : 0 < n) (hroot : v15ClassicCoarseRoot n d < 1) :
    v15ClassicCoarseUpper n d < 1 := by
  rw [v15ClassicCoarseUpper_eq_root_pow]
  exact pow_lt_one₀ (v15ClassicCoarseRoot_nonneg n d) hroot hn.ne'

theorem v15IntegralCoarseUpper_lt_one_of_root_lt (n d : ℕ)
    (hn : 0 < n) (hroot : v15IntegralCoarseRoot n d < 1) :
    v15IntegralCoarseUpper n d < 1 := by
  rw [v15IntegralCoarseUpper_eq_root_pow]
  exact pow_lt_one₀ (v15IntegralCoarseRoot_nonneg n d) hroot hn.ne'

theorem v15AnalyticH_lt_classicCoarseUpper (n d : ℕ)
    (hn : 0 < n) (hd : 0 < d) :
    v15AnalyticH n d < v15ClassicCoarseUpper n d := by
  rw [v15AnalyticH_eq_algebraic]
  have hball := v15_ball_degree_bound n d hn hd 1 (by norm_num)
  have hball' :
      euclideanUnitBallVolume (n * d) ^ (2 : ℕ) *
          (d : ℝ) ^ (n * d) ≤
        ((2 * Real.pi * Real.exp 1) / (n : ℝ)) ^ (n * d) := by
    convert hball using 1 <;> ring
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbase :
      (2 * Real.pi * Real.exp 1) / (n : ℝ) < 18 / (n : ℝ) :=
    div_lt_div_of_pos_right v15_two_pi_e_lt_eighteen hnR
  have hm : n * d ≠ 0 := (Nat.mul_pos hn hd).ne'
  have hpow :
      ((2 * Real.pi * Real.exp 1) / (n : ℝ)) ^ (n * d) <
        ((18 : ℝ) / n) ^ (n * d) :=
    pow_lt_pow_left₀ hbase (by positivity) hm
  have hnum := hball'.trans_lt hpow
  have hdiv := div_lt_div_of_pos_right hnum
    (v15AlgebraicBetaPower_pos n d)
  have hcorrPos : 0 < v15ExponentialCorrection n d :=
    (zero_lt_one.trans_le (v15_exponentialCorrection_one_le n d))
  have hcorrUpper := v15_exponentialCorrection_le_upper n d
  unfold v15ClassicCoarseUpper
  exact (mul_lt_mul_of_pos_right hdiv hcorrPos).trans_le
    (mul_le_mul_of_nonneg_left hcorrUpper
      (div_nonneg (pow_nonneg (by positivity) _)
        (v15AlgebraicBetaPower_pos n d).le))

theorem v15ScaledAnalyticH_lt_integralCoarseUpper (n d : ℕ)
    (hn : 0 < n) (hd : 0 < d) :
    (2 : ℝ) ^ (n * d) * v15AnalyticH n d <
      v15IntegralCoarseUpper n d := by
  rw [v15AnalyticH_eq_algebraic]
  have hball := v15_ball_degree_bound n d hn hd 2 (by norm_num)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbase :
      (4 * Real.pi * Real.exp 1) / (n : ℝ) < 35 / (n : ℝ) :=
    div_lt_div_of_pos_right v15_four_pi_e_lt_thirtyfive hnR
  have hm : n * d ≠ 0 := (Nat.mul_pos hn hd).ne'
  have hpow :
      ((4 * Real.pi * Real.exp 1) / (n : ℝ)) ^ (n * d) <
        ((35 : ℝ) / n) ^ (n * d) :=
    pow_lt_pow_left₀ hbase (by positivity) hm
  have hnum :
      (2 : ℝ) ^ (n * d) *
          (euclideanUnitBallVolume (n * d) ^ (2 : ℕ) *
            (d : ℝ) ^ (n * d)) <
        ((35 : ℝ) / n) ^ (n * d) := by
    calc
      (2 : ℝ) ^ (n * d) *
          (euclideanUnitBallVolume (n * d) ^ (2 : ℕ) *
            (d : ℝ) ^ (n * d)) =
          euclideanUnitBallVolume (n * d) ^ (2 : ℕ) *
            (2 * (d : ℝ)) ^ (n * d) := by
              rw [mul_pow]
              ring
      _ ≤ ((4 * Real.pi * Real.exp 1) / (n : ℝ)) ^ (n * d) := by
        convert hball using 1 <;> ring
      _ < ((35 : ℝ) / n) ^ (n * d) := hpow
  have hdiv := div_lt_div_of_pos_right hnum
    (v15AlgebraicBetaPower_pos n d)
  have hcorrPos : 0 < v15ExponentialCorrection n d :=
    (zero_lt_one.trans_le (v15_exponentialCorrection_one_le n d))
  have hcorrUpper := v15_exponentialCorrection_le_upper n d
  unfold v15IntegralCoarseUpper
  calc
    (2 : ℝ) ^ (n * d) *
        ((euclideanUnitBallVolume (n * d) ^ (2 : ℕ) *
            (d : ℝ) ^ (n * d) / v15AlgebraicBetaPower n d) *
          v15ExponentialCorrection n d) =
      (((2 : ℝ) ^ (n * d) *
          (euclideanUnitBallVolume (n * d) ^ (2 : ℕ) *
            (d : ℝ) ^ (n * d))) /
        v15AlgebraicBetaPower n d) * v15ExponentialCorrection n d := by ring
    _ < (((35 : ℝ) / n) ^ (n * d) /
          v15AlgebraicBetaPower n d) * v15ExponentialCorrection n d :=
      mul_lt_mul_of_pos_right hdiv hcorrPos
    _ ≤ ((35 : ℝ) / n) ^ (n * d) /
          v15AlgebraicBetaPower n d *
        (if 12 ≤ d then v15ExpUpper ^ n else 1) :=
      mul_le_mul_of_nonneg_left hcorrUpper
        (div_nonneg (pow_nonneg (by positivity) _)
          (v15AlgebraicBetaPower_pos n d).le)

/-- The manuscript's necessary threshold in the integral branch.  Rank one
uses the classic threshold; higher rank uses `2^(-nd)`. -/
def v15IntegralThreshold (n d : ℕ) : ℝ :=
  if n = 1 then 1 else 1 / (2 : ℝ) ^ (n * d)

/-- The coarse root appropriate to the piecewise integral threshold. -/
def v15IntegralDecisionRoot (n d : ℕ) : ℝ :=
  if n = 1 then v15ClassicCoarseRoot n d else v15IntegralCoarseRoot n d

theorem v15AnalyticH_lt_integralThreshold_of_root_lt (n d : ℕ)
    (hn : 0 < n) (hd : 0 < d)
    (hroot : v15IntegralDecisionRoot n d < 1) :
    v15AnalyticH n d < v15IntegralThreshold n d := by
  by_cases hn1 : n = 1
  · subst n
    simp only [v15IntegralDecisionRoot, v15IntegralThreshold, if_true] at hroot ⊢
    exact (v15AnalyticH_lt_classicCoarseUpper 1 d (by norm_num) hd).trans
      (v15ClassicCoarseUpper_lt_one_of_root_lt 1 d (by norm_num) hroot)
  · simp only [v15IntegralDecisionRoot, v15IntegralThreshold, hn1, if_false] at hroot ⊢
    have hs := (v15ScaledAnalyticH_lt_integralCoarseUpper n d hn hd).trans
      (v15IntegralCoarseUpper_lt_one_of_root_lt n d hn hroot)
    apply (lt_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) (n * d))).2
    simpa only [mul_comm] using hs

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exhaustive rational normalization checks all 476 finite-grid cells.
/-- Kernel-checked rational certificates for every classic cell in the
`34 × 14` grid. -/
theorem v15_classic_grid_certificate (n d : ℕ)
    (hn : 1 ≤ n) (hn' : n ≤ 34) (hd : 1 ≤ d) (hd' : d ≤ 14) :
    ((n, d) ∈ v15ClassicAdmissiblePairs → (1 : ℝ) ≤ v15HLower n d) ∧
      ((n, d) ∉ v15ClassicAdmissiblePairs →
        v15ClassicCoarseRoot n d < 1 ∨ v15HUpper n d < 1) := by
  constructor
  · intro hmem
    interval_cases n <;> interval_cases d <;>
      simp [v15ClassicAdmissiblePairs] at hmem
    all_goals
      norm_num [v15HLower, v15HCoefficient, v15UnitBallSquareCoefficient,
        v15PiExponent, v15PiLower, v15AlgebraicBetaPower,
        v15MinimumDiscriminant, Nat.factorial, Nat.doubleFactorial]
  · intro hmem
    interval_cases n <;> interval_cases d <;>
      simp [v15ClassicAdmissiblePairs] at hmem
    all_goals
      norm_num [v15ClassicCoarseRoot, v15AlgebraicBetaDegree,
        v15HUpper, v15HCoefficient, v15UnitBallSquareCoefficient,
        v15PiExponent, v15PiUpper, v15ExpUpper,
        v15AlgebraicBetaPower, v15MinimumDiscriminant,
        Nat.factorial, Nat.doubleFactorial]

/-- On the full finite grid, the analytic condition `H(n,d) ≥ 1` is
equivalent to membership in the 24-pair classic table. -/
theorem v15_classic_analytic_grid_iff_mem (n d : ℕ)
    (hn : 1 ≤ n) (hn' : n ≤ 34) (hd : 1 ≤ d) (hd' : d ≤ 14) :
    (1 : ℝ) ≤ v15AnalyticH n d ↔
      (n, d) ∈ v15ClassicAdmissiblePairs := by
  have hcert := v15_classic_grid_certificate n d hn hn' hd hd'
  constructor
  · intro hH
    by_contra hmem
    rcases hcert.2 hmem with hroot | hupper
    · have hlt := (v15AnalyticH_lt_classicCoarseUpper n d (by omega) (by omega)).trans
          (v15ClassicCoarseUpper_lt_one_of_root_lt n d (by omega) hroot)
      linarith
    · have hlt := (v15HLower_le_analyticH_le_upper n d).2.trans_lt hupper
      linarith
  · intro hmem
    exact (hcert.1 hmem).trans (v15HLower_le_analyticH_le_upper n d).1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exhaustive rational normalization checks all 476 finite-grid cells.
/-- Kernel-checked rational certificates for every integral cell in the
`34 × 14` grid, including the separate rank-one threshold. -/
theorem v15_integral_grid_certificate (n d : ℕ)
    (hn : 1 ≤ n) (hn' : n ≤ 34) (hd : 1 ≤ d) (hd' : d ≤ 14) :
    ((n, d) ∈ v15IntegralAdmissiblePairs →
        v15IntegralThreshold n d ≤ v15HLower n d) ∧
      ((n, d) ∉ v15IntegralAdmissiblePairs →
        v15IntegralDecisionRoot n d < 1 ∨
          v15HUpper n d < v15IntegralThreshold n d) := by
  constructor
  · intro hmem
    interval_cases n <;> interval_cases d <;>
      simp [v15IntegralAdmissiblePairs] at hmem
    all_goals
      norm_num [v15IntegralThreshold, v15HLower, v15HCoefficient,
        v15UnitBallSquareCoefficient, v15PiExponent, v15PiLower,
        v15AlgebraicBetaPower, v15MinimumDiscriminant,
        Nat.factorial, Nat.doubleFactorial]
  · intro hmem
    interval_cases n <;> interval_cases d <;>
      simp [v15IntegralAdmissiblePairs] at hmem
    all_goals
      norm_num [v15IntegralDecisionRoot, v15ClassicCoarseRoot,
        v15IntegralCoarseRoot, v15AlgebraicBetaDegree,
        v15IntegralThreshold, v15HUpper, v15HCoefficient,
        v15UnitBallSquareCoefficient, v15PiExponent, v15PiUpper,
        v15ExpUpper, v15AlgebraicBetaPower, v15MinimumDiscriminant,
        Nat.factorial, Nat.doubleFactorial]

/-- On the full finite grid, the manuscript's piecewise integral condition
is equivalent to membership in the 63-pair integral table. -/
theorem v15_integral_analytic_grid_iff_mem (n d : ℕ)
    (hn : 1 ≤ n) (hn' : n ≤ 34) (hd : 1 ≤ d) (hd' : d ≤ 14) :
    v15IntegralThreshold n d ≤ v15AnalyticH n d ↔
      (n, d) ∈ v15IntegralAdmissiblePairs := by
  have hcert := v15_integral_grid_certificate n d hn hn' hd hd'
  constructor
  · intro hH
    by_contra hmem
    rcases hcert.2 hmem with hroot | hupper
    · have hlt := v15AnalyticH_lt_integralThreshold_of_root_lt
          n d (by omega) (by omega) hroot
      linarith
    · have hlt := (v15HLower_le_analyticH_le_upper n d).2.trans_lt hupper
      linarith
  · intro hmem
    exact (hcert.1 hmem).trans (v15HLower_le_analyticH_le_upper n d).1

end

end TraceEuclidean
