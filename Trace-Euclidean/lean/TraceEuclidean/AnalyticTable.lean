import TraceEuclidean.AdmissibleTables
import TraceEuclidean.FinitenessAssembly
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Real.Pi.Bounds

/-!
The analytic quantity used for the finite rank--degree tables in Section 4 of
the frozen Trace-Euclidean  input.  This module turns the Gamma expression
into an exact factorial expression and then encloses it between rational
bounds.  The cited root-discriminant estimates remain external inputs; all
subsequent analytic and finite arithmetic is checked by Lean.
-/

namespace TraceEuclidean

noncomputable section

/-- The exact discriminant minima used in degrees `1, ..., 9`. -/
def minimumDiscriminant : ℕ → ℕ
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
def algebraicBetaPower (n d : ℕ) : ℝ :=
  if d ≤ 9 then (minimumDiscriminant d : ℝ) ^ n
  else if d = 10 then (14 : ℝ) ^ (n * d)
  else if d = 11 then (14083 / 1000 : ℝ) ^ (n * d)
  else (36347 / 1000 : ℝ) ^ (n * d)

/-- The exact power `β_d^(nd)` corresponding to the piecewise `β_d` in
Section 4. -/
def betaPower (n d : ℕ) : ℝ :=
  if 12 ≤ d then
    algebraicBetaPower n d *
      Real.exp (-(10667 / 1000 : ℝ) * n)
  else algebraicBetaPower n d

/-- The manuscript's analytic quantity
`H(n,d) = (πd)^(nd) / (Γ(nd/2+1)^2 β_d^(nd))`. -/
def analyticH (n d : ℕ) : ℝ :=
  euclideanUnitBallVolume (n * d) ^ (2 : ℕ) *
    (d : ℝ) ^ (n * d) / betaPower n d

/-- The exponent of `π` after evaluating the half-integral Gamma value. -/
def piExponent (m : ℕ) : ℕ :=
  if Even m then m else m - 1

/-- The rational coefficient in the square of the unit-ball volume after
evaluating the Gamma value. -/
def unitBallSquareCoefficient (m : ℕ) : ℝ :=
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
theorem unitBallVolume_sq_closed (m : ℕ) :
    euclideanUnitBallVolume m ^ (2 : ℕ) =
      unitBallSquareCoefficient m * Real.pi ^ piExponent m := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · have harg : (((2 * k : ℕ) : ℝ) / 2 + 1) = (k : ℝ) + 1 := by
      push_cast
      ring
    have heven : Even (2 * k) := even_two_mul k
    have hdiv : (2 * k) / 2 = k := by omega
    have hfac : (k.factorial : ℝ) ≠ 0 := by positivity
    unfold euclideanUnitBallVolume unitBallSquareCoefficient piExponent
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
    unfold euclideanUnitBallVolume unitBallSquareCoefficient piExponent
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
def exponentialCorrection (n d : ℕ) : ℝ :=
  if 12 ≤ d then Real.exp ((10667 / 1000 : ℝ) * n) else 1

/-- The factorial form of `analyticH`. -/
def closedH (n d : ℕ) : ℝ :=
  (unitBallSquareCoefficient (n * d) * (d : ℝ) ^ (n * d) /
      algebraicBetaPower n d) *
    Real.pi ^ piExponent (n * d) * exponentialCorrection n d

theorem algebraicBetaPower_pos (n d : ℕ) :
    0 < algebraicBetaPower n d := by
  unfold algebraicBetaPower
  split_ifs with hd9 hd10 hd11
  · have hdisc : 0 < minimumDiscriminant d := by
      interval_cases d <;> norm_num [minimumDiscriminant]
    positivity
  all_goals positivity

/-- The Gamma definition of `H(n,d)` and its factorial form agree exactly. -/
theorem analyticH_eq_closed (n d : ℕ) :
    analyticH n d = closedH n d := by
  rw [analyticH, unitBallVolume_sq_closed]
  unfold closedH betaPower exponentialCorrection
  by_cases hd : 12 ≤ d
  · simp only [hd, if_true]
    have hneg : -(10667 / 1000 : ℝ) * (n : ℝ) =
        -((10667 / 1000 : ℝ) * n) := by ring
    rw [hneg]
    rw [Real.exp_neg]
    have hA := (algebraicBetaPower_pos n d).ne'
    have hE := Real.exp_ne_zero ((10667 / 1000 : ℝ) * n)
    field_simp
  · simp only [hd, if_false]
    ring

/-- A compact Archimedean lower bound sufficient for every table decision. -/
def piLower : ℝ := 333 / 106

/-- A compact Archimedean upper bound sufficient for every table decision. -/
def piUpper : ℝ := 355 / 113

/-- A rational upper bound for `exp(10.667)`. -/
def expUpper : ℝ := (21 / 10) ^ (15 : ℕ)

private theorem pi_lower_lt : piLower < Real.pi := by
  unfold piLower
  linarith [Real.pi_gt_d20]

private theorem pi_lt_upper : Real.pi < piUpper := by
  unfold piUpper
  linarith [Real.pi_lt_d20]

private theorem exp_small_lt :
    Real.exp (10667 / 15000 : ℝ) < 21 / 10 := by
  have h := Real.exp_bound' (x := (10667 / 15000 : ℝ))
    (by norm_num) (by norm_num) (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem exp_lt_upper :
    Real.exp (10667 / 1000 : ℝ) < expUpper := by
  have hpow := pow_lt_pow_left₀ exp_small_lt (Real.exp_nonneg _)
    (by norm_num : (15 : ℕ) ≠ 0)
  rw [← Real.exp_nat_mul] at hpow
  have harg : (↑(15 : ℕ) : ℝ) * (10667 / 15000 : ℝ) =
      10667 / 1000 := by norm_num
  simpa only [expUpper, harg] using hpow

/-- The rational coefficient multiplying the powers of `π` and `exp`. -/
def hCoefficient (n d : ℕ) : ℝ :=
  unitBallSquareCoefficient (n * d) * (d : ℝ) ^ (n * d) /
    algebraicBetaPower n d

def hLower (n d : ℕ) : ℝ :=
  hCoefficient n d * piLower ^ piExponent (n * d)

def hUpper (n d : ℕ) : ℝ :=
  hCoefficient n d * piUpper ^ piExponent (n * d) *
    (if 12 ≤ d then expUpper ^ n else 1)

private theorem unitBallSquareCoefficient_pos (m : ℕ) :
    0 < unitBallSquareCoefficient m := by
  unfold unitBallSquareCoefficient
  split_ifs <;> positivity

private theorem hCoefficient_nonneg (n d : ℕ) :
    0 ≤ hCoefficient n d := by
  unfold hCoefficient
  exact div_nonneg
    (mul_nonneg (unitBallSquareCoefficient_pos _).le (by positivity))
    (algebraicBetaPower_pos n d).le

private theorem exponentialCorrection_one_le (n d : ℕ) :
    1 ≤ exponentialCorrection n d := by
  unfold exponentialCorrection
  split_ifs
  · apply Real.one_le_exp
    positivity
  · exact le_rfl

private theorem exponentialCorrection_le_upper (n d : ℕ) :
    exponentialCorrection n d ≤
      (if 12 ≤ d then expUpper ^ n else 1) := by
  unfold exponentialCorrection
  split_ifs
  · have hpow := pow_le_pow_left₀ (Real.exp_nonneg _)
      exp_lt_upper.le n
    rw [← Real.exp_nat_mul] at hpow
    simpa only [Nat.cast_ofNat, mul_comm] using hpow
  · exact le_rfl

/-- The two compact rational expressions enclose the exact analytic
quantity on every natural rank--degree pair. -/
theorem hLower_le_analyticH_le_upper (n d : ℕ) :
    hLower n d ≤ analyticH n d ∧
      analyticH n d ≤ hUpper n d := by
  rw [analyticH_eq_closed]
  have hC := hCoefficient_nonneg n d
  have hPiLowerNonneg : 0 ≤ piLower := by
    norm_num [piLower]
  have hPiUpperNonneg : 0 ≤ piUpper := by
    norm_num [piUpper]
  have hPiL : piLower ^ piExponent (n * d) ≤
      Real.pi ^ piExponent (n * d) :=
    pow_le_pow_left₀ hPiLowerNonneg pi_lower_lt.le _
  have hPiU : Real.pi ^ piExponent (n * d) ≤
      piUpper ^ piExponent (n * d) :=
    pow_le_pow_left₀ Real.pi_pos.le pi_lt_upper.le _
  have hExpL := exponentialCorrection_one_le n d
  have hExpU := exponentialCorrection_le_upper n d
  change
    hCoefficient n d * piLower ^ piExponent (n * d) ≤
        hCoefficient n d * Real.pi ^ piExponent (n * d) *
          exponentialCorrection n d ∧
      hCoefficient n d * Real.pi ^ piExponent (n * d) *
          exponentialCorrection n d ≤
        hCoefficient n d * piUpper ^ piExponent (n * d) *
          (if 12 ≤ d then expUpper ^ n else 1)
  constructor
  · calc
      hCoefficient n d * piLower ^ piExponent (n * d) ≤
          hCoefficient n d * Real.pi ^ piExponent (n * d) :=
        mul_le_mul_of_nonneg_left hPiL hC
      _ = hCoefficient n d * Real.pi ^ piExponent (n * d) * 1 := by ring
      _ ≤ hCoefficient n d * Real.pi ^ piExponent (n * d) *
          exponentialCorrection n d :=
        mul_le_mul_of_nonneg_left hExpL (mul_nonneg hC (by positivity))
  · calc
      hCoefficient n d * Real.pi ^ piExponent (n * d) *
          exponentialCorrection n d ≤
        hCoefficient n d * piUpper ^ piExponent (n * d) *
          exponentialCorrection n d :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hPiU hC) (by positivity)
      _ ≤ hCoefficient n d * piUpper ^ piExponent (n * d) *
          (if 12 ≤ d then expUpper ^ n else 1) :=
        mul_le_mul_of_nonneg_left hExpU
          (mul_nonneg hC (pow_nonneg hPiUpperNonneg _))

/-- A form of `H` convenient for the coarse Stirling estimate. -/
theorem analyticH_eq_algebraic (n d : ℕ) :
    analyticH n d =
      (euclideanUnitBallVolume (n * d) ^ (2 : ℕ) *
          (d : ℝ) ^ (n * d) / algebraicBetaPower n d) *
        exponentialCorrection n d := by
  unfold analyticH betaPower exponentialCorrection
  by_cases hd : 12 ≤ d
  · simp only [hd, if_true]
    have hneg : -(10667 / 1000 : ℝ) * (n : ℝ) =
        -((10667 / 1000 : ℝ) * n) := by ring
    rw [hneg, Real.exp_neg]
    have hA := (algebraicBetaPower_pos n d).ne'
    have hE := Real.exp_ne_zero ((10667 / 1000 : ℝ) * n)
    field_simp
  · simp only [hd, if_false]
    ring

private theorem two_pi_e_lt_eighteen :
    2 * Real.pi * Real.exp 1 < 18 := by
  have hpi : Real.pi < (22 / 7 : ℝ) := by
    linarith [Real.pi_lt_d4]
  have he : Real.exp 1 < (11 / 4 : ℝ) := by
    linarith [Real.exp_one_lt_d9]
  nlinarith [Real.pi_pos, Real.exp_pos (1 : ℝ)]

private theorem four_pi_e_lt_thirtyfive :
    4 * Real.pi * Real.exp 1 < 35 := by
  have hpi : Real.pi < (22 / 7 : ℝ) := by
    linarith [Real.pi_lt_d4]
  have he : Real.exp 1 < (11 / 4 : ℝ) := by
    linarith [Real.exp_one_lt_d9]
  nlinarith [Real.pi_pos, Real.exp_pos (1 : ℝ)]

/-- A small rational upper bound used to discharge most classic table cells
without expanding a large factorial. -/
def classicCoarseUpper (n d : ℕ) : ℝ :=
  ((18 : ℝ) / n) ^ (n * d) / algebraicBetaPower n d *
    (if 12 ≤ d then expUpper ^ n else 1)

/-- A small rational upper bound for the scale-two integral condition. -/
def integralCoarseUpper (n d : ℕ) : ℝ :=
  ((35 : ℝ) / n) ^ (n * d) / algebraicBetaPower n d *
    (if 12 ≤ d then expUpper ^ n else 1)

/-- The degree-sized factor whose `n`-th power is the algebraic denominator. -/
def algebraicBetaDegree (d : ℕ) : ℝ :=
  if d ≤ 9 then (minimumDiscriminant d : ℝ)
  else if d = 10 then (14 : ℝ) ^ d
  else if d = 11 then (14083 / 1000 : ℝ) ^ d
  else (36347 / 1000 : ℝ) ^ d

theorem algebraicBetaPower_eq_degree_pow (n d : ℕ) :
    algebraicBetaPower n d = algebraicBetaDegree d ^ n := by
  unfold algebraicBetaPower algebraicBetaDegree
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
def classicCoarseRoot (n d : ℕ) : ℝ :=
  ((18 : ℝ) / n) ^ d / algebraicBetaDegree d *
    (if 12 ≤ d then expUpper else 1)

/-- The single-rank factor underlying the integral coarse upper bound. -/
def integralCoarseRoot (n d : ℕ) : ℝ :=
  ((35 : ℝ) / n) ^ d / algebraicBetaDegree d *
    (if 12 ≤ d then expUpper else 1)

private theorem coarse_correction_eq_pow (n d : ℕ) :
    (if 12 ≤ d then expUpper ^ n else 1) =
      (if 12 ≤ d then expUpper else 1) ^ n := by
  split_ifs <;> simp

theorem classicCoarseUpper_eq_root_pow (n d : ℕ) :
    classicCoarseUpper n d = classicCoarseRoot n d ^ n := by
  unfold classicCoarseUpper classicCoarseRoot
  rw [algebraicBetaPower_eq_degree_pow,
    coarse_correction_eq_pow]
  conv_rhs => rw [mul_pow, div_pow]
  have hpow : ((18 : ℝ) / n) ^ (n * d) =
      (((18 : ℝ) / n) ^ d) ^ n := by
    simpa [Nat.mul_comm] using (pow_mul ((18 : ℝ) / n) d n)
  rw [hpow]

theorem integralCoarseUpper_eq_root_pow (n d : ℕ) :
    integralCoarseUpper n d = integralCoarseRoot n d ^ n := by
  unfold integralCoarseUpper integralCoarseRoot
  rw [algebraicBetaPower_eq_degree_pow,
    coarse_correction_eq_pow]
  conv_rhs => rw [mul_pow, div_pow]
  have hpow : ((35 : ℝ) / n) ^ (n * d) =
      (((35 : ℝ) / n) ^ d) ^ n := by
    simpa [Nat.mul_comm] using (pow_mul ((35 : ℝ) / n) d n)
  rw [hpow]

private theorem algebraicBetaDegree_pos (d : ℕ) :
    0 < algebraicBetaDegree d := by
  unfold algebraicBetaDegree
  split_ifs with hd9 hd10 hd11
  · have hdisc : 0 < minimumDiscriminant d := by
      interval_cases d <;> norm_num [minimumDiscriminant]
    positivity
  all_goals positivity

private theorem classicCoarseRoot_nonneg (n d : ℕ) :
    0 ≤ classicCoarseRoot n d := by
  unfold classicCoarseRoot
  exact mul_nonneg
    (div_nonneg (pow_nonneg (by positivity) _)
      (algebraicBetaDegree_pos d).le)
    (by split_ifs <;> norm_num [expUpper])

private theorem integralCoarseRoot_nonneg (n d : ℕ) :
    0 ≤ integralCoarseRoot n d := by
  unfold integralCoarseRoot
  exact mul_nonneg
    (div_nonneg (pow_nonneg (by positivity) _)
      (algebraicBetaDegree_pos d).le)
    (by split_ifs <;> norm_num [expUpper])

theorem classicCoarseUpper_lt_one_of_root_lt (n d : ℕ)
    (hn : 0 < n) (hroot : classicCoarseRoot n d < 1) :
    classicCoarseUpper n d < 1 := by
  rw [classicCoarseUpper_eq_root_pow]
  exact pow_lt_one₀ (classicCoarseRoot_nonneg n d) hroot hn.ne'

theorem integralCoarseUpper_lt_one_of_root_lt (n d : ℕ)
    (hn : 0 < n) (hroot : integralCoarseRoot n d < 1) :
    integralCoarseUpper n d < 1 := by
  rw [integralCoarseUpper_eq_root_pow]
  exact pow_lt_one₀ (integralCoarseRoot_nonneg n d) hroot hn.ne'

theorem analyticH_lt_classicCoarseUpper (n d : ℕ)
    (hn : 0 < n) (hd : 0 < d) :
    analyticH n d < classicCoarseUpper n d := by
  rw [analyticH_eq_algebraic]
  have hball := ball_degree_bound n d hn hd 1 (by norm_num)
  have hball' :
      euclideanUnitBallVolume (n * d) ^ (2 : ℕ) *
          (d : ℝ) ^ (n * d) ≤
        ((2 * Real.pi * Real.exp 1) / (n : ℝ)) ^ (n * d) := by
    convert hball using 1 <;> ring
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbase :
      (2 * Real.pi * Real.exp 1) / (n : ℝ) < 18 / (n : ℝ) :=
    div_lt_div_of_pos_right two_pi_e_lt_eighteen hnR
  have hm : n * d ≠ 0 := (Nat.mul_pos hn hd).ne'
  have hpow :
      ((2 * Real.pi * Real.exp 1) / (n : ℝ)) ^ (n * d) <
        ((18 : ℝ) / n) ^ (n * d) :=
    pow_lt_pow_left₀ hbase (by positivity) hm
  have hnum := hball'.trans_lt hpow
  have hdiv := div_lt_div_of_pos_right hnum
    (algebraicBetaPower_pos n d)
  have hcorrPos : 0 < exponentialCorrection n d :=
    (zero_lt_one.trans_le (exponentialCorrection_one_le n d))
  have hcorrUpper := exponentialCorrection_le_upper n d
  unfold classicCoarseUpper
  exact (mul_lt_mul_of_pos_right hdiv hcorrPos).trans_le
    (mul_le_mul_of_nonneg_left hcorrUpper
      (div_nonneg (pow_nonneg (by positivity) _)
        (algebraicBetaPower_pos n d).le))

theorem scaledAnalyticH_lt_integralCoarseUpper (n d : ℕ)
    (hn : 0 < n) (hd : 0 < d) :
    (2 : ℝ) ^ (n * d) * analyticH n d <
      integralCoarseUpper n d := by
  rw [analyticH_eq_algebraic]
  have hball := ball_degree_bound n d hn hd 2 (by norm_num)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbase :
      (4 * Real.pi * Real.exp 1) / (n : ℝ) < 35 / (n : ℝ) :=
    div_lt_div_of_pos_right four_pi_e_lt_thirtyfive hnR
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
    (algebraicBetaPower_pos n d)
  have hcorrPos : 0 < exponentialCorrection n d :=
    (zero_lt_one.trans_le (exponentialCorrection_one_le n d))
  have hcorrUpper := exponentialCorrection_le_upper n d
  unfold integralCoarseUpper
  calc
    (2 : ℝ) ^ (n * d) *
        ((euclideanUnitBallVolume (n * d) ^ (2 : ℕ) *
            (d : ℝ) ^ (n * d) / algebraicBetaPower n d) *
          exponentialCorrection n d) =
      (((2 : ℝ) ^ (n * d) *
          (euclideanUnitBallVolume (n * d) ^ (2 : ℕ) *
            (d : ℝ) ^ (n * d))) /
        algebraicBetaPower n d) * exponentialCorrection n d := by ring
    _ < (((35 : ℝ) / n) ^ (n * d) /
          algebraicBetaPower n d) * exponentialCorrection n d :=
      mul_lt_mul_of_pos_right hdiv hcorrPos
    _ ≤ ((35 : ℝ) / n) ^ (n * d) /
          algebraicBetaPower n d *
        (if 12 ≤ d then expUpper ^ n else 1) :=
      mul_le_mul_of_nonneg_left hcorrUpper
        (div_nonneg (pow_nonneg (by positivity) _)
          (algebraicBetaPower_pos n d).le)

/-- The manuscript's necessary threshold in the integral branch.  Rank one
uses the classic threshold; higher rank uses `2^(-nd)`. -/
def integralThreshold (n d : ℕ) : ℝ :=
  if n = 1 then 1 else 1 / (2 : ℝ) ^ (n * d)

/-- The coarse root appropriate to the piecewise integral threshold. -/
def integralDecisionRoot (n d : ℕ) : ℝ :=
  if n = 1 then classicCoarseRoot n d else integralCoarseRoot n d

theorem analyticH_lt_integralThreshold_of_root_lt (n d : ℕ)
    (hn : 0 < n) (hd : 0 < d)
    (hroot : integralDecisionRoot n d < 1) :
    analyticH n d < integralThreshold n d := by
  by_cases hn1 : n = 1
  · subst n
    simp only [integralDecisionRoot, integralThreshold, if_true] at hroot ⊢
    exact (analyticH_lt_classicCoarseUpper 1 d (by norm_num) hd).trans
      (classicCoarseUpper_lt_one_of_root_lt 1 d (by norm_num) hroot)
  · simp only [integralDecisionRoot, integralThreshold, hn1, if_false] at hroot ⊢
    have hs := (scaledAnalyticH_lt_integralCoarseUpper n d hn hd).trans
      (integralCoarseUpper_lt_one_of_root_lt n d hn hroot)
    apply (lt_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) (n * d))).2
    simpa only [mul_comm] using hs

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exhaustive rational normalization checks all 476 finite-grid cells.
/-- Kernel-checked rational certificates for every classic cell in the
`34 × 14` grid. -/
theorem classic_grid_certificate (n d : ℕ)
    (hn : 1 ≤ n) (hn' : n ≤ 34) (hd : 1 ≤ d) (hd' : d ≤ 14) :
    ((n, d) ∈ classicAdmissiblePairs → (1 : ℝ) ≤ hLower n d) ∧
      ((n, d) ∉ classicAdmissiblePairs →
        classicCoarseRoot n d < 1 ∨ hUpper n d < 1) := by
  constructor
  · intro hmem
    interval_cases n <;> interval_cases d <;>
      simp [classicAdmissiblePairs] at hmem
    all_goals
      norm_num [hLower, hCoefficient, unitBallSquareCoefficient,
        piExponent, piLower, algebraicBetaPower,
        minimumDiscriminant, Nat.factorial, Nat.doubleFactorial]
  · intro hmem
    interval_cases n <;> interval_cases d <;>
      simp [classicAdmissiblePairs] at hmem
    all_goals
      norm_num [classicCoarseRoot, algebraicBetaDegree,
        hUpper, hCoefficient, unitBallSquareCoefficient,
        piExponent, piUpper, expUpper,
        algebraicBetaPower, minimumDiscriminant,
        Nat.factorial, Nat.doubleFactorial]

/-- On the full finite grid, the analytic condition `H(n,d) ≥ 1` is
equivalent to membership in the 24-pair classic table. -/
theorem classic_analytic_grid_iff_mem (n d : ℕ)
    (hn : 1 ≤ n) (hn' : n ≤ 34) (hd : 1 ≤ d) (hd' : d ≤ 14) :
    (1 : ℝ) ≤ analyticH n d ↔
      (n, d) ∈ classicAdmissiblePairs := by
  have hcert := classic_grid_certificate n d hn hn' hd hd'
  constructor
  · intro hH
    by_contra hmem
    rcases hcert.2 hmem with hroot | hupper
    · have hlt := (analyticH_lt_classicCoarseUpper n d (by omega) (by omega)).trans
          (classicCoarseUpper_lt_one_of_root_lt n d (by omega) hroot)
      linarith
    · have hlt := (hLower_le_analyticH_le_upper n d).2.trans_lt hupper
      linarith
  · intro hmem
    exact (hcert.1 hmem).trans (hLower_le_analyticH_le_upper n d).1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exhaustive rational normalization checks all 476 finite-grid cells.
/-- Kernel-checked rational certificates for every integral cell in the
`34 × 14` grid, including the separate rank-one threshold. -/
theorem integral_grid_certificate (n d : ℕ)
    (hn : 1 ≤ n) (hn' : n ≤ 34) (hd : 1 ≤ d) (hd' : d ≤ 14) :
    ((n, d) ∈ integralAdmissiblePairs →
        integralThreshold n d ≤ hLower n d) ∧
      ((n, d) ∉ integralAdmissiblePairs →
        integralDecisionRoot n d < 1 ∨
          hUpper n d < integralThreshold n d) := by
  constructor
  · intro hmem
    interval_cases n <;> interval_cases d <;>
      simp [integralAdmissiblePairs] at hmem
    all_goals
      norm_num [integralThreshold, hLower, hCoefficient,
        unitBallSquareCoefficient, piExponent, piLower,
        algebraicBetaPower, minimumDiscriminant,
        Nat.factorial, Nat.doubleFactorial]
  · intro hmem
    interval_cases n <;> interval_cases d <;>
      simp [integralAdmissiblePairs] at hmem
    all_goals
      norm_num [integralDecisionRoot, classicCoarseRoot,
        integralCoarseRoot, algebraicBetaDegree,
        integralThreshold, hUpper, hCoefficient,
        unitBallSquareCoefficient, piExponent, piUpper,
        expUpper, algebraicBetaPower, minimumDiscriminant,
        Nat.factorial, Nat.doubleFactorial]

/-- On the full finite grid, the manuscript's piecewise integral condition
is equivalent to membership in the 63-pair integral table. -/
theorem integral_analytic_grid_iff_mem (n d : ℕ)
    (hn : 1 ≤ n) (hn' : n ≤ 34) (hd : 1 ≤ d) (hd' : d ≤ 14) :
    integralThreshold n d ≤ analyticH n d ↔
      (n, d) ∈ integralAdmissiblePairs := by
  have hcert := integral_grid_certificate n d hn hn' hd hd'
  constructor
  · intro hH
    by_contra hmem
    rcases hcert.2 hmem with hroot | hupper
    · have hlt := analyticH_lt_integralThreshold_of_root_lt
          n d (by omega) (by omega) hroot
      linarith
    · have hlt := (hLower_le_analyticH_le_upper n d).2.trans_lt hupper
      linarith
  · intro hmem
    exact (hcert.1 hmem).trans (hLower_le_analyticH_le_upper n d).1

end

end TraceEuclidean
