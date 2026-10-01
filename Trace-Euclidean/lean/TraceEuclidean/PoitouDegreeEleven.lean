import LeanCert.Core.IntervalRat.Taylor
import LeanCert.Examples.EulerMascheroniLowerBounds
import TraceEuclidean.AnalyticTableBridge
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Numerical ingredients for Poitou's degree-eleven discriminant kernel

This file certifies exact rational enclosures for the logarithm, square root,
and arctangent occurring in Poitou's closed function `L`.  It also isolates
  Poitou's infinite `L₁` sum and the exact specialized explicit-formula
  statement.  The strict upper bound for that sum is proved separately in
  `PoitouDegreeElevenClosed`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open scoped BigOperators
open Finset Filter
open LeanCert.Core

namespace TraceEuclidean.PoitouDegreeEleven

noncomputable section

def poitouY : ℝ := 1351 / 2000

def poitouLClosed (y : ℝ) : ℝ :=
  -3 / (20 * y ^ 2) + 33 / (10 * y) + 2 +
    (3 / (80 * y ^ 3) + 3 / (4 * y ^ 2)) * Real.log (1 + 4 * y) -
    (3 / y + 12 / 5) / Real.sqrt y * Real.arctan (2 * Real.sqrt y)

/-- Poitou's `L₁` function in the totally real case `r₁ / n = 1`. -/
def poitouL1 (y : ℝ) : ℝ :=
  (∑' k : ℕ,
      poitouLClosed (y / ((2 * k + 1 : ℕ) : ℝ) ^ 2) /
        ((2 * k + 1 : ℕ) : ℝ)) +
    ∑' k : ℕ,
      (-1 : ℝ) ^ k *
        poitouLClosed (y / ((k + 1 : ℕ) : ℝ) ^ 2)

/-- The remaining specialized numerical certificate for the degree-eleven
row.  Its target leaves more than `1.4e-6` above the numerical value of `L₁`. -/
def PoitouL1UpperCertificate : Prop :=
  poitouL1 poitouY < (629291 / 1000000 : ℝ)

/-- Poitou's discriminant inequality, specialized to totally real degree
eleven and the rational parameter used for the optimized table row. -/
def PoitouDegreeElevenFormulaInput : Prop :=
  ∀ (K : CodedNumberField), NumberField.IsTotallyReal K.1 →
    Module.finrank ℚ K.1 = 11 →
      Real.eulerMascheroniConstant + Real.log (4 * Real.pi) + 1 -
          poitouL1 poitouY - 12 * Real.pi / (55 * Real.sqrt poitouY) ≤
        Real.log (((|K.discriminant| : ℤ) : ℝ)) / 11

theorem log_1851_div_500_upper :
    Real.log (1851 / 500 : ℝ) < (1308873215 / 1000000000 : ℝ) := by
  let z : ℝ := 1351 / 2351
  have hz0 : 0 ≤ z := by norm_num [z]
  have hz1 : z < 1 := by norm_num [z]
  have h := Real.log_div_le_sum_range_add hz0 hz1 20
  have hratio : (1 + z) / (1 - z) = (1851 / 500 : ℝ) := by
    norm_num [z]
  rw [hratio] at h
  have hnum :
      2 * ((∑ i ∈ range 20, z ^ (2 * i + 1) / (2 * i + 1)) +
        z ^ (41 : ℕ) / (1 - z ^ 2)) <
        (1308873215 / 1000000000 : ℝ) := by
    norm_num [z, Finset.sum_range_succ]
  nlinarith

private def atanTerm (q : ℝ) (n : ℕ) : ℝ :=
  q ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)

private theorem atanTerm_antitone {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Antitone (atanTerm q) := by
  intro a b hab
  dsimp [atanTerm]
  have hpow : q ^ (2 * b + 1) ≤ q ^ (2 * a + 1) := by
    exact pow_le_pow_of_le_one hq0 hq1 (by omega)
  have hdena : (0 : ℝ) < ((2 * a + 1 : ℕ) : ℝ) := by positivity
  have hden : ((2 * a + 1 : ℕ) : ℝ) ≤ ((2 * b + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 2 * a + 1 ≤ 2 * b + 1)
  exact (div_le_div_of_nonneg_left (pow_nonneg hq0 _) hdena hden).trans
    (div_le_div_of_nonneg_right hpow (by positivity))

theorem arctan_q_upper : Real.arctan (6083553444 / 10000000000 : ℝ) <
    (5465404961 / 10000000000 : ℝ) := by
  let q : ℝ := 6083553444 / 10000000000
  have hq0 : 0 ≤ q := by norm_num [q]
  have hq1 : q ≤ 1 := by norm_num [q]
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    norm_num [q]
  have hsum := Real.hasSum_arctan hqnorm
  have hlim : Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * atanTerm q i)
      atTop (nhds (Real.arctan q)) := by
    simpa [atanTerm, div_eq_mul_inv, mul_assoc] using hsum.tendsto_sum_nat
  have hupper := (atanTerm_antitone hq0 hq1).tendsto_le_alternating_series hlim 12
  have hpartial : (∑ i ∈ range (2 * 12 + 1), (-1 : ℝ) ^ i * atanTerm q i) <
      (5465404961 / 10000000000 : ℝ) := by
    norm_num [q, atanTerm, Finset.sum_range_succ]
  exact hupper.trans_lt hpartial

theorem sqrt_y_bounds :
    (8218880702 / 10000000000 : ℝ) < Real.sqrt poitouY ∧
      Real.sqrt poitouY < (8218880703 / 10000000000 : ℝ) := by
  constructor
  · rw [Real.lt_sqrt (by norm_num [poitouY])]
    norm_num [poitouY]
  · rw [Real.sqrt_lt' (by norm_num)]
    norm_num [poitouY]

theorem arctan_two_sqrt_y_lower :
    (10242558306 / 10000000000 : ℝ) <
      Real.arctan (2 * Real.sqrt poitouY) := by
  let s := Real.sqrt poitouY
  let q : ℝ := 6083553444 / 10000000000
  have hspos : 0 < s := Real.sqrt_pos.2 (by norm_num [poitouY])
  have hslow : (8218880702 / 10000000000 : ℝ) < s := sqrt_y_bounds.1
  have htpos : 0 < (2 * s)⁻¹ := by positivity
  have htq : (2 * s)⁻¹ < q := by
    rw [inv_lt_iff_one_lt_mul₀' (by positivity)]
    dsimp [q]
    nlinarith
  have hatanInv : Real.arctan ((2 * s)⁻¹) =
      Real.pi / 2 - Real.arctan (2 * s) := by
    have h := Real.arctan_inv_of_pos (x := 2 * s) (by positivity)
    simpa using h
  have hatanSmall : Real.arctan ((2 * s)⁻¹) <
      (5465404961 / 10000000000 : ℝ) := by
    exact (Real.arctan_strictMono htq).trans (by simpa [q] using arctan_q_upper)
  have hpi := Real.pi_gt_d20
  rw [hatanInv] at hatanSmall
  change (10242558306 / 10000000000 : ℝ) < Real.arctan (2 * s)
  norm_num at hpi ⊢
  linarith

theorem poitou_coefficient_lower :
    (8323706046 / 1000000000 : ℝ) <
      (3 / poitouY + 12 / 5) / Real.sqrt poitouY := by
  have hspos : 0 < Real.sqrt poitouY := Real.sqrt_pos.2 (by norm_num [poitouY])
  have hsup : Real.sqrt poitouY < (8218880703 / 10000000000 : ℝ) :=
    sqrt_y_bounds.2
  have hnum : (0 : ℝ) ≤ 3 / poitouY + 12 / 5 := by norm_num [poitouY]
  have hdiv : (3 / poitouY + 12 / 5) / (8218880703 / 10000000000 : ℝ) <
      (3 / poitouY + 12 / 5) / Real.sqrt poitouY := by
    exact div_lt_div_of_pos_left (by norm_num [poitouY]) hspos hsup
  have hrat : (8323706046 / 1000000000 : ℝ) <
      (3 / poitouY + 12 / 5) / (8218880703 / 10000000000 : ℝ) := by
    norm_num [poitouY]
  exact hrat.trans hdiv

theorem poitouLClosed_y_upper :
    poitouLClosed poitouY <
      (2105281197815083333790761031 / 6164616377500000000000000000 : ℝ) := by
  have hlog : Real.log (1 + 4 * poitouY) <
      (1308873215 / 1000000000 : ℝ) := by
    convert log_1851_div_500_upper using 1 <;> norm_num [poitouY]
  have hP : 0 < 3 / (80 * poitouY ^ 3) + 3 / (4 * poitouY ^ 2) := by
    norm_num [poitouY]
  have hlogmul :
      (3 / (80 * poitouY ^ 3) + 3 / (4 * poitouY ^ 2)) *
          Real.log (1 + 4 * poitouY) <
        (3 / (80 * poitouY ^ 3) + 3 / (4 * poitouY ^ 2)) *
          (1308873215 / 1000000000 : ℝ) :=
    mul_lt_mul_of_pos_left hlog hP
  have hC := poitou_coefficient_lower
  have hA := arctan_two_sqrt_y_lower
  have hprod :
      (8323706046 / 1000000000 : ℝ) *
          (10242558306 / 10000000000 : ℝ) <
        ((3 / poitouY + 12 / 5) / Real.sqrt poitouY) *
          Real.arctan (2 * Real.sqrt poitouY) := by
    have hfirst :
        (8323706046 / 1000000000 : ℝ) * (10242558306 / 10000000000 : ℝ) <
          ((3 / poitouY + 12 / 5) / Real.sqrt poitouY) *
            (10242558306 / 10000000000 : ℝ) :=
      mul_lt_mul_of_pos_right hC (by norm_num)
    have hsecond :
        ((3 / poitouY + 12 / 5) / Real.sqrt poitouY) *
            (10242558306 / 10000000000 : ℝ) <
          ((3 / poitouY + 12 / 5) / Real.sqrt poitouY) *
            Real.arctan (2 * Real.sqrt poitouY) :=
      mul_lt_mul_of_pos_left hA (by positivity)
    exact hfirst.trans hsecond
  dsimp [poitouLClosed]
  norm_num [poitouY] at hlogmul hprod ⊢
  linarith

theorem log_four_pi_lower :
    (253102424 / 100000000 : ℝ) < Real.log (4 * Real.pi) := by
  let q : ℝ := 125663706 / 10000000
  let z : ℝ := (16 - q) / (16 + q)
  have hq0 : 0 < q := by norm_num [q]
  have hz0 : 0 ≤ z := by norm_num [z, q]
  have hz1 : z < 1 := by norm_num [z, q]
  have hseries := Real.log_div_le_sum_range_add hz0 hz1 5
  have hratio : (1 + z) / (1 - z) = 16 / q := by
    norm_num [z, q]
  rw [hratio] at hseries
  have hseriesUpper :
      2 * ((∑ i ∈ range 5, z ^ (2 * i + 1) / (2 * i + 1)) +
        z ^ (11 : ℕ) / (1 - z ^ 2)) <
        (2415644812 / 10000000000 : ℝ) := by
    norm_num [z, q, Finset.sum_range_succ]
  have hlogRatio :
      Real.log (16 / q) < (2415644812 / 10000000000 : ℝ) :=
    by nlinarith [hseries, hseriesUpper]
  have hlogSixteen : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlogQ : Real.log q = Real.log 16 - Real.log (16 / q) := by
    rw [Real.log_div (by norm_num : (16 : ℝ) ≠ 0) hq0.ne']
    ring
  have hlogTwo := Real.log_two_gt_d9
  have hqPi : q < 4 * Real.pi := by
    dsimp [q]
    nlinarith [Real.pi_gt_d20]
  have hmono : Real.log q < Real.log (4 * Real.pi) :=
    Real.log_lt_log hq0 hqPi
  rw [hlogQ, hlogSixteen] at hmono
  linarith

theorem log_14083_div_1000_upper :
    Real.log (14083 / 1000 : ℝ) <
      (26449684 / 10000000 : ℝ) := by
  let z : ℝ := 1917 / 30083
  have hz0 : 0 ≤ z := by norm_num [z]
  have hz1 : z < 1 := by norm_num [z]
  have hseries := Real.sum_range_le_log_div hz0 hz1 3
  have hratio : (1 + z) / (1 - z) = (16000 / 14083 : ℝ) := by
    norm_num [z]
  rw [hratio] at hseries
  have hseriesLower :
      (1276203232 / 10000000000 : ℝ) <
        2 * ∑ i ∈ range 3, z ^ (2 * i + 1) / (2 * i + 1) := by
    norm_num [z, Finset.sum_range_succ]
  have hlogRatio :
      (1276203232 / 10000000000 : ℝ) <
        Real.log (16000 / 14083 : ℝ) :=
    by nlinarith [hseriesLower, hseries]
  have hlogSixteen : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlogTarget :
      Real.log (14083 / 1000 : ℝ) =
        Real.log 16 - Real.log (16000 / 14083 : ℝ) := by
    have htarget : (14083 / 1000 : ℝ) = 16 / (16000 / 14083) := by
      norm_num
    rw [htarget, Real.log_div (by norm_num : (16 : ℝ) ≠ 0) (by norm_num)]
  rw [hlogTarget, hlogSixteen]
  linarith [Real.log_two_lt_d9]

theorem poitou_degree_eleven_correction_upper :
    12 * Real.pi / (55 * Real.sqrt poitouY) <
      (833980225 / 1000000000 : ℝ) := by
  have hs := sqrt_y_bounds.1
  have hspos : 0 < Real.sqrt poitouY :=
    Real.sqrt_pos.2 (by norm_num [poitouY])
  have hpi := Real.pi_lt_d20
  apply (div_lt_iff₀ (by positivity : 0 < 55 * Real.sqrt poitouY)).2
  have hrat :
      12 * (3.14159265358979323847 : ℝ) <
        (833980225 / 1000000000 : ℝ) *
          (55 * (8218880702 / 10000000000 : ℝ)) := by
    norm_num
  nlinarith

/-- Once the `L₁` sum is bounded, all remaining numerical inequalities for
the optimized degree-eleven row are kernel proofs. -/
theorem poitou_degree_eleven_log_target
    (hL1 : PoitouL1UpperCertificate) :
    Real.log (14083 / 1000 : ℝ) <
      Real.eulerMascheroniConstant + Real.log (4 * Real.pi) + 1 -
        poitouL1 poitouY - 12 * Real.pi / (55 * Real.sqrt poitouY) := by
  have hγ := EulerMascheroni.gamma_lower_strong
  have hlog := log_four_pi_lower
  have htarget := log_14083_div_1000_upper
  have hcorr := poitou_degree_eleven_correction_upper
  dsimp [PoitouL1UpperCertificate] at hL1
  norm_num at hγ hlog htarget hcorr hL1 ⊢
  linarith

/-- The specialized Poitou formula and the remaining `L₁` certificate imply
the exact degree-eleven interface used by Section 4. -/
theorem degreeElevenRootDiscriminantInput_of_poitou
    (hFormula : PoitouDegreeElevenFormulaInput)
    (hL1 : PoitouL1UpperCertificate) :
    DegreeElevenRootDiscriminantInput := by
  intro K hreal hdegree
  have hsource := hFormula K hreal hdegree
  have htarget := poitou_degree_eleven_log_target hL1
  have hlog :
      (11 : ℝ) * Real.log (14083 / 1000 : ℝ) <
        Real.log (((|K.discriminant| : ℤ) : ℝ)) := by
    nlinarith
  have hDpos : 0 < (((|K.discriminant| : ℤ) : ℝ)) := by
    have hne : K.discriminant ≠ 0 := NumberField.discr_ne_zero K.1
    exact_mod_cast (abs_pos.mpr hne : (0 : ℤ) < |K.discriminant|)
  have hexp := Real.exp_lt_exp.mpr hlog
  have hleft :
      Real.exp ((11 : ℝ) * Real.log (14083 / 1000 : ℝ)) =
        (14083 / 1000 : ℝ) ^ (11 : ℕ) := by
    change Real.exp (((11 : ℕ) : ℝ) * Real.log (14083 / 1000 : ℝ)) = _
    rw [Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 14083 / 1000)]
  rw [hleft, Real.exp_log hDpos] at hexp
  simpa using hexp

end
end TraceEuclidean.PoitouDegreeEleven
