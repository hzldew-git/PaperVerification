import TraceEuclidean.V15GeneralPowerIndex
import TraceEuclidean.V15AnalyticTable

/-!
# Explicit degree-five and degree-seven Hunter boxes

This module specializes the general Hunter construction to root discriminant
at most `14` in the two prime degrees needed by the Voight enumeration.  It
uses elementary rational radii, proves the corresponding ball inequalities,
and records explicit uniform bounds for every polynomial coefficient.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

/-- Radius `6` satisfies the degree-five Hunter ball inequality at root
discriminant `14`. -/
theorem v15_degreeFive_hunterBall_numerical :
    ((14 : ℝ) ^ 5) * (((2 : ℝ) ^ 4) ^ 2) <
      (5 : ℝ) *
        (euclideanUnitBallVolume 4 * (6 : ℝ) ^ 4) ^ 2 := by
  rw [mul_pow, v15_unitBallVolume_sq_closed]
  norm_num [v15UnitBallSquareCoefficient, v15PiExponent]
  have hpi := Real.pi_gt_three
  nlinarith [sq_nonneg (Real.pi ^ 2 - 81 / 8)]

/-- Radius `7` satisfies the degree-seven Hunter ball inequality at root
discriminant `14`. -/
theorem v15_degreeSeven_hunterBall_numerical :
    ((14 : ℝ) ^ 7) * (((2 : ℝ) ^ 6) ^ 2) <
      (7 : ℝ) *
        (euclideanUnitBallVolume 6 * (7 : ℝ) ^ 6) ^ 2 := by
  rw [mul_pow, v15_unitBallVolume_sq_closed]
  norm_num [v15UnitBallSquareCoefficient, v15PiExponent]
  have hpi := Real.pi_gt_three
  have hpi6 : (3 : ℝ) ^ 6 < Real.pi ^ 6 :=
    pow_lt_pow_left₀ hpi (by norm_num) (by norm_num)
  nlinarith

/-- The general Vieta root estimate gives this explicit degree-five
coefficient bound. -/
theorem v15_degreeFive_hunterCoefficientBound :
    v15HunterCoefficientBound 5 180 ≤ 7593750 := by
  have hroot : v15HunterRootBound 5 180 ≤ 15 := by
    rw [v15HunterRootBound]
    norm_num
    exact (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  have hmax : max (v15HunterRootBound 5 180) 1 ≤ 15 :=
    max_le hroot (by norm_num)
  rw [v15HunterCoefficientBound]
  calc
    max (v15HunterRootBound 5 180) 1 ^ 5 *
        Nat.choose 5 (5 / 2) ≤
      (15 : ℝ) ^ 5 * Nat.choose 5 (5 / 2) := by
        gcongr
    _ = 7593750 := by norm_num [Nat.choose]

/-- The general Vieta root estimate gives this explicit degree-seven
coefficient bound. -/
theorem v15_degreeSeven_hunterCoefficientBound :
    v15HunterCoefficientBound 7 343 ≤ 44800000000 := by
  have hroot : v15HunterRootBound 7 343 ≤ 20 := by
    rw [v15HunterRootBound]
    norm_num
    exact (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  have hmax : max (v15HunterRootBound 7 343) 1 ≤ 20 :=
    max_le hroot (by norm_num)
  rw [v15HunterCoefficientBound]
  calc
    max (v15HunterRootBound 7 343) 1 ^ 7 *
        Nat.choose 7 (7 / 2) ≤
      (20 : ℝ) ^ 7 * Nat.choose 7 (7 / 2) := by
        gcongr
    _ = 44800000000 := by norm_num [Nat.choose]

/-- Every coefficient of a degree-five root-discriminant-14 Hunter candidate
lies in the displayed integer interval. -/
theorem v15_degreeFive_hunterCandidate_coeff_bound
    {f : ℤ[X]} (h : V15HunterPolynomialCandidate 5 180 f)
    (i : ℕ) :
    ‖(f.coeff i : ℝ)‖ ≤ 7593750 :=
  (v15_hunterPolynomialCandidate_coeff_bound (by norm_num) h i).trans
    v15_degreeFive_hunterCoefficientBound

/-- Every coefficient of a degree-seven root-discriminant-14 Hunter candidate
lies in the displayed integer interval. -/
theorem v15_degreeSeven_hunterCandidate_coeff_bound
    {f : ℤ[X]} (h : V15HunterPolynomialCandidate 7 343 f)
    (i : ℕ) :
    ‖(f.coeff i : ℝ)‖ ≤ 44800000000 :=
  (v15_hunterPolynomialCandidate_coeff_bound (by norm_num) h i).trans
    v15_degreeSeven_hunterCoefficientBound

/-- The complete degree-five Hunter candidate set at this bound is finite. -/
theorem v15_degreeFive_hunterCandidates_finite :
    Set.Finite {f : ℤ[X] |
      V15HunterPolynomialCandidate 5 180 f} :=
  v15_hunterPolynomialCandidates_finite (by norm_num) 180

/-- The complete degree-seven Hunter candidate set at this bound is finite. -/
theorem v15_degreeSeven_hunterCandidates_finite :
    Set.Finite {f : ℤ[X] |
      V15HunterPolynomialCandidate 7 343 f} :=
  v15_hunterPolynomialCandidates_finite (by norm_num) 343

/-- Every totally real quintic field of root discriminant at most `14`
admits a polynomial in the finite degree-five Hunter candidate set. -/
theorem v15_exists_degreeFive_hunterCandidate_of_discriminant_le
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 5)
    (hdisc :
      ((|NumberField.discr K| : ℤ) : ℝ) ≤ (14 : ℝ) ^ 5) :
    ∃ f : ℤ[X], V15HunterPolynomialCandidate 5 180 f := by
  have hball :
      ((|NumberField.discr K| : ℤ) : ℝ) *
          (((2 : ℝ) ^ 4) ^ 2) <
        (5 : ℝ) *
          (euclideanUnitBallVolume 4 * (6 : ℝ) ^ 4) ^ 2 :=
    (mul_le_mul_of_nonneg_right hdisc (by positivity)).trans_lt
      v15_degreeFive_hunterBall_numerical
  obtain ⟨f, hf⟩ :=
    v15_exists_hunterPolynomialCandidate_of_hunterBall K hreal
      (by simpa using hdegree) (by norm_num) (by norm_num)
      6 (by norm_num) (by
        convert hball using 1
        all_goals norm_num)
  refine ⟨f, ?_⟩
  convert hf using 1
  all_goals norm_num

/-- Every totally real septic field of root discriminant at most `14`
admits a polynomial in the finite degree-seven Hunter candidate set. -/
theorem v15_exists_degreeSeven_hunterCandidate_of_discriminant_le
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 7)
    (hdisc :
      ((|NumberField.discr K| : ℤ) : ℝ) ≤ (14 : ℝ) ^ 7) :
    ∃ f : ℤ[X], V15HunterPolynomialCandidate 7 343 f := by
  have hball :
      ((|NumberField.discr K| : ℤ) : ℝ) *
          (((2 : ℝ) ^ 6) ^ 2) <
        (7 : ℝ) *
          (euclideanUnitBallVolume 6 * (7 : ℝ) ^ 6) ^ 2 :=
    (mul_le_mul_of_nonneg_right hdisc (by positivity)).trans_lt
      v15_degreeSeven_hunterBall_numerical
  obtain ⟨f, hf⟩ :=
    v15_exists_hunterPolynomialCandidate_of_hunterBall K hreal
      (by simpa using hdegree) (by norm_num) (by norm_num)
      7 (by norm_num) (by
        convert hball using 1
        all_goals norm_num)
  refine ⟨f, ?_⟩
  convert hf using 1
  all_goals norm_num

/-- Every totally real quintic field of root discriminant at most `14`
lands in the finite Hunter search together with its primitive generator and
strictly positive integral index. -/
theorem v15_exists_degreeFive_hunterFieldCandidate_of_discriminant_le
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 5)
    (hdisc :
      ((|NumberField.discr K| : ℤ) : ℝ) ≤ (14 : ℝ) ^ 5) :
    ∃ f ∈ v15HunterPolynomialCandidates 5 (by norm_num) 180,
      V15HunterFieldPolynomialCandidate K 5 180 f := by
  have hball :
      ((|NumberField.discr K| : ℤ) : ℝ) *
          (((2 : ℝ) ^ 4) ^ 2) <
        (5 : ℝ) *
          (euclideanUnitBallVolume 4 * (6 : ℝ) ^ 4) ^ 2 :=
    (mul_le_mul_of_nonneg_right hdisc (by positivity)).trans_lt
      v15_degreeFive_hunterBall_numerical
  obtain ⟨f, hf⟩ :=
    v15_exists_hunterFieldPolynomialCandidate_of_hunterBall K hreal
      (by simpa using hdegree) (by norm_num) (by norm_num)
      6 (by norm_num) (by
        convert hball using 1
        all_goals norm_num)
  have hf' : V15HunterFieldPolynomialCandidate K 5 180 f := by
    convert hf using 1
    all_goals norm_num
  exact ⟨f,
    (v15_mem_hunterPolynomialCandidates_iff
      5 (by norm_num) 180 f).2 hf'.1,
    hf'⟩

/-- Every totally real septic field of root discriminant at most `14`
lands in the finite Hunter search together with its primitive generator and
strictly positive integral index. -/
theorem v15_exists_degreeSeven_hunterFieldCandidate_of_discriminant_le
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 7)
    (hdisc :
      ((|NumberField.discr K| : ℤ) : ℝ) ≤ (14 : ℝ) ^ 7) :
    ∃ f ∈ v15HunterPolynomialCandidates 7 (by norm_num) 343,
      V15HunterFieldPolynomialCandidate K 7 343 f := by
  have hball :
      ((|NumberField.discr K| : ℤ) : ℝ) *
          (((2 : ℝ) ^ 6) ^ 2) <
        (7 : ℝ) *
          (euclideanUnitBallVolume 6 * (7 : ℝ) ^ 6) ^ 2 :=
    (mul_le_mul_of_nonneg_right hdisc (by positivity)).trans_lt
      v15_degreeSeven_hunterBall_numerical
  obtain ⟨f, hf⟩ :=
    v15_exists_hunterFieldPolynomialCandidate_of_hunterBall K hreal
      (by simpa using hdegree) (by norm_num) (by norm_num)
      7 (by norm_num) (by
        convert hball using 1
        all_goals norm_num)
  have hf' : V15HunterFieldPolynomialCandidate K 7 343 f := by
    convert hf using 1
    all_goals norm_num
  exact ⟨f,
    (v15_mem_hunterPolynomialCandidates_iff
      7 (by norm_num) 343 f).2 hf'.1,
    hf'⟩

end

end TraceEuclidean
