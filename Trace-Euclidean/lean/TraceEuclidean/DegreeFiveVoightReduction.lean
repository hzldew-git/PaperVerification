import TraceEuclidean.HunterPrimeDegreeBoxes
import TraceEuclidean.VoightRollePruning
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Degree-five Voight reduction below the first discriminant

This file sharpens the Hunter construction under the contradiction
hypothesis `|disc K| < 14641`.  The smaller radius produces a primitive
quintic polynomial with exact spread bound `67`; this is the input for the
finite Rolle search rather than the much larger root-discriminant-14 box.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

/-- The radius `sqrt (67 / 5)` satisfies the degree-five Hunter ball
inequality for every discriminant at most `14640`. -/
theorem degreeFive_minimumHunterBall_numerical :
    (14640 : ℝ) * (((2 : ℝ) ^ 4) ^ 2) <
      (5 : ℝ) *
        (euclideanUnitBallVolume 4 *
          (Real.sqrt (67 / 5 : ℝ)) ^ 4) ^ 2 := by
  have hpow :
      (Real.sqrt (67 / 5 : ℝ)) ^ 4 = (67 / 5 : ℝ) ^ 2 := by
    calc
      (Real.sqrt (67 / 5 : ℝ)) ^ 4 =
          ((Real.sqrt (67 / 5 : ℝ)) ^ 2) ^ 2 := by ring
      _ = (67 / 5 : ℝ) ^ 2 := by
        rw [Real.sq_sqrt]
        norm_num
  rw [hpow, mul_pow, unitBallVolume_sq_closed]
  norm_num [unitBallSquareCoefficient, piExponent]
  have hpi := Real.pi_gt_d2
  have hpi4 : (3.14 : ℝ) ^ 4 < Real.pi ^ 4 :=
    pow_lt_pow_left₀ hpi (by norm_num) (by norm_num)
  nlinarith

/-- Every totally real quintic field below discriminant `14641` has a
primitive integral Hunter polynomial with spread strictly less than `67`.
The accompanying field-candidate structure retains the generator and the
exact power-basis index equation. -/
theorem exists_degreeFive_hunterFieldCandidate_of_discriminant_lt_14641
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 5)
    (hdisc :
      ((|NumberField.discr K| : ℤ) : ℝ) < 14641) :
    ∃ f : ℤ[X],
      HunterFieldPolynomialCandidate K 5 67 f := by
  have hdiscInt : |NumberField.discr K| < (14641 : ℤ) := by
    exact_mod_cast hdisc
  have hdiscLeInt : |NumberField.discr K| ≤ (14640 : ℤ) := by
    omega
  have hdiscLe :
      ((|NumberField.discr K| : ℤ) : ℝ) ≤ 14640 := by
    exact_mod_cast hdiscLeInt
  have hball :
      ((|NumberField.discr K| : ℤ) : ℝ) *
          (((2 : ℝ) ^ 4) ^ 2) <
        (5 : ℝ) *
          (euclideanUnitBallVolume 4 *
            (Real.sqrt (67 / 5 : ℝ)) ^ 4) ^ 2 :=
    (mul_le_mul_of_nonneg_right hdiscLe (by positivity)).trans_lt
      degreeFive_minimumHunterBall_numerical
  have hr : 0 < Real.sqrt (67 / 5 : ℝ) := by positivity
  obtain ⟨f, hf⟩ :=
    exists_hunterFieldPolynomialCandidate_of_hunterBall
      K hreal (by simpa using hdegree) (by norm_num) (by norm_num)
      (Real.sqrt (67 / 5 : ℝ)) hr (by
        convert hball using 1
        all_goals norm_num)
  have hB :
      ((4 : ℝ) + 1) * (Real.sqrt (67 / 5 : ℝ)) ^ 2 = 67 := by
    rw [Real.sq_sqrt]
    all_goals norm_num
  refine ⟨f, ?_⟩
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, hB] using hf

/-- The uniform root bound for the sharpened quintic Hunter polynomial is
strictly smaller than `10`. -/
theorem degreeFive_minimumHunterRootBound :
    hunterRootBound 5 67 < 10 := by
  rw [hunterRootBound]
  norm_num [max_eq_left]
  have hsqrtNonneg : 0 ≤ Real.sqrt (92 : ℝ) :=
    Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt (92 : ℝ)) ^ 2 = 92 := by
    rw [Real.sq_sqrt]
    norm_num
  nlinarith

/-- Every root of the sharpened quintic Hunter polynomial lies strictly
between the rational endpoints `-10` and `10`. -/
theorem degreeFive_minimumHunterCandidate_root_bounds
    {f : ℤ[X]} (h : HunterPolynomialCandidate 5 67 f) :
    ∀ z ∈ (f.map (algebraMap ℤ ℝ)).roots,
      (-10 : ℝ) < z ∧ z < 10 := by
  intro z hz
  have hnorm := hunterPolynomialCandidate_root_bound
    (d := 5) (B := 67) (by norm_num) h z hz
  have hnorm' : ‖z‖ < (10 : ℝ) :=
    hnorm.trans_lt degreeFive_minimumHunterRootBound
  simpa [Real.norm_eq_abs, abs_lt] using hnorm'

/-- The top two nonleading coefficients of every sharpened quintic Hunter
candidate lie in the small integer box used to start the exact Rolle search. -/
theorem degreeFive_minimumHunter_topCoefficient_bounds
    {f : ℤ[X]} (h : HunterPolynomialCandidate 5 67 f) :
    -2 ≤ f.coeff 4 ∧ f.coeff 4 ≤ 0 ∧
      -6 ≤ f.coeff 3 ∧ f.coeff 3 ≤ 2 := by
  let s1 : ℤ := -f.coeff 4
  let s2 : ℤ := f.coeff 3
  have hs1nonneg : 0 ≤ s1 := h.2.2.2.2.1
  have hs1half : 2 * s1 ≤ 5 := h.2.2.2.2.2.1
  have hs1le : s1 ≤ 2 := by omega
  have hsum := hunter_roots_sum_sq_eq_coefficients
    5 (by norm_num) f h.1 h.2.2.1 h.2.2.2.1
  change ((((f.map (algebraMap ℤ ℝ)).roots).map
    fun x => x ^ 2).sum) = (s1 : ℝ) ^ 2 - 2 * (s2 : ℝ) at hsum
  have hsumNonneg :
      0 ≤ (((f.map (algebraMap ℤ ℝ)).roots).map
        fun x => x ^ 2).sum := by
    apply Multiset.sum_nonneg
    intro y hy
    obtain ⟨x, _, rfl⟩ := Multiset.mem_map.mp hy
    exact sq_nonneg x
  rw [hsum] at hsumNonneg
  have htwiceReal : (2 : ℝ) * (s2 : ℝ) ≤ (s1 : ℝ) ^ 2 := by
    linarith
  have htwice : 2 * s2 ≤ s1 ^ 2 := by
    exact_mod_cast htwiceReal
  have hspread := h.2.2.2.2.2.2
  change (((generalSpread 5 s1 s2 : ℤ) : ℝ)) < 67 at hspread
  have hspreadInt : generalSpread 5 s1 s2 < (67 : ℤ) := by
    exact_mod_cast hspread
  have hlower : -6 ≤ s2 := by
    have hmul : -67 < 10 * s2 := by
      simp [generalSpread] at hspreadInt
      nlinarith [sq_nonneg s1]
    omega
  have hsq : s1 ^ 2 ≤ 4 := by nlinarith
  have hupper : s2 ≤ 2 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [s1] using neg_le_neg hs1le
  · simpa [s1] using neg_nonpos.mpr hs1nonneg
  · simpa [s2] using hlower
  · simpa [s2] using hupper

end

end TraceEuclidean
