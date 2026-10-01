import TraceEuclidean.HunterDiscriminantBoxes
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Hunter reduction at the exact degree-seven minimum

For the contradiction range `|D_K| < 20134393`, a radius of `263/50`
reduces Hunter's spread bound from `343` to the integer bound `194`.  This
module records the resulting smaller coefficient box and retains the exact
power-order index relation needed by the finite search.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

/-- The rational radius `263/50` satisfies Hunter's six-dimensional ball
inequality throughout the degree-seven contradiction range. -/
theorem degreeSevenMinimum_hunterBall_numerical :
    (20134393 : ℝ) * (((2 : ℝ) ^ 6) ^ 2) <
      (7 : ℝ) *
        (euclideanUnitBallVolume 6 * (263 / 50 : ℝ) ^ 6) ^ 2 := by
  rw [mul_pow, unitBallVolume_sq_closed]
  norm_num [unitBallSquareCoefficient, piExponent]
  have hpi := Real.pi_gt_d20
  have hpi6 : (3.14159265358979323846 : ℝ) ^ 6 < Real.pi ^ 6 :=
    pow_lt_pow_left₀ hpi (by norm_num) (by norm_num)
  nlinarith

/-- The exact rational spread produced by the radius is strictly below the
integer bound used by the finite polynomial search. -/
theorem degreeSevenMinimum_spread_lt :
    (7 : ℝ) * (263 / 50 : ℝ) ^ 2 < 194 := by
  norm_num

/-- Every totally real septic field below the claimed minimum produces a
field-realizable Hunter polynomial with spread below `194`. -/
theorem exists_degreeSevenMinimum_hunterFieldCandidate
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 7)
    (hdisc :
      ((|NumberField.discr K| : ℤ) : ℝ) < 20134393) :
    ∃ f : ℤ[X], HunterFieldPolynomialCandidate K 7 194 f := by
  have hball :
      ((|NumberField.discr K| : ℤ) : ℝ) *
          (((2 : ℝ) ^ 6) ^ 2) <
        (7 : ℝ) *
          (euclideanUnitBallVolume 6 * (263 / 50 : ℝ) ^ 6) ^ 2 :=
    (mul_lt_mul_of_pos_right hdisc (by positivity)).trans
      degreeSevenMinimum_hunterBall_numerical
  obtain ⟨f, hf, hfield⟩ :=
    exists_hunterFieldPolynomialCandidate_of_hunterBall
      K hreal (by simpa using hdegree) (by norm_num) (by norm_num)
      (263 / 50) (by norm_num) (by
        convert hball using 1
        all_goals norm_num)
  rcases hf with
    ⟨hmonic, hirreducible, hdegreeF, hsplits, htrace0, htraceHalf,
      hspread⟩
  have hspreadBound :
      ((6 : ℝ) + 1) * (263 / 50 : ℝ) ^ 2 < 194 := by
    norm_num
  exact ⟨f,
    ⟨hmonic, hirreducible, hdegreeF, hsplits, htrace0, htraceHalf,
      hspread.trans hspreadBound⟩,
    hfield⟩

/-- The roots in the sharpened degree-seven search have absolute value at
most `16`. -/
theorem degreeSevenMinimum_hunterRootBound :
    hunterRootBound 7 194 ≤ 16 := by
  rw [hunterRootBound]
  norm_num
  exact (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩

/-- The second signed coefficient is forced into the interval `[-13,4]`. -/
theorem degreeSevenMinimum_secondCoefficient_bounds
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f) :
    -13 ≤ f.coeff 5 ∧ f.coeff 5 ≤ 4 := by
  let s1 : ℤ := -f.coeff 6
  let s2 : ℤ := f.coeff 5
  have hs1nonneg : 0 ≤ s1 := h.2.2.2.2.1
  have hs1half : 2 * s1 ≤ 7 := h.2.2.2.2.2.1
  have hs1le : s1 ≤ 3 := by omega
  have hsum := hunter_roots_sum_sq_eq_coefficients
    7 (by norm_num) f h.1 h.2.2.1 h.2.2.2.1
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
  change (((generalSpread 7 s1 s2 : ℤ) : ℝ)) < 194 at hspread
  have hspreadInt : generalSpread 7 s1 s2 < (194 : ℤ) := by
    exact_mod_cast hspread
  have hlower : -13 ≤ s2 := by
    have hmul : -194 < 14 * s2 := by
      simp [generalSpread] at hspreadInt
      nlinarith [sq_nonneg s1]
    omega
  have hsq : s1 ^ 2 ≤ 9 := by nlinarith
  have hupper : s2 ≤ 4 := by
    have : 2 * s2 ≤ 9 := htwice.trans hsq
    omega
  exact ⟨by simpa [s2] using hlower, by simpa [s2] using hupper⟩

/-- The normalized trace coefficient remains in `[-3,0]`. -/
theorem degreeSevenMinimum_traceCoefficient_bounds
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f) :
    -3 ≤ f.coeff 6 ∧ f.coeff 6 ≤ 0 := by
  have hnonneg := h.2.2.2.2.1
  have hhalf := h.2.2.2.2.2.1
  norm_num at hnonneg hhalf
  omega

/-- Lower endpoints of the sharpened degree-seven coefficient box. -/
def degreeSevenMinimumLower : Fin 8 → ℤ :=
  ![-268435456, -117440512, -22020096, -2293760,
    -143360, -13, -3, 1]

/-- Upper endpoints of the sharpened degree-seven coefficient box. -/
def degreeSevenMinimumUpper : Fin 8 → ℤ :=
  ![268435456, 117440512, 22020096, 2293760,
    143360, 4, 0, 1]

/-- Executable interval box for the exact-minimum contradiction search. -/
def degreeSevenMinimumBox : Finset ℤ[X] :=
  integralPolynomialIntervalBox 7
    degreeSevenMinimumLower degreeSevenMinimumUpper

/-- Every sharpened Hunter candidate belongs to the displayed interval box. -/
theorem degreeSevenMinimum_candidate_mem_box
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f) :
    f ∈ degreeSevenMinimumBox := by
  rw [degreeSevenMinimumBox,
    mem_integralPolynomialIntervalBox_iff]
  have hs2 := degreeSevenMinimum_secondCoefficient_bounds h
  have hs1 := degreeSevenMinimum_traceCoefficient_bounds h
  have hrootNonneg : 0 ≤ hunterRootBound 7 194 :=
    Real.sqrt_nonneg _
  have hrootLe : hunterRootBound 7 194 ≤ 16 :=
    degreeSevenMinimum_hunterRootBound
  have hpow (n : ℕ) :
      hunterRootBound 7 194 ^ n ≤ (16 : ℝ) ^ n :=
    pow_le_pow_left₀ hrootNonneg hrootLe n
  have hlead : f.coeff 7 = 1 := by
    have hc := h.1.coeff_natDegree
    rwa [h.2.2.1] at hc
  refine ⟨h.2.2.1.le, ?_⟩
  intro i
  fin_cases i
  · have hb := hunterPolynomialCandidate_coeff_bound_at
      (d := 7) (B := 194) (f := f) (by norm_num) h 0 (by norm_num)
    have hb' : ‖(f.coeff 0 : ℝ)‖ ≤ (1 : ℝ) * 16 ^ 7 :=
      calc
        _ ≤ (1 : ℝ) * hunterRootBound 7 194 ^ 7 := by
          simpa [Nat.choose] using hb
        _ ≤ (1 : ℝ) * 16 ^ 7 :=
          mul_le_mul_of_nonneg_left (hpow 7) (by norm_num)
    norm_num [Nat.choose, Real.norm_eq_abs] at hb'
    simpa [degreeSevenMinimumLower, degreeSevenMinimumUpper] using
      (show -268435456 ≤ f.coeff 0 ∧ f.coeff 0 ≤ 268435456 by
        exact_mod_cast (abs_le.mp hb'))
  · have hb := hunterPolynomialCandidate_coeff_bound_at
      (d := 7) (B := 194) (f := f) (by norm_num) h 1 (by norm_num)
    have hb' : ‖(f.coeff 1 : ℝ)‖ ≤ (7 : ℝ) * 16 ^ 6 :=
      calc
        _ ≤ (7 : ℝ) * hunterRootBound 7 194 ^ 6 := by
          simpa [Nat.choose] using hb
        _ ≤ (7 : ℝ) * 16 ^ 6 :=
          mul_le_mul_of_nonneg_left (hpow 6) (by norm_num)
    norm_num [Nat.choose, Real.norm_eq_abs] at hb'
    simpa [degreeSevenMinimumLower, degreeSevenMinimumUpper] using
      (show -117440512 ≤ f.coeff 1 ∧ f.coeff 1 ≤ 117440512 by
        exact_mod_cast (abs_le.mp hb'))
  · have hb := hunterPolynomialCandidate_coeff_bound_at
      (d := 7) (B := 194) (f := f) (by norm_num) h 2 (by norm_num)
    have hb' : ‖(f.coeff 2 : ℝ)‖ ≤ (21 : ℝ) * 16 ^ 5 :=
      calc
        _ ≤ (21 : ℝ) * hunterRootBound 7 194 ^ 5 := by
          simpa [Nat.choose] using hb
        _ ≤ (21 : ℝ) * 16 ^ 5 :=
          mul_le_mul_of_nonneg_left (hpow 5) (by norm_num)
    norm_num [Nat.choose, Real.norm_eq_abs] at hb'
    simpa [degreeSevenMinimumLower, degreeSevenMinimumUpper] using
      (show -22020096 ≤ f.coeff 2 ∧ f.coeff 2 ≤ 22020096 by
        exact_mod_cast (abs_le.mp hb'))
  · have hb := hunterPolynomialCandidate_coeff_bound_at
      (d := 7) (B := 194) (f := f) (by norm_num) h 3 (by norm_num)
    have hb' : ‖(f.coeff 3 : ℝ)‖ ≤ (35 : ℝ) * 16 ^ 4 :=
      calc
        _ ≤ (35 : ℝ) * hunterRootBound 7 194 ^ 4 := by
          simpa [Nat.choose] using hb
        _ ≤ (35 : ℝ) * 16 ^ 4 :=
          mul_le_mul_of_nonneg_left (hpow 4) (by norm_num)
    norm_num [Nat.choose, Real.norm_eq_abs] at hb'
    simpa [degreeSevenMinimumLower, degreeSevenMinimumUpper] using
      (show -2293760 ≤ f.coeff 3 ∧ f.coeff 3 ≤ 2293760 by
        exact_mod_cast (abs_le.mp hb'))
  · have hb := hunterPolynomialCandidate_coeff_bound_at
      (d := 7) (B := 194) (f := f) (by norm_num) h 4 (by norm_num)
    have hb' : ‖(f.coeff 4 : ℝ)‖ ≤ (35 : ℝ) * 16 ^ 3 :=
      calc
        _ ≤ (35 : ℝ) * hunterRootBound 7 194 ^ 3 := by
          simpa [Nat.choose] using hb
        _ ≤ (35 : ℝ) * 16 ^ 3 :=
          mul_le_mul_of_nonneg_left (hpow 3) (by norm_num)
    norm_num [Nat.choose, Real.norm_eq_abs] at hb'
    simpa [degreeSevenMinimumLower, degreeSevenMinimumUpper] using
      (show -143360 ≤ f.coeff 4 ∧ f.coeff 4 ≤ 143360 by
        exact_mod_cast (abs_le.mp hb'))
  · simpa [degreeSevenMinimumLower, degreeSevenMinimumUpper] using hs2
  · simpa [degreeSevenMinimumLower, degreeSevenMinimumUpper] using hs1
  · simp [degreeSevenMinimumLower, degreeSevenMinimumUpper, hlead]

end

end TraceEuclidean
