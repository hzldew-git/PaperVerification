import TraceEuclidean.V15GeneralPowerIndex
import TraceEuclidean.V15HunterCoordinateBoxes
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

/-- The degree-five Hunter roots have norm at most `15`. -/
theorem v15_degreeFive_hunterRootBound :
    v15HunterRootBound 5 180 ≤ 15 := by
  rw [v15HunterRootBound]
  norm_num
  exact (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩

/-- The degree-seven Hunter roots have norm at most `20`. -/
theorem v15_degreeSeven_hunterRootBound :
    v15HunterRootBound 7 343 ≤ 20 := by
  rw [v15HunterRootBound]
  norm_num
  exact (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩

/-- The general Vieta root estimate gives this explicit degree-five
coefficient bound. -/
theorem v15_degreeFive_hunterCoefficientBound :
    v15HunterCoefficientBound 5 180 ≤ 7593750 := by
  have hmax : max (v15HunterRootBound 5 180) 1 ≤ 15 :=
    max_le v15_degreeFive_hunterRootBound (by norm_num)
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
  have hmax : max (v15HunterRootBound 7 343) 1 ≤ 20 :=
    max_le v15_degreeSeven_hunterRootBound (by norm_num)
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

/-- The sharper coordinatewise degree-five coefficient estimate. -/
theorem v15_degreeFive_hunterCandidate_coeff_bound_sharp
    {f : ℤ[X]} (h : V15HunterPolynomialCandidate 5 180 f)
    (i : ℕ) (hi : i ≤ 5) :
    ‖(f.coeff i : ℝ)‖ ≤
      (Nat.choose 5 (5 - i) : ℝ) * 15 ^ (5 - i) := by
  have hb := v15_hunterPolynomialCandidate_coeff_bound_at
    (d := 5) (B := 180) (f := f) (by norm_num) h i hi
  exact hb.trans (by
    have hrootNonneg : 0 ≤ v15HunterRootBound 5 180 :=
      Real.sqrt_nonneg _
    gcongr
    exact v15_degreeFive_hunterRootBound)

/-- The sharper coordinatewise degree-seven coefficient estimate. -/
theorem v15_degreeSeven_hunterCandidate_coeff_bound_sharp
    {f : ℤ[X]} (h : V15HunterPolynomialCandidate 7 343 f)
    (i : ℕ) (hi : i ≤ 7) :
    ‖(f.coeff i : ℝ)‖ ≤
      (Nat.choose 7 (7 - i) : ℝ) * 20 ^ (7 - i) := by
  have hb := v15_hunterPolynomialCandidate_coeff_bound_at
    (d := 7) (B := 343) (f := f) (by norm_num) h i hi
  exact hb.trans (by
    have hrootNonneg : 0 ≤ v15HunterRootBound 7 343 :=
      Real.sqrt_nonneg _
    gcongr
    exact v15_degreeSeven_hunterRootBound)

/-- The sharper executable degree-five coefficient box.  Its coordinate
radii, from constant to leading coefficient, are
`759375, 253125, 33750, 2250, 75, 1`. -/
def v15DegreeFiveHunterCoordinateBox : Finset ℤ[X] :=
  v15IntegralPolynomialCoordinateBox 5
    (v15HunterCoordinateBound 5 15)

/-- The sharper executable degree-seven coefficient box.  Its coordinate
radii, from constant to leading coefficient, are
`1280000000, 448000000, 67200000, 5600000, 280000, 8400, 140, 1`. -/
def v15DegreeSevenHunterCoordinateBox : Finset ℤ[X] :=
  v15IntegralPolynomialCoordinateBox 7
    (v15HunterCoordinateBound 7 20)

/-- Exact size of the degree-five coordinate box. -/
theorem v15_degreeFive_hunterCoordinateBox_card :
    v15DegreeFiveHunterCoordinateBox.card =
      105820520340154659628953 := by
  rw [v15DegreeFiveHunterCoordinateBox,
    v15_card_integralPolynomialCoordinateBox]
  norm_num [v15HunterCoordinateBound, Fin.prod_univ_succ, Nat.choose]

/-- Exact size of the degree-seven coordinate box. -/
theorem v15_degreeSeven_hunterCoordinateBox_card :
    v15DegreeSevenHunterCoordinateBox.card =
      27385256812699621612303428104012519835419043243 := by
  rw [v15DegreeSevenHunterCoordinateBox,
    v15_card_integralPolynomialCoordinateBox]
  norm_num [v15HunterCoordinateBound, Fin.prod_univ_succ, Nat.choose]

/-- Every degree-five Hunter candidate belongs to the sharper coordinate
box. -/
theorem v15_degreeFive_hunterCandidate_mem_coordinateBox
    {f : ℤ[X]} (h : V15HunterPolynomialCandidate 5 180 f) :
    f ∈ v15DegreeFiveHunterCoordinateBox := by
  rw [v15DegreeFiveHunterCoordinateBox,
    v15_mem_integralPolynomialCoordinateBox_iff]
  refine ⟨h.2.2.1.le, ?_⟩
  intro i
  have hb := v15_hunterPolynomialCandidate_coeff_bound_at
    (d := 5) (B := 180) (f := f) (by norm_num) h i (by omega)
  have hpow :
      v15HunterRootBound 5 180 ^ (5 - (i : ℕ)) ≤
        (15 : ℝ) ^ (5 - (i : ℕ)) := by
    gcongr
    · exact Real.sqrt_nonneg _
    · exact v15_degreeFive_hunterRootBound
  have hb' :
      |(f.coeff i : ℝ)| ≤
        (v15HunterCoordinateBound 5 15 i : ℝ) := by
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (by
      rw [v15HunterCoordinateBound]
      push_cast
      gcongr)
  constructor
  · exact_mod_cast (abs_le.mp hb').1
  · exact_mod_cast (abs_le.mp hb').2

/-- Every degree-seven Hunter candidate belongs to the sharper coordinate
box. -/
theorem v15_degreeSeven_hunterCandidate_mem_coordinateBox
    {f : ℤ[X]} (h : V15HunterPolynomialCandidate 7 343 f) :
    f ∈ v15DegreeSevenHunterCoordinateBox := by
  rw [v15DegreeSevenHunterCoordinateBox,
    v15_mem_integralPolynomialCoordinateBox_iff]
  refine ⟨h.2.2.1.le, ?_⟩
  intro i
  have hb := v15_hunterPolynomialCandidate_coeff_bound_at
    (d := 7) (B := 343) (f := f) (by norm_num) h i (by omega)
  have hpow :
      v15HunterRootBound 7 343 ^ (7 - (i : ℕ)) ≤
        (20 : ℝ) ^ (7 - (i : ℕ)) := by
    gcongr
    · exact Real.sqrt_nonneg _
    · exact v15_degreeSeven_hunterRootBound
  have hb' :
      |(f.coeff i : ℝ)| ≤
        (v15HunterCoordinateBound 7 20 i : ℝ) := by
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (by
      rw [v15HunterCoordinateBound]
      push_cast
      gcongr)
  constructor
  · exact_mod_cast (abs_le.mp hb').1
  · exact_mod_cast (abs_le.mp hb').2

/-- The second signed coefficient of a degree-five Hunter candidate lies in
the much smaller interval forced by the sum of squared roots and the strict
spread inequality. -/
theorem v15_degreeFive_hunterSecondCoefficient_bounds
    {f : ℤ[X]} (h : V15HunterPolynomialCandidate 5 180 f) :
    -17 ≤ f.coeff 3 ∧ f.coeff 3 ≤ 2 := by
  let s1 : ℤ := -f.coeff 4
  let s2 : ℤ := f.coeff 3
  have hs1nonneg : 0 ≤ s1 := h.2.2.2.2.1
  have hs1half : 2 * s1 ≤ 5 := h.2.2.2.2.2.1
  have hs1le : s1 ≤ 2 := by omega
  have hsum := v15_hunter_roots_sum_sq_eq_coefficients
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
  change (((v15GeneralSpread 5 s1 s2 : ℤ) : ℝ)) < 180 at hspread
  have hspreadInt : v15GeneralSpread 5 s1 s2 < (180 : ℤ) := by
    exact_mod_cast hspread
  have hlower : -17 ≤ s2 := by
    have hmul : -180 < 10 * s2 := by
      simp [v15GeneralSpread] at hspreadInt
      nlinarith [sq_nonneg s1]
    omega
  have hsq : s1 ^ 2 ≤ 4 := by nlinarith
  have hupper : s2 ≤ 2 := by nlinarith
  exact ⟨by simpa [s2] using hlower, by simpa [s2] using hupper⟩

/-- The corresponding degree-seven second-coefficient interval. -/
theorem v15_degreeSeven_hunterSecondCoefficient_bounds
    {f : ℤ[X]} (h : V15HunterPolynomialCandidate 7 343 f) :
    -24 ≤ f.coeff 5 ∧ f.coeff 5 ≤ 4 := by
  let s1 : ℤ := -f.coeff 6
  let s2 : ℤ := f.coeff 5
  have hs1nonneg : 0 ≤ s1 := h.2.2.2.2.1
  have hs1half : 2 * s1 ≤ 7 := h.2.2.2.2.2.1
  have hs1le : s1 ≤ 3 := by omega
  have hsum := v15_hunter_roots_sum_sq_eq_coefficients
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
  change (((v15GeneralSpread 7 s1 s2 : ℤ) : ℝ)) < 343 at hspread
  have hspreadInt : v15GeneralSpread 7 s1 s2 < (343 : ℤ) := by
    exact_mod_cast hspread
  have hlower : -24 ≤ s2 := by
    have hmul : -343 < 14 * s2 := by
      simp [v15GeneralSpread] at hspreadInt
      nlinarith [sq_nonneg s1]
    omega
  have hsq : s1 ^ 2 ≤ 9 := by nlinarith
  have htwiceBound : 2 * s2 ≤ 9 := htwice.trans hsq
  have hupper : s2 ≤ 4 := by omega
  exact ⟨by simpa [s2] using hlower, by simpa [s2] using hupper⟩

/-- The normalized degree-five trace coefficient interval. -/
theorem v15_degreeFive_hunterTraceCoefficient_bounds
    {f : ℤ[X]} (h : V15HunterPolynomialCandidate 5 180 f) :
    -2 ≤ f.coeff 4 ∧ f.coeff 4 ≤ 0 := by
  have hnonneg := h.2.2.2.2.1
  have hhalf := h.2.2.2.2.2.1
  norm_num at hnonneg hhalf
  omega

/-- The normalized degree-seven trace coefficient interval. -/
theorem v15_degreeSeven_hunterTraceCoefficient_bounds
    {f : ℤ[X]} (h : V15HunterPolynomialCandidate 7 343 f) :
    -3 ≤ f.coeff 6 ∧ f.coeff 6 ≤ 0 := by
  have hnonneg := h.2.2.2.2.1
  have hhalf := h.2.2.2.2.2.1
  norm_num at hnonneg hhalf
  omega

/-- Lower endpoints for the refined degree-five Hunter box. -/
def v15DegreeFiveHunterLower : Fin 6 → ℤ :=
  ![-759375, -253125, -33750, -17, -2, 1]

/-- Upper endpoints for the refined degree-five Hunter box. -/
def v15DegreeFiveHunterUpper : Fin 6 → ℤ :=
  ![759375, 253125, 33750, 2, 0, 1]

/-- Lower endpoints for the refined degree-seven Hunter box. -/
def v15DegreeSevenHunterLower : Fin 8 → ℤ :=
  ![-1280000000, -448000000, -67200000, -5600000,
    -280000, -24, -3, 1]

/-- Upper endpoints for the refined degree-seven Hunter box. -/
def v15DegreeSevenHunterUpper : Fin 8 → ℤ :=
  ![1280000000, 448000000, 67200000, 5600000,
    280000, 4, 0, 1]

/-- The refined degree-five box fixes monicity and incorporates the exact
trace and second-coefficient intervals. -/
def v15DegreeFiveHunterRefinedBox : Finset ℤ[X] :=
  v15IntegralPolynomialIntervalBox 5
    v15DegreeFiveHunterLower v15DegreeFiveHunterUpper

/-- The analogous refined degree-seven box. -/
def v15DegreeSevenHunterRefinedBox : Finset ℤ[X] :=
  v15IntegralPolynomialIntervalBox 7
    v15DegreeSevenHunterLower v15DegreeSevenHunterUpper

/-- Exact size of the refined degree-five box. -/
theorem v15_degreeFive_hunterRefinedBox_card :
    v15DegreeFiveHunterRefinedBox.card = 3113966442781800060 := by
  rw [v15DegreeFiveHunterRefinedBox,
    v15_card_integralPolynomialIntervalBox]
  norm_num [v15DegreeFiveHunterLower, v15DegreeFiveHunterUpper,
    Fin.prod_univ_succ, Int.toNat]

/-- Exact size of the refined degree-seven box. -/
theorem v15_degreeSeven_hunterRefinedBox_card :
    v15DegreeSevenHunterRefinedBox.card =
      224291130941773441790640579990433850560116 := by
  rw [v15DegreeSevenHunterRefinedBox,
    v15_card_integralPolynomialIntervalBox]
  norm_num [v15DegreeSevenHunterLower, v15DegreeSevenHunterUpper,
    Fin.prod_univ_succ, Int.toNat]

/-- Coordinate inequalities defining the refined degree-five interval box. -/
theorem v15_degreeFive_hunterCandidate_refined_bounds
    {f : ℤ[X]} (h : V15HunterPolynomialCandidate 5 180 f) :
    f.natDegree ≤ 5 ∧ ∀ i : Fin 6,
      v15DegreeFiveHunterLower i ≤ f.coeff i ∧
        f.coeff i ≤ v15DegreeFiveHunterUpper i := by
  have hs2 := v15_degreeFive_hunterSecondCoefficient_bounds h
  have hs1 := v15_degreeFive_hunterTraceCoefficient_bounds h
  have hlead : f.coeff 5 = 1 := by
    have hc := h.1.coeff_natDegree
    rwa [h.2.2.1] at hc
  refine ⟨h.2.2.1.le, ?_⟩
  intro i
  fin_cases i
  · have hb := v15_degreeFive_hunterCandidate_coeff_bound_sharp
      h 0 (by norm_num)
    norm_num [Nat.choose, Real.norm_eq_abs] at hb
    simpa [v15DegreeFiveHunterLower, v15DegreeFiveHunterUpper] using
      (show -759375 ≤ f.coeff 0 ∧ f.coeff 0 ≤ 759375 by
        exact_mod_cast (abs_le.mp hb))
  · have hb := v15_degreeFive_hunterCandidate_coeff_bound_sharp
      h 1 (by norm_num)
    norm_num [Nat.choose, Real.norm_eq_abs] at hb
    simpa [v15DegreeFiveHunterLower, v15DegreeFiveHunterUpper] using
      (show -253125 ≤ f.coeff 1 ∧ f.coeff 1 ≤ 253125 by
        exact_mod_cast (abs_le.mp hb))
  · have hb := v15_degreeFive_hunterCandidate_coeff_bound_sharp
      h 2 (by norm_num)
    norm_num [Nat.choose, Real.norm_eq_abs] at hb
    simpa [v15DegreeFiveHunterLower, v15DegreeFiveHunterUpper] using
      (show -33750 ≤ f.coeff 2 ∧ f.coeff 2 ≤ 33750 by
        exact_mod_cast (abs_le.mp hb))
  · simpa [v15DegreeFiveHunterLower, v15DegreeFiveHunterUpper] using hs2
  · simpa [v15DegreeFiveHunterLower, v15DegreeFiveHunterUpper] using hs1
  · simp [v15DegreeFiveHunterLower, v15DegreeFiveHunterUpper, hlead]

/-- Every degree-five Hunter candidate belongs to the refined interval box. -/
theorem v15_degreeFive_hunterCandidate_mem_refinedBox
    {f : ℤ[X]} (h : V15HunterPolynomialCandidate 5 180 f) :
    f ∈ v15DegreeFiveHunterRefinedBox := by
  rw [v15DegreeFiveHunterRefinedBox,
    v15_mem_integralPolynomialIntervalBox_iff]
  exact v15_degreeFive_hunterCandidate_refined_bounds h

/-- Coordinate inequalities defining the refined degree-seven interval box. -/
theorem v15_degreeSeven_hunterCandidate_refined_bounds
    {f : ℤ[X]} (h : V15HunterPolynomialCandidate 7 343 f) :
    f.natDegree ≤ 7 ∧ ∀ i : Fin 8,
      v15DegreeSevenHunterLower i ≤ f.coeff i ∧
        f.coeff i ≤ v15DegreeSevenHunterUpper i := by
  have hs2 := v15_degreeSeven_hunterSecondCoefficient_bounds h
  have hs1 := v15_degreeSeven_hunterTraceCoefficient_bounds h
  have hlead : f.coeff 7 = 1 := by
    have hc := h.1.coeff_natDegree
    rwa [h.2.2.1] at hc
  refine ⟨h.2.2.1.le, ?_⟩
  intro i
  fin_cases i
  · have hb := v15_degreeSeven_hunterCandidate_coeff_bound_sharp
      h 0 (by norm_num)
    norm_num [Nat.choose, Real.norm_eq_abs] at hb
    simpa [v15DegreeSevenHunterLower, v15DegreeSevenHunterUpper] using
      (show -1280000000 ≤ f.coeff 0 ∧ f.coeff 0 ≤ 1280000000 by
        exact_mod_cast (abs_le.mp hb))
  · have hb := v15_degreeSeven_hunterCandidate_coeff_bound_sharp
      h 1 (by norm_num)
    norm_num [Nat.choose, Real.norm_eq_abs] at hb
    simpa [v15DegreeSevenHunterLower, v15DegreeSevenHunterUpper] using
      (show -448000000 ≤ f.coeff 1 ∧ f.coeff 1 ≤ 448000000 by
        exact_mod_cast (abs_le.mp hb))
  · have hb := v15_degreeSeven_hunterCandidate_coeff_bound_sharp
      h 2 (by norm_num)
    norm_num [Nat.choose, Real.norm_eq_abs] at hb
    simpa [v15DegreeSevenHunterLower, v15DegreeSevenHunterUpper] using
      (show -67200000 ≤ f.coeff 2 ∧ f.coeff 2 ≤ 67200000 by
        exact_mod_cast (abs_le.mp hb))
  · have hb := v15_degreeSeven_hunterCandidate_coeff_bound_sharp
      h 3 (by norm_num)
    norm_num [Nat.choose, Real.norm_eq_abs] at hb
    simpa [v15DegreeSevenHunterLower, v15DegreeSevenHunterUpper] using
      (show -5600000 ≤ f.coeff 3 ∧ f.coeff 3 ≤ 5600000 by
        exact_mod_cast (abs_le.mp hb))
  · have hb := v15_degreeSeven_hunterCandidate_coeff_bound_sharp
      h 4 (by norm_num)
    norm_num [Nat.choose, Real.norm_eq_abs] at hb
    simpa [v15DegreeSevenHunterLower, v15DegreeSevenHunterUpper] using
      (show -280000 ≤ f.coeff 4 ∧ f.coeff 4 ≤ 280000 by
        exact_mod_cast (abs_le.mp hb))
  · simpa [v15DegreeSevenHunterLower, v15DegreeSevenHunterUpper] using hs2
  · simpa [v15DegreeSevenHunterLower, v15DegreeSevenHunterUpper] using hs1
  · simp [v15DegreeSevenHunterLower, v15DegreeSevenHunterUpper, hlead]

/-- Every degree-seven Hunter candidate belongs to the refined interval box. -/
theorem v15_degreeSeven_hunterCandidate_mem_refinedBox
    {f : ℤ[X]} (h : V15HunterPolynomialCandidate 7 343 f) :
    f ∈ v15DegreeSevenHunterRefinedBox := by
  rw [v15DegreeSevenHunterRefinedBox,
    v15_mem_integralPolynomialIntervalBox_iff]
  exact v15_degreeSeven_hunterCandidate_refined_bounds h

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

/-- Every qualifying quintic field lands in the refined executable interval
box and retains its generator and exact positive-index discriminant formula. -/
theorem v15_exists_degreeFive_hunterFieldCandidate_mem_refinedBox
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 5)
    (hdisc :
      ((|NumberField.discr K| : ℤ) : ℝ) ≤ (14 : ℝ) ^ 5) :
    ∃ f ∈ v15DegreeFiveHunterRefinedBox,
      V15HunterFieldPolynomialCandidate K 5 180 f := by
  obtain ⟨f, _, hf⟩ :=
    v15_exists_degreeFive_hunterFieldCandidate_of_discriminant_le
      K hreal hdegree hdisc
  refine ⟨f, ?_, hf⟩
  rw [v15DegreeFiveHunterRefinedBox,
    v15_mem_integralPolynomialIntervalBox_iff]
  exact v15_degreeFive_hunterCandidate_refined_bounds hf.1

/-- Every qualifying septic field lands in the refined executable interval
box and retains its generator and exact positive-index discriminant formula. -/
theorem v15_exists_degreeSeven_hunterFieldCandidate_mem_refinedBox
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 7)
    (hdisc :
      ((|NumberField.discr K| : ℤ) : ℝ) ≤ (14 : ℝ) ^ 7) :
    ∃ f ∈ v15DegreeSevenHunterRefinedBox,
      V15HunterFieldPolynomialCandidate K 7 343 f := by
  obtain ⟨f, _, hf⟩ :=
    v15_exists_degreeSeven_hunterFieldCandidate_of_discriminant_le
      K hreal hdegree hdisc
  refine ⟨f, ?_, hf⟩
  rw [v15DegreeSevenHunterRefinedBox,
    v15_mem_integralPolynomialIntervalBox_iff]
  exact v15_degreeSeven_hunterCandidate_refined_bounds hf.1

end

end TraceEuclidean
