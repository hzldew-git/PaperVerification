import TraceEuclidean.GeneralPowerIndex
import TraceEuclidean.HunterCoordinateBoxes
import TraceEuclidean.AnalyticTable

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
theorem degreeFive_hunterBall_numerical :
    ((14 : ℝ) ^ 5) * (((2 : ℝ) ^ 4) ^ 2) <
      (5 : ℝ) *
        (euclideanUnitBallVolume 4 * (6 : ℝ) ^ 4) ^ 2 := by
  rw [mul_pow, unitBallVolume_sq_closed]
  norm_num [unitBallSquareCoefficient, piExponent]
  have hpi := Real.pi_gt_three
  nlinarith [sq_nonneg (Real.pi ^ 2 - 81 / 8)]

/-- Radius `7` satisfies the degree-seven Hunter ball inequality at root
discriminant `14`. -/
theorem degreeSeven_hunterBall_numerical :
    ((14 : ℝ) ^ 7) * (((2 : ℝ) ^ 6) ^ 2) <
      (7 : ℝ) *
        (euclideanUnitBallVolume 6 * (7 : ℝ) ^ 6) ^ 2 := by
  rw [mul_pow, unitBallVolume_sq_closed]
  norm_num [unitBallSquareCoefficient, piExponent]
  have hpi := Real.pi_gt_three
  have hpi6 : (3 : ℝ) ^ 6 < Real.pi ^ 6 :=
    pow_lt_pow_left₀ hpi (by norm_num) (by norm_num)
  nlinarith

/-- The degree-five Hunter roots have norm at most `15`. -/
theorem degreeFive_hunterRootBound :
    hunterRootBound 5 180 ≤ 15 := by
  rw [hunterRootBound]
  norm_num
  exact (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩

/-- The degree-seven Hunter roots have norm at most `20`. -/
theorem degreeSeven_hunterRootBound :
    hunterRootBound 7 343 ≤ 20 := by
  rw [hunterRootBound]
  norm_num
  exact (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩

/-- The general Vieta root estimate gives this explicit degree-five
coefficient bound. -/
theorem degreeFive_hunterCoefficientBound :
    hunterCoefficientBound 5 180 ≤ 7593750 := by
  have hmax : max (hunterRootBound 5 180) 1 ≤ 15 :=
    max_le degreeFive_hunterRootBound (by norm_num)
  rw [hunterCoefficientBound]
  calc
    max (hunterRootBound 5 180) 1 ^ 5 *
        Nat.choose 5 (5 / 2) ≤
      (15 : ℝ) ^ 5 * Nat.choose 5 (5 / 2) := by
        gcongr
    _ = 7593750 := by norm_num [Nat.choose]

/-- The general Vieta root estimate gives this explicit degree-seven
coefficient bound. -/
theorem degreeSeven_hunterCoefficientBound :
    hunterCoefficientBound 7 343 ≤ 44800000000 := by
  have hmax : max (hunterRootBound 7 343) 1 ≤ 20 :=
    max_le degreeSeven_hunterRootBound (by norm_num)
  rw [hunterCoefficientBound]
  calc
    max (hunterRootBound 7 343) 1 ^ 7 *
        Nat.choose 7 (7 / 2) ≤
      (20 : ℝ) ^ 7 * Nat.choose 7 (7 / 2) := by
        gcongr
    _ = 44800000000 := by norm_num [Nat.choose]

/-- Every coefficient of a degree-five root-discriminant-14 Hunter candidate
lies in the displayed integer interval. -/
theorem degreeFive_hunterCandidate_coeff_bound
    {f : ℤ[X]} (h : HunterPolynomialCandidate 5 180 f)
    (i : ℕ) :
    ‖(f.coeff i : ℝ)‖ ≤ 7593750 :=
  (hunterPolynomialCandidate_coeff_bound (by norm_num) h i).trans
    degreeFive_hunterCoefficientBound

/-- Every coefficient of a degree-seven root-discriminant-14 Hunter candidate
lies in the displayed integer interval. -/
theorem degreeSeven_hunterCandidate_coeff_bound
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 343 f)
    (i : ℕ) :
    ‖(f.coeff i : ℝ)‖ ≤ 44800000000 :=
  (hunterPolynomialCandidate_coeff_bound (by norm_num) h i).trans
    degreeSeven_hunterCoefficientBound

/-- The sharper coordinatewise degree-five coefficient estimate. -/
theorem degreeFive_hunterCandidate_coeff_bound_sharp
    {f : ℤ[X]} (h : HunterPolynomialCandidate 5 180 f)
    (i : ℕ) (hi : i ≤ 5) :
    ‖(f.coeff i : ℝ)‖ ≤
      (Nat.choose 5 (5 - i) : ℝ) * 15 ^ (5 - i) := by
  have hb := hunterPolynomialCandidate_coeff_bound_at
    (d := 5) (B := 180) (f := f) (by norm_num) h i hi
  exact hb.trans (by
    have hrootNonneg : 0 ≤ hunterRootBound 5 180 :=
      Real.sqrt_nonneg _
    gcongr
    exact degreeFive_hunterRootBound)

/-- The sharper coordinatewise degree-seven coefficient estimate. -/
theorem degreeSeven_hunterCandidate_coeff_bound_sharp
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 343 f)
    (i : ℕ) (hi : i ≤ 7) :
    ‖(f.coeff i : ℝ)‖ ≤
      (Nat.choose 7 (7 - i) : ℝ) * 20 ^ (7 - i) := by
  have hb := hunterPolynomialCandidate_coeff_bound_at
    (d := 7) (B := 343) (f := f) (by norm_num) h i hi
  exact hb.trans (by
    have hrootNonneg : 0 ≤ hunterRootBound 7 343 :=
      Real.sqrt_nonneg _
    gcongr
    exact degreeSeven_hunterRootBound)

/-- The sharper executable degree-five coefficient box.  Its coordinate
radii, from constant to leading coefficient, are
`759375, 253125, 33750, 2250, 75, 1`. -/
def degreeFiveHunterCoordinateBox : Finset ℤ[X] :=
  integralPolynomialCoordinateBox 5
    (hunterCoordinateBound 5 15)

/-- The sharper executable degree-seven coefficient box.  Its coordinate
radii, from constant to leading coefficient, are
`1280000000, 448000000, 67200000, 5600000, 280000, 8400, 140, 1`. -/
def degreeSevenHunterCoordinateBox : Finset ℤ[X] :=
  integralPolynomialCoordinateBox 7
    (hunterCoordinateBound 7 20)

/-- Exact size of the degree-five coordinate box. -/
theorem degreeFive_hunterCoordinateBox_card :
    degreeFiveHunterCoordinateBox.card =
      105820520340154659628953 := by
  rw [degreeFiveHunterCoordinateBox,
    card_integralPolynomialCoordinateBox]
  norm_num [hunterCoordinateBound, Fin.prod_univ_succ, Nat.choose]

/-- Exact size of the degree-seven coordinate box. -/
theorem degreeSeven_hunterCoordinateBox_card :
    degreeSevenHunterCoordinateBox.card =
      27385256812699621612303428104012519835419043243 := by
  rw [degreeSevenHunterCoordinateBox,
    card_integralPolynomialCoordinateBox]
  norm_num [hunterCoordinateBound, Fin.prod_univ_succ, Nat.choose]

/-- Every degree-five Hunter candidate belongs to the sharper coordinate
box. -/
theorem degreeFive_hunterCandidate_mem_coordinateBox
    {f : ℤ[X]} (h : HunterPolynomialCandidate 5 180 f) :
    f ∈ degreeFiveHunterCoordinateBox := by
  rw [degreeFiveHunterCoordinateBox,
    mem_integralPolynomialCoordinateBox_iff]
  refine ⟨h.2.2.1.le, ?_⟩
  intro i
  have hb := hunterPolynomialCandidate_coeff_bound_at
    (d := 5) (B := 180) (f := f) (by norm_num) h i (by omega)
  have hpow :
      hunterRootBound 5 180 ^ (5 - (i : ℕ)) ≤
        (15 : ℝ) ^ (5 - (i : ℕ)) := by
    gcongr
    · exact Real.sqrt_nonneg _
    · exact degreeFive_hunterRootBound
  have hb' :
      |(f.coeff i : ℝ)| ≤
        (hunterCoordinateBound 5 15 i : ℝ) := by
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (by
      rw [hunterCoordinateBound]
      push_cast
      gcongr)
  constructor
  · exact_mod_cast (abs_le.mp hb').1
  · exact_mod_cast (abs_le.mp hb').2

/-- Every degree-seven Hunter candidate belongs to the sharper coordinate
box. -/
theorem degreeSeven_hunterCandidate_mem_coordinateBox
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 343 f) :
    f ∈ degreeSevenHunterCoordinateBox := by
  rw [degreeSevenHunterCoordinateBox,
    mem_integralPolynomialCoordinateBox_iff]
  refine ⟨h.2.2.1.le, ?_⟩
  intro i
  have hb := hunterPolynomialCandidate_coeff_bound_at
    (d := 7) (B := 343) (f := f) (by norm_num) h i (by omega)
  have hpow :
      hunterRootBound 7 343 ^ (7 - (i : ℕ)) ≤
        (20 : ℝ) ^ (7 - (i : ℕ)) := by
    gcongr
    · exact Real.sqrt_nonneg _
    · exact degreeSeven_hunterRootBound
  have hb' :
      |(f.coeff i : ℝ)| ≤
        (hunterCoordinateBound 7 20 i : ℝ) := by
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (by
      rw [hunterCoordinateBound]
      push_cast
      gcongr)
  constructor
  · exact_mod_cast (abs_le.mp hb').1
  · exact_mod_cast (abs_le.mp hb').2

/-- The second signed coefficient of a degree-five Hunter candidate lies in
the much smaller interval forced by the sum of squared roots and the strict
spread inequality. -/
theorem degreeFive_hunterSecondCoefficient_bounds
    {f : ℤ[X]} (h : HunterPolynomialCandidate 5 180 f) :
    -17 ≤ f.coeff 3 ∧ f.coeff 3 ≤ 2 := by
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
  change (((generalSpread 5 s1 s2 : ℤ) : ℝ)) < 180 at hspread
  have hspreadInt : generalSpread 5 s1 s2 < (180 : ℤ) := by
    exact_mod_cast hspread
  have hlower : -17 ≤ s2 := by
    have hmul : -180 < 10 * s2 := by
      simp [generalSpread] at hspreadInt
      nlinarith [sq_nonneg s1]
    omega
  have hsq : s1 ^ 2 ≤ 4 := by nlinarith
  have hupper : s2 ≤ 2 := by nlinarith
  exact ⟨by simpa [s2] using hlower, by simpa [s2] using hupper⟩

/-- The corresponding degree-seven second-coefficient interval. -/
theorem degreeSeven_hunterSecondCoefficient_bounds
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 343 f) :
    -24 ≤ f.coeff 5 ∧ f.coeff 5 ≤ 4 := by
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
  change (((generalSpread 7 s1 s2 : ℤ) : ℝ)) < 343 at hspread
  have hspreadInt : generalSpread 7 s1 s2 < (343 : ℤ) := by
    exact_mod_cast hspread
  have hlower : -24 ≤ s2 := by
    have hmul : -343 < 14 * s2 := by
      simp [generalSpread] at hspreadInt
      nlinarith [sq_nonneg s1]
    omega
  have hsq : s1 ^ 2 ≤ 9 := by nlinarith
  have htwiceBound : 2 * s2 ≤ 9 := htwice.trans hsq
  have hupper : s2 ≤ 4 := by omega
  exact ⟨by simpa [s2] using hlower, by simpa [s2] using hupper⟩

/-- The normalized degree-five trace coefficient interval. -/
theorem degreeFive_hunterTraceCoefficient_bounds
    {f : ℤ[X]} (h : HunterPolynomialCandidate 5 180 f) :
    -2 ≤ f.coeff 4 ∧ f.coeff 4 ≤ 0 := by
  have hnonneg := h.2.2.2.2.1
  have hhalf := h.2.2.2.2.2.1
  norm_num at hnonneg hhalf
  omega

/-- The normalized degree-seven trace coefficient interval. -/
theorem degreeSeven_hunterTraceCoefficient_bounds
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 343 f) :
    -3 ≤ f.coeff 6 ∧ f.coeff 6 ≤ 0 := by
  have hnonneg := h.2.2.2.2.1
  have hhalf := h.2.2.2.2.2.1
  norm_num at hnonneg hhalf
  omega

/-- Lower endpoints for the refined degree-five Hunter box. -/
def degreeFiveHunterLower : Fin 6 → ℤ :=
  ![-759375, -253125, -33750, -17, -2, 1]

/-- Upper endpoints for the refined degree-five Hunter box. -/
def degreeFiveHunterUpper : Fin 6 → ℤ :=
  ![759375, 253125, 33750, 2, 0, 1]

/-- Lower endpoints for the refined degree-seven Hunter box. -/
def degreeSevenHunterLower : Fin 8 → ℤ :=
  ![-1280000000, -448000000, -67200000, -5600000,
    -280000, -24, -3, 1]

/-- Upper endpoints for the refined degree-seven Hunter box. -/
def degreeSevenHunterUpper : Fin 8 → ℤ :=
  ![1280000000, 448000000, 67200000, 5600000,
    280000, 4, 0, 1]

/-- The refined degree-five box fixes monicity and incorporates the exact
trace and second-coefficient intervals. -/
def degreeFiveHunterRefinedBox : Finset ℤ[X] :=
  integralPolynomialIntervalBox 5
    degreeFiveHunterLower degreeFiveHunterUpper

/-- The analogous refined degree-seven box. -/
def degreeSevenHunterRefinedBox : Finset ℤ[X] :=
  integralPolynomialIntervalBox 7
    degreeSevenHunterLower degreeSevenHunterUpper

/-- Exact size of the refined degree-five box. -/
theorem degreeFive_hunterRefinedBox_card :
    degreeFiveHunterRefinedBox.card = 3113966442781800060 := by
  rw [degreeFiveHunterRefinedBox,
    card_integralPolynomialIntervalBox]
  norm_num [degreeFiveHunterLower, degreeFiveHunterUpper,
    Fin.prod_univ_succ, Int.toNat]

/-- Exact size of the refined degree-seven box. -/
theorem degreeSeven_hunterRefinedBox_card :
    degreeSevenHunterRefinedBox.card =
      224291130941773441790640579990433850560116 := by
  rw [degreeSevenHunterRefinedBox,
    card_integralPolynomialIntervalBox]
  norm_num [degreeSevenHunterLower, degreeSevenHunterUpper,
    Fin.prod_univ_succ, Int.toNat]

/-- Coordinate inequalities defining the refined degree-five interval box. -/
theorem degreeFive_hunterCandidate_refined_bounds
    {f : ℤ[X]} (h : HunterPolynomialCandidate 5 180 f) :
    f.natDegree ≤ 5 ∧ ∀ i : Fin 6,
      degreeFiveHunterLower i ≤ f.coeff i ∧
        f.coeff i ≤ degreeFiveHunterUpper i := by
  have hs2 := degreeFive_hunterSecondCoefficient_bounds h
  have hs1 := degreeFive_hunterTraceCoefficient_bounds h
  have hlead : f.coeff 5 = 1 := by
    have hc := h.1.coeff_natDegree
    rwa [h.2.2.1] at hc
  refine ⟨h.2.2.1.le, ?_⟩
  intro i
  fin_cases i
  · have hb := degreeFive_hunterCandidate_coeff_bound_sharp
      h 0 (by norm_num)
    norm_num [Nat.choose, Real.norm_eq_abs] at hb
    simpa [degreeFiveHunterLower, degreeFiveHunterUpper] using
      (show -759375 ≤ f.coeff 0 ∧ f.coeff 0 ≤ 759375 by
        exact_mod_cast (abs_le.mp hb))
  · have hb := degreeFive_hunterCandidate_coeff_bound_sharp
      h 1 (by norm_num)
    norm_num [Nat.choose, Real.norm_eq_abs] at hb
    simpa [degreeFiveHunterLower, degreeFiveHunterUpper] using
      (show -253125 ≤ f.coeff 1 ∧ f.coeff 1 ≤ 253125 by
        exact_mod_cast (abs_le.mp hb))
  · have hb := degreeFive_hunterCandidate_coeff_bound_sharp
      h 2 (by norm_num)
    norm_num [Nat.choose, Real.norm_eq_abs] at hb
    simpa [degreeFiveHunterLower, degreeFiveHunterUpper] using
      (show -33750 ≤ f.coeff 2 ∧ f.coeff 2 ≤ 33750 by
        exact_mod_cast (abs_le.mp hb))
  · simpa [degreeFiveHunterLower, degreeFiveHunterUpper] using hs2
  · simpa [degreeFiveHunterLower, degreeFiveHunterUpper] using hs1
  · simp [degreeFiveHunterLower, degreeFiveHunterUpper, hlead]

/-- Every degree-five Hunter candidate belongs to the refined interval box. -/
theorem degreeFive_hunterCandidate_mem_refinedBox
    {f : ℤ[X]} (h : HunterPolynomialCandidate 5 180 f) :
    f ∈ degreeFiveHunterRefinedBox := by
  rw [degreeFiveHunterRefinedBox,
    mem_integralPolynomialIntervalBox_iff]
  exact degreeFive_hunterCandidate_refined_bounds h

/-- Coordinate inequalities defining the refined degree-seven interval box. -/
theorem degreeSeven_hunterCandidate_refined_bounds
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 343 f) :
    f.natDegree ≤ 7 ∧ ∀ i : Fin 8,
      degreeSevenHunterLower i ≤ f.coeff i ∧
        f.coeff i ≤ degreeSevenHunterUpper i := by
  have hs2 := degreeSeven_hunterSecondCoefficient_bounds h
  have hs1 := degreeSeven_hunterTraceCoefficient_bounds h
  have hlead : f.coeff 7 = 1 := by
    have hc := h.1.coeff_natDegree
    rwa [h.2.2.1] at hc
  refine ⟨h.2.2.1.le, ?_⟩
  intro i
  fin_cases i
  · have hb := degreeSeven_hunterCandidate_coeff_bound_sharp
      h 0 (by norm_num)
    norm_num [Nat.choose, Real.norm_eq_abs] at hb
    simpa [degreeSevenHunterLower, degreeSevenHunterUpper] using
      (show -1280000000 ≤ f.coeff 0 ∧ f.coeff 0 ≤ 1280000000 by
        exact_mod_cast (abs_le.mp hb))
  · have hb := degreeSeven_hunterCandidate_coeff_bound_sharp
      h 1 (by norm_num)
    norm_num [Nat.choose, Real.norm_eq_abs] at hb
    simpa [degreeSevenHunterLower, degreeSevenHunterUpper] using
      (show -448000000 ≤ f.coeff 1 ∧ f.coeff 1 ≤ 448000000 by
        exact_mod_cast (abs_le.mp hb))
  · have hb := degreeSeven_hunterCandidate_coeff_bound_sharp
      h 2 (by norm_num)
    norm_num [Nat.choose, Real.norm_eq_abs] at hb
    simpa [degreeSevenHunterLower, degreeSevenHunterUpper] using
      (show -67200000 ≤ f.coeff 2 ∧ f.coeff 2 ≤ 67200000 by
        exact_mod_cast (abs_le.mp hb))
  · have hb := degreeSeven_hunterCandidate_coeff_bound_sharp
      h 3 (by norm_num)
    norm_num [Nat.choose, Real.norm_eq_abs] at hb
    simpa [degreeSevenHunterLower, degreeSevenHunterUpper] using
      (show -5600000 ≤ f.coeff 3 ∧ f.coeff 3 ≤ 5600000 by
        exact_mod_cast (abs_le.mp hb))
  · have hb := degreeSeven_hunterCandidate_coeff_bound_sharp
      h 4 (by norm_num)
    norm_num [Nat.choose, Real.norm_eq_abs] at hb
    simpa [degreeSevenHunterLower, degreeSevenHunterUpper] using
      (show -280000 ≤ f.coeff 4 ∧ f.coeff 4 ≤ 280000 by
        exact_mod_cast (abs_le.mp hb))
  · simpa [degreeSevenHunterLower, degreeSevenHunterUpper] using hs2
  · simpa [degreeSevenHunterLower, degreeSevenHunterUpper] using hs1
  · simp [degreeSevenHunterLower, degreeSevenHunterUpper, hlead]

/-- Every degree-seven Hunter candidate belongs to the refined interval box. -/
theorem degreeSeven_hunterCandidate_mem_refinedBox
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 343 f) :
    f ∈ degreeSevenHunterRefinedBox := by
  rw [degreeSevenHunterRefinedBox,
    mem_integralPolynomialIntervalBox_iff]
  exact degreeSeven_hunterCandidate_refined_bounds h

/-- The complete degree-five Hunter candidate set at this bound is finite. -/
theorem degreeFive_hunterCandidates_finite :
    Set.Finite {f : ℤ[X] |
      HunterPolynomialCandidate 5 180 f} :=
  hunterPolynomialCandidates_finite (by norm_num) 180

/-- The complete degree-seven Hunter candidate set at this bound is finite. -/
theorem degreeSeven_hunterCandidates_finite :
    Set.Finite {f : ℤ[X] |
      HunterPolynomialCandidate 7 343 f} :=
  hunterPolynomialCandidates_finite (by norm_num) 343

/-- Every totally real quintic field of root discriminant at most `14`
admits a polynomial in the finite degree-five Hunter candidate set. -/
theorem exists_degreeFive_hunterCandidate_of_discriminant_le
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 5)
    (hdisc :
      ((|NumberField.discr K| : ℤ) : ℝ) ≤ (14 : ℝ) ^ 5) :
    ∃ f : ℤ[X], HunterPolynomialCandidate 5 180 f := by
  have hball :
      ((|NumberField.discr K| : ℤ) : ℝ) *
          (((2 : ℝ) ^ 4) ^ 2) <
        (5 : ℝ) *
          (euclideanUnitBallVolume 4 * (6 : ℝ) ^ 4) ^ 2 :=
    (mul_le_mul_of_nonneg_right hdisc (by positivity)).trans_lt
      degreeFive_hunterBall_numerical
  obtain ⟨f, hf⟩ :=
    exists_hunterPolynomialCandidate_of_hunterBall K hreal
      (by simpa using hdegree) (by norm_num) (by norm_num)
      6 (by norm_num) (by
        convert hball using 1
        all_goals norm_num)
  refine ⟨f, ?_⟩
  convert hf using 1
  all_goals norm_num

/-- Every totally real septic field of root discriminant at most `14`
admits a polynomial in the finite degree-seven Hunter candidate set. -/
theorem exists_degreeSeven_hunterCandidate_of_discriminant_le
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 7)
    (hdisc :
      ((|NumberField.discr K| : ℤ) : ℝ) ≤ (14 : ℝ) ^ 7) :
    ∃ f : ℤ[X], HunterPolynomialCandidate 7 343 f := by
  have hball :
      ((|NumberField.discr K| : ℤ) : ℝ) *
          (((2 : ℝ) ^ 6) ^ 2) <
        (7 : ℝ) *
          (euclideanUnitBallVolume 6 * (7 : ℝ) ^ 6) ^ 2 :=
    (mul_le_mul_of_nonneg_right hdisc (by positivity)).trans_lt
      degreeSeven_hunterBall_numerical
  obtain ⟨f, hf⟩ :=
    exists_hunterPolynomialCandidate_of_hunterBall K hreal
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
theorem exists_degreeFive_hunterFieldCandidate_of_discriminant_le
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 5)
    (hdisc :
      ((|NumberField.discr K| : ℤ) : ℝ) ≤ (14 : ℝ) ^ 5) :
    ∃ f ∈ hunterPolynomialCandidates 5 (by norm_num) 180,
      HunterFieldPolynomialCandidate K 5 180 f := by
  have hball :
      ((|NumberField.discr K| : ℤ) : ℝ) *
          (((2 : ℝ) ^ 4) ^ 2) <
        (5 : ℝ) *
          (euclideanUnitBallVolume 4 * (6 : ℝ) ^ 4) ^ 2 :=
    (mul_le_mul_of_nonneg_right hdisc (by positivity)).trans_lt
      degreeFive_hunterBall_numerical
  obtain ⟨f, hf⟩ :=
    exists_hunterFieldPolynomialCandidate_of_hunterBall K hreal
      (by simpa using hdegree) (by norm_num) (by norm_num)
      6 (by norm_num) (by
        convert hball using 1
        all_goals norm_num)
  have hf' : HunterFieldPolynomialCandidate K 5 180 f := by
    convert hf using 1
    all_goals norm_num
  exact ⟨f,
    (mem_hunterPolynomialCandidates_iff
      5 (by norm_num) 180 f).2 hf'.1,
    hf'⟩

/-- Every totally real septic field of root discriminant at most `14`
lands in the finite Hunter search together with its primitive generator and
strictly positive integral index. -/
theorem exists_degreeSeven_hunterFieldCandidate_of_discriminant_le
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 7)
    (hdisc :
      ((|NumberField.discr K| : ℤ) : ℝ) ≤ (14 : ℝ) ^ 7) :
    ∃ f ∈ hunterPolynomialCandidates 7 (by norm_num) 343,
      HunterFieldPolynomialCandidate K 7 343 f := by
  have hball :
      ((|NumberField.discr K| : ℤ) : ℝ) *
          (((2 : ℝ) ^ 6) ^ 2) <
        (7 : ℝ) *
          (euclideanUnitBallVolume 6 * (7 : ℝ) ^ 6) ^ 2 :=
    (mul_le_mul_of_nonneg_right hdisc (by positivity)).trans_lt
      degreeSeven_hunterBall_numerical
  obtain ⟨f, hf⟩ :=
    exists_hunterFieldPolynomialCandidate_of_hunterBall K hreal
      (by simpa using hdegree) (by norm_num) (by norm_num)
      7 (by norm_num) (by
        convert hball using 1
        all_goals norm_num)
  have hf' : HunterFieldPolynomialCandidate K 7 343 f := by
    convert hf using 1
    all_goals norm_num
  exact ⟨f,
    (mem_hunterPolynomialCandidates_iff
      7 (by norm_num) 343 f).2 hf'.1,
    hf'⟩

/-- Every qualifying quintic field lands in the refined executable interval
box and retains its generator and exact positive-index discriminant formula. -/
theorem exists_degreeFive_hunterFieldCandidate_mem_refinedBox
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 5)
    (hdisc :
      ((|NumberField.discr K| : ℤ) : ℝ) ≤ (14 : ℝ) ^ 5) :
    ∃ f ∈ degreeFiveHunterRefinedBox,
      HunterFieldPolynomialCandidate K 5 180 f := by
  obtain ⟨f, _, hf⟩ :=
    exists_degreeFive_hunterFieldCandidate_of_discriminant_le
      K hreal hdegree hdisc
  refine ⟨f, ?_, hf⟩
  rw [degreeFiveHunterRefinedBox,
    mem_integralPolynomialIntervalBox_iff]
  exact degreeFive_hunterCandidate_refined_bounds hf.1

/-- Every qualifying septic field lands in the refined executable interval
box and retains its generator and exact positive-index discriminant formula. -/
theorem exists_degreeSeven_hunterFieldCandidate_mem_refinedBox
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 7)
    (hdisc :
      ((|NumberField.discr K| : ℤ) : ℝ) ≤ (14 : ℝ) ^ 7) :
    ∃ f ∈ degreeSevenHunterRefinedBox,
      HunterFieldPolynomialCandidate K 7 343 f := by
  obtain ⟨f, _, hf⟩ :=
    exists_degreeSeven_hunterFieldCandidate_of_discriminant_le
      K hreal hdegree hdisc
  refine ⟨f, ?_, hf⟩
  rw [degreeSevenHunterRefinedBox,
    mem_integralPolynomialIntervalBox_iff]
  exact degreeSeven_hunterCandidate_refined_bounds hf.1

end

end TraceEuclidean
