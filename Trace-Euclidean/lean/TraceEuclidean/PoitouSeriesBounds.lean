import TraceEuclidean.PoitouDegreeEleven

set_option maxRecDepth 100000

open scoped BigOperators
open Finset Filter

namespace TraceEuclidean.PoitouSeriesBounds

noncomputable section

private def logTerm (u : ℝ) (n : ℕ) : ℝ :=
  u ^ (n + 1) / ((n + 1 : ℕ) : ℝ)

private theorem hasSum_log_one_add_alternating {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n * logTerm u n)
      (Real.log (1 + u)) := by
  have huabs : |(-u : ℝ)| < 1 := by
    rw [abs_neg, abs_of_nonneg hu0]
    exact hu1
  have h :=
    (Real.hasSum_pow_div_log_of_abs_lt_one huabs).mul_left (-1 : ℝ)
  have h' : HasSum (fun n : ℕ => (-1 : ℝ) ^ n * logTerm u n)
      (-1 * -Real.log (1 - -u)) := HasSum.congr_fun h fun n => by
    dsimp [logTerm]
    push_cast
    rw [neg_pow, pow_succ]
    ring
  have harg : (1 : ℝ) - -u = 1 + u := by ring
  simpa only [harg, neg_mul, one_mul, neg_neg] using h'

private theorem logTerm_antitone {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Antitone (logTerm u) := by
  intro a b hab
  dsimp [logTerm]
  have hpow : u ^ (b + 1) ≤ u ^ (a + 1) :=
    pow_le_pow_of_le_one hu0 hu1 (by omega)
  have hden : ((a + 1 : ℕ) : ℝ) ≤ ((b + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right hab 1
  exact (div_le_div_of_nonneg_left (pow_nonneg hu0 _) (by positivity) hden).trans
    (div_le_div_of_nonneg_right hpow (by positivity))

private theorem log_one_add_lower {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (m : ℕ) :
    (∑ n ∈ range (2 * m), (-1 : ℝ) ^ n * logTerm u n) ≤
      Real.log (1 + u) := by
  have ht := (hasSum_log_one_add_alternating hu0 hu1).tendsto_sum_nat
  exact (logTerm_antitone hu0 hu1.le).alternating_series_le_tendsto ht m

private theorem log_one_add_upper {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (m : ℕ) :
    Real.log (1 + u) ≤
      ∑ n ∈ range (2 * m + 1), (-1 : ℝ) ^ n * logTerm u n := by
  have ht := (hasSum_log_one_add_alternating hu0 hu1).tendsto_sum_nat
  exact (logTerm_antitone hu0 hu1.le).tendsto_le_alternating_series ht m

private def atanTerm (t : ℝ) (n : ℕ) : ℝ :=
  t ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)

private theorem atanTerm_antitone {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Antitone (atanTerm t) := by
  intro a b hab
  dsimp [atanTerm]
  have hpow : t ^ (2 * b + 1) ≤ t ^ (2 * a + 1) :=
    pow_le_pow_of_le_one ht0 ht1 (by omega)
  have hden : ((2 * a + 1 : ℕ) : ℝ) ≤ ((2 * b + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 2 * a + 1 ≤ 2 * b + 1)
  exact (div_le_div_of_nonneg_left (pow_nonneg ht0 _) (by positivity) hden).trans
    (div_le_div_of_nonneg_right hpow (by positivity))

private theorem arctan_lower {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (m : ℕ) :
    (∑ n ∈ range (2 * m), (-1 : ℝ) ^ n * atanTerm t n) ≤
      Real.arctan t := by
  have htNorm : ‖t‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg ht0]
    exact ht1
  have hs := (Real.hasSum_arctan htNorm).tendsto_sum_nat
  have ht : Tendsto
      (fun k => ∑ n ∈ range k, (-1 : ℝ) ^ n * atanTerm t n)
      atTop (nhds (Real.arctan t)) := by
    simpa [atanTerm, mul_div_assoc] using hs
  exact (atanTerm_antitone ht0 ht1.le).alternating_series_le_tendsto ht m

private theorem arctan_upper {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (m : ℕ) :
    Real.arctan t ≤
      ∑ n ∈ range (2 * m + 1), (-1 : ℝ) ^ n * atanTerm t n := by
  have htNorm : ‖t‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg ht0]
    exact ht1
  have hs := (Real.hasSum_arctan htNorm).tendsto_sum_nat
  have ht : Tendsto
      (fun k => ∑ n ∈ range k, (-1 : ℝ) ^ n * atanTerm t n)
      atTop (nhds (Real.arctan t)) := by
    simpa [atanTerm, mul_div_assoc] using hs
  exact (atanTerm_antitone ht0 ht1.le).tendsto_le_alternating_series ht m

private def poitouUpperCrude (x : ℝ) : ℝ :=
  -3 / (20 * x ^ 2) + 33 / (10 * x) + 2 +
    (3 / (80 * x ^ 3) + 3 / (4 * x ^ 2)) *
      (∑ n ∈ range 11, (-1 : ℝ) ^ n * logTerm (4 * x) n) -
    (3 / x + 12 / 5) / Real.sqrt x *
      (∑ n ∈ range 6, (-1 : ℝ) ^ n * atanTerm (2 * Real.sqrt x) n)

private def poitouLowerCrude (x : ℝ) : ℝ :=
  -3 / (20 * x ^ 2) + 33 / (10 * x) + 2 +
    (3 / (80 * x ^ 3) + 3 / (4 * x ^ 2)) *
      (∑ n ∈ range 8, (-1 : ℝ) ^ n * logTerm (4 * x) n) -
    (3 / x + 12 / 5) / Real.sqrt x *
      (∑ n ∈ range 9, (-1 : ℝ) ^ n * atanTerm (2 * Real.sqrt x) n)

private def poitouUpperFine (x : ℝ) : ℝ :=
  -3 / (20 * x ^ 2) + 33 / (10 * x) + 2 +
    (3 / (80 * x ^ 3) + 3 / (4 * x ^ 2)) *
      (∑ n ∈ range 25, (-1 : ℝ) ^ n * logTerm (4 * x) n) -
    (3 / x + 12 / 5) / Real.sqrt x *
      (∑ n ∈ range 16, (-1 : ℝ) ^ n * atanTerm (2 * Real.sqrt x) n)

private def poitouLowerFine (x : ℝ) : ℝ :=
  -3 / (20 * x ^ 2) + 33 / (10 * x) + 2 +
    (3 / (80 * x ^ 3) + 3 / (4 * x ^ 2)) *
      (∑ n ∈ range 24, (-1 : ℝ) ^ n * logTerm (4 * x) n) -
    (3 / x + 12 / 5) / Real.sqrt x *
      (∑ n ∈ range 15, (-1 : ℝ) ^ n * atanTerm (2 * Real.sqrt x) n)

/-- Rational polynomial above `poitouLClosed` on the small-argument range. -/
def upperPoly (x : ℝ) : ℝ :=
  4 / 5 * x - 144 / 175 * x ^ 2 + 128 / 105 * x ^ 3 -
    512 / 231 * x ^ 4 + 145920 / 77 * x ^ 5 -
    75776 / 15 * x ^ 6 + 1343488 / 75 * x ^ 7 -
    3538944 / 55 * x ^ 8 + 3145728 / 11 * x ^ 9

/-- Rational polynomial below `poitouLClosed` on the small-argument range. -/
def lowerPoly (x : ℝ) : ℝ :=
  4 / 5 * x - 144 / 175 * x ^ 2 + 128 / 105 * x ^ 3 -
    512 / 231 * x ^ 4 + 4608 / 1001 * x ^ 5 -
    14336 / 13 * x ^ 6 - 7602176 / 425 * x ^ 7 -
    1572864 / 85 * x ^ 8

private theorem poitouLClosed_le_upperCrude {x : ℝ}
    (hx0 : 0 < x) (hx4 : 4 * x < 1) :
    TraceEuclidean.PoitouDegreeEleven.poitouLClosed x ≤
      poitouUpperCrude x := by
  have hlog := log_one_add_upper (u := 4 * x) (by positivity) hx4 5
  have hsqrt0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have ht : 2 * Real.sqrt x < 1 := by
    have hsquare : (2 * Real.sqrt x) ^ 2 < (1 : ℝ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hx0.le]
      nlinarith
    nlinarith
  have hatan := arctan_lower (t := 2 * Real.sqrt x) (by positivity) ht 3
  have hB : 0 ≤ 3 / (80 * x ^ 3) + 3 / (4 * x ^ 2) := by positivity
  have hC : 0 ≤ (3 / x + 12 / 5) / Real.sqrt x := by positivity
  have hlogMul := mul_le_mul_of_nonneg_left hlog hB
  have hatanMul := mul_le_mul_of_nonneg_left hatan hC
  dsimp [TraceEuclidean.PoitouDegreeEleven.poitouLClosed, poitouUpperCrude]
  linarith

private theorem lowerCrude_le_poitouLClosed {x : ℝ}
    (hx0 : 0 < x) (hx4 : 4 * x < 1) :
    poitouLowerCrude x ≤
      TraceEuclidean.PoitouDegreeEleven.poitouLClosed x := by
  have hlog := log_one_add_lower (u := 4 * x) (by positivity) hx4 4
  have ht : 2 * Real.sqrt x < 1 := by
    have hsquare : (2 * Real.sqrt x) ^ 2 < (1 : ℝ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hx0.le]
      nlinarith
    nlinarith
  have hatan := arctan_upper (t := 2 * Real.sqrt x) (by positivity) ht 4
  have hB : 0 ≤ 3 / (80 * x ^ 3) + 3 / (4 * x ^ 2) := by positivity
  have hC : 0 ≤ (3 / x + 12 / 5) / Real.sqrt x := by positivity
  have hlogMul := mul_le_mul_of_nonneg_left hlog hB
  have hatanMul := mul_le_mul_of_nonneg_left hatan hC
  dsimp [TraceEuclidean.PoitouDegreeEleven.poitouLClosed, poitouLowerCrude]
  linarith

private theorem poitouLClosed_le_upperFine {x : ℝ}
    (hx0 : 0 < x) (hx4 : 4 * x < 1) :
    TraceEuclidean.PoitouDegreeEleven.poitouLClosed x ≤
      poitouUpperFine x := by
  have hlog := log_one_add_upper (u := 4 * x) (by positivity) hx4 12
  have ht : 2 * Real.sqrt x < 1 := by
    have hsquare : (2 * Real.sqrt x) ^ 2 < (1 : ℝ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hx0.le]
      nlinarith
    nlinarith
  have hatan := arctan_lower (t := 2 * Real.sqrt x) (by positivity) ht 8
  have hB : 0 ≤ 3 / (80 * x ^ 3) + 3 / (4 * x ^ 2) := by positivity
  have hC : 0 ≤ (3 / x + 12 / 5) / Real.sqrt x := by positivity
  have hlogMul := mul_le_mul_of_nonneg_left hlog hB
  have hatanMul := mul_le_mul_of_nonneg_left hatan hC
  dsimp [TraceEuclidean.PoitouDegreeEleven.poitouLClosed, poitouUpperFine]
  linarith

private theorem lowerFine_le_poitouLClosed {x : ℝ}
    (hx0 : 0 < x) (hx4 : 4 * x < 1) :
    poitouLowerFine x ≤
      TraceEuclidean.PoitouDegreeEleven.poitouLClosed x := by
  have hlog := log_one_add_lower (u := 4 * x) (by positivity) hx4 12
  have ht : 2 * Real.sqrt x < 1 := by
    have hsquare : (2 * Real.sqrt x) ^ 2 < (1 : ℝ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hx0.le]
      nlinarith
    nlinarith
  have hatan := arctan_upper (t := 2 * Real.sqrt x) (by positivity) ht 7
  have hB : 0 ≤ 3 / (80 * x ^ 3) + 3 / (4 * x ^ 2) := by positivity
  have hC : 0 ≤ (3 / x + 12 / 5) / Real.sqrt x := by positivity
  have hlogMul := mul_le_mul_of_nonneg_left hlog hB
  have hatanMul := mul_le_mul_of_nonneg_left hatan hC
  dsimp [TraceEuclidean.PoitouDegreeEleven.poitouLClosed, poitouLowerFine]
  linarith

private theorem upperCrude_eq_poly {x : ℝ} (hx0 : 0 < x) :
    poitouUpperCrude x =
      4 / 5 * x - 144 / 175 * x ^ 2 + 128 / 105 * x ^ 3 -
        512 / 231 * x ^ 4 + 145920 / 77 * x ^ 5 -
        75776 / 15 * x ^ 6 + 1343488 / 75 * x ^ 7 -
        3538944 / 55 * x ^ 8 + 3145728 / 11 * x ^ 9 := by
  have hsqrt0 : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx0).ne'
  have hsquare : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  rw [← hsquare]
  dsimp [poitouUpperCrude, logTerm, atanTerm]
  norm_num [Finset.sum_range_succ]
  field_simp
  ring

private theorem lowerCrude_eq_poly {x : ℝ} (hx0 : 0 < x) :
    poitouLowerCrude x =
      4 / 5 * x - 144 / 175 * x ^ 2 + 128 / 105 * x ^ 3 -
        512 / 231 * x ^ 4 + 4608 / 1001 * x ^ 5 -
        14336 / 13 * x ^ 6 - 7602176 / 425 * x ^ 7 -
        1572864 / 85 * x ^ 8 := by
  have hsqrt0 : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx0).ne'
  have hsquare : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  rw [← hsquare]
  dsimp [poitouLowerCrude, logTerm, atanTerm]
  norm_num [Finset.sum_range_succ]
  field_simp
  ring

private def fineUpperPoly (x : ℝ) : ℝ :=
  4 / 5 * x - 144 / 175 * x ^ 2 + 128 / 105 * x ^ 3 -
    512 / 231 * x ^ 4 + 4608 / 1001 * x ^ 5 -
    2048 / 195 * x ^ 6 + 32768 / 1275 * x ^ 7 -
    1179648 / 17765 * x ^ 8 + 262144 / 1463 * x ^ 9 -
    1048576 / 2093 * x ^ 10 + 75497472 / 52325 * x ^ 11 -
    33554432 / 7875 * x ^ 12 + 16777216 / 1305 * x ^ 13 -
    603979776 / 15283 * x ^ 14 + 1234803097600 / 1581 * x ^ 15 -
    661424963584 / 285 * x ^ 16 + 4174708211712 / 475 * x ^ 17 -
    1168231104512 / 35 * x ^ 18 + 48928267436032 / 385 * x ^ 19 -
    613527488299008 / 1265 * x ^ 20 + 213305255788544 / 115 * x ^ 21 -
    888405395243008 / 125 * x ^ 22 + 844424930131968 / 25 * x ^ 23

private def fineLowerPoly (x : ℝ) : ℝ :=
  4 / 5 * x - 144 / 175 * x ^ 2 + 128 / 105 * x ^ 3 -
    512 / 231 * x ^ 4 + 4608 / 1001 * x ^ 5 -
    2048 / 195 * x ^ 6 + 32768 / 1275 * x ^ 7 -
    1179648 / 17765 * x ^ 8 + 262144 / 1463 * x ^ 9 -
    1048576 / 2093 * x ^ 10 + 75497472 / 52325 * x ^ 11 -
    33554432 / 7875 * x ^ 12 + 16777216 / 1305 * x ^ 13 -
    102475235328 / 493 * x ^ 14 + 156766306304 / 255 * x ^ 15 -
    661424963584 / 285 * x ^ 16 + 4174708211712 / 475 * x ^ 17 -
    1168231104512 / 35 * x ^ 18 + 48928267436032 / 385 * x ^ 19 -
    613527488299008 / 1265 * x ^ 20 + 213305255788544 / 115 * x ^ 21 -
    8796093022208 * x ^ 22

private theorem upperFine_eq_poly {x : ℝ} (hx0 : 0 < x) :
    poitouUpperFine x = fineUpperPoly x := by
  have hsqrt0 : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx0).ne'
  have hsquare : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  rw [← hsquare]
  dsimp [poitouUpperFine, fineUpperPoly, logTerm, atanTerm]
  norm_num [Finset.sum_range_succ]
  field_simp
  ring

private theorem lowerFine_eq_poly {x : ℝ} (hx0 : 0 < x) :
    poitouLowerFine x = fineLowerPoly x := by
  have hsqrt0 : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx0).ne'
  have hsquare : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  rw [← hsquare]
  dsimp [poitouLowerFine, fineLowerPoly, logTerm, atanTerm]
  norm_num [Finset.sum_range_succ]
  field_simp
  ring

theorem poitouLClosed_le_upperPoly {x : ℝ}
    (hx0 : 0 < x) (hx4 : 4 * x < 1) :
    TraceEuclidean.PoitouDegreeEleven.poitouLClosed x ≤ upperPoly x := by
  have h := poitouLClosed_le_upperCrude hx0 hx4
  rw [upperCrude_eq_poly hx0] at h
  simpa [upperPoly] using h

theorem lowerPoly_le_poitouLClosed {x : ℝ}
    (hx0 : 0 < x) (hx4 : 4 * x < 1) :
    lowerPoly x ≤
      TraceEuclidean.PoitouDegreeEleven.poitouLClosed x := by
  have h := lowerCrude_le_poitouLClosed hx0 hx4
  rw [lowerCrude_eq_poly hx0] at h
  simpa [lowerPoly] using h

private theorem upperBracket_nonpos {x : ℝ}
    (hx0 : 0 ≤ x) (hxc : x ≤ (1351 / 18000 : ℝ)) :
    103219200 * x ^ 7 - 23224320 * x ^ 6 + 6465536 * x ^ 5 -
        1823360 * x ^ 4 + 684000 * x ^ 3 - 800 * x ^ 2 + 440 * x - 297 ≤ 0 := by
  let t : ℝ := x / (1351 / 18000 : ℝ)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    exact (div_le_one (by norm_num : (0 : ℝ) < 1351 / 18000)).2 hxc
  have hbernstein :
      103219200 * x ^ 7 - 23224320 * x ^ 6 + 6465536 * x ^ 5 -
          1823360 * x ^ 4 + 684000 * x ^ 3 - 800 * x ^ 2 + 440 * x - 297 =
        1 * (-297 : ℝ) * t ^ 0 * (1 - t) ^ 7 +
        7 * (-131527 / 450 : ℝ) * t ^ 1 * (1 - t) ^ 6 +
        21 * (-349651543 / 1215000 : ℝ) * t ^ 2 * (1 - t) ^ 5 +
        35 * (-222934273933 / 810000000 : ℝ) * t ^ 3 * (1 - t) ^ 4 +
        35 * (-203405628265643207 / 820125000000000 : ℝ) * t ^ 4 *
          (1 - t) ^ 3 +
        21 * (-17339320711822647607 / 86497558593750000 : ℝ) * t ^ 5 *
          (1 - t) ^ 2 +
        7 * (-11777005305487865232709 / 92264062500000000000 : ℝ) * t ^ 6 *
          (1 - t) ^ 1 +
        1 * (-1017556481173781041499693 / 41518828125000000000000 : ℝ) *
          t ^ 7 * (1 - t) ^ 0 := by
    dsimp [t]
    field_simp
    ring
  rw [hbernstein]
  have htcomp : 0 ≤ 1 - t := by linarith
  have hterm (c : ℝ) (hc : c ≤ 0) (a b : ℕ) :
      c * t ^ a * (1 - t) ^ b ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hc (pow_nonneg ht0 a))
      (pow_nonneg htcomp b)
  have h0 := hterm (-297) (by norm_num) 0 7
  have h1 := hterm (7 * (-131527 / 450)) (by norm_num) 1 6
  have h2 := hterm (21 * (-349651543 / 1215000)) (by norm_num) 2 5
  have h3 := hterm (35 * (-222934273933 / 810000000)) (by norm_num) 3 4
  have h4 := hterm (35 * (-203405628265643207 / 820125000000000))
    (by norm_num) 4 3
  have h5 := hterm (21 * (-17339320711822647607 / 86497558593750000))
    (by norm_num) 5 2
  have h6 := hterm (7 * (-11777005305487865232709 / 92264062500000000000))
    (by norm_num) 6 1
  have h7 := hterm
    (-1017556481173781041499693 / 41518828125000000000000)
    (by norm_num) 7 0
  linarith

private theorem lowerBracket_nonpos {x : ℝ}
    (hx0 : 0 ≤ x) (hxc : x ≤ (1351 / 18000 : ℝ)) :
    184504320 * x ^ 5 + 178354176 * x ^ 4 + 10995600 * x ^ 3 -
        45900 * x ^ 2 + 22100 * x - 12155 ≤ 0 := by
  let t : ℝ := x / (1351 / 18000 : ℝ)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    exact (div_le_one (by norm_num : (0 : ℝ) < 1351 / 18000)).2 hxc
  have hbernstein :
      184504320 * x ^ 5 + 178354176 * x ^ 4 + 10995600 * x ^ 3 -
          45900 * x ^ 2 + 22100 * x - 12155 =
        1 * (-12155 : ℝ) * t ^ 0 * (1 - t) ^ 5 +
        5 * (-10640929 / 900 : ℝ) * t ^ 1 * (1 - t) ^ 4 +
        10 * (-41462517251 / 3600000 : ℝ) * t ^ 2 * (1 - t) ^ 3 +
        10 * (-523539898718687 / 48600000000 : ℝ) * t ^ 3 *
          (1 - t) ^ 2 +
        5 * (-2730855840159875609 / 341718750000000 : ℝ) * t ^ 4 *
          (1 - t) ^ 1 +
        1 * (-32391273866577737 / 5125781250000000 : ℝ) * t ^ 5 *
          (1 - t) ^ 0 := by
    dsimp [t]
    field_simp
    ring
  rw [hbernstein]
  have htcomp : 0 ≤ 1 - t := by linarith
  have hterm (c : ℝ) (hc : c ≤ 0) (a b : ℕ) :
      c * t ^ a * (1 - t) ^ b ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hc (pow_nonneg ht0 a))
      (pow_nonneg htcomp b)
  have h0 := hterm (-12155) (by norm_num) 0 5
  have h1 := hterm (5 * (-10640929 / 900)) (by norm_num) 1 4
  have h2 := hterm (10 * (-41462517251 / 3600000)) (by norm_num) 2 3
  have h3 := hterm (10 * (-523539898718687 / 48600000000)) (by norm_num) 3 2
  have h4 := hterm (5 * (-2730855840159875609 / 341718750000000))
    (by norm_num) 4 1
  have h5 := hterm (-32391273866577737 / 5125781250000000)
    (by norm_num) 5 0
  linarith

theorem poitouLClosed_small_bounds {x : ℝ}
    (hx0 : 0 < x) (hxc : x ≤ (1351 / 18000 : ℝ)) :
    0 ≤ TraceEuclidean.PoitouDegreeEleven.poitouLClosed x ∧
      TraceEuclidean.PoitouDegreeEleven.poitouLClosed x ≤ 4 / 5 * x := by
  have hx4 : 4 * x < 1 := by nlinarith
  have hupper := poitouLClosed_le_upperCrude hx0 hx4
  have hlower := lowerCrude_le_poitouLClosed hx0 hx4
  rw [upperCrude_eq_poly hx0] at hupper
  rw [lowerCrude_eq_poly hx0] at hlower
  have hP := upperBracket_nonpos hx0.le hxc
  have hR := lowerBracket_nonpos hx0.le hxc
  have hupperPoly :
      4 / 5 * x - 144 / 175 * x ^ 2 + 128 / 105 * x ^ 3 -
          512 / 231 * x ^ 4 + 145920 / 77 * x ^ 5 -
          75776 / 15 * x ^ 6 + 1343488 / 75 * x ^ 7 -
          3538944 / 55 * x ^ 8 + 3145728 / 11 * x ^ 9 ≤ 4 / 5 * x := by
    have hfactor :
        (4 / 5 * x - 144 / 175 * x ^ 2 + 128 / 105 * x ^ 3 -
            512 / 231 * x ^ 4 + 145920 / 77 * x ^ 5 -
            75776 / 15 * x ^ 6 + 1343488 / 75 * x ^ 7 -
            3538944 / 55 * x ^ 8 + 3145728 / 11 * x ^ 9) - 4 / 5 * x =
          16 * x ^ 2 / 5775 *
            (103219200 * x ^ 7 - 23224320 * x ^ 6 + 6465536 * x ^ 5 -
              1823360 * x ^ 4 + 684000 * x ^ 3 - 800 * x ^ 2 + 440 * x -
              297) := by ring
    have hdiff :
        (4 / 5 * x - 144 / 175 * x ^ 2 + 128 / 105 * x ^ 3 -
            512 / 231 * x ^ 4 + 145920 / 77 * x ^ 5 -
            75776 / 15 * x ^ 6 + 1343488 / 75 * x ^ 7 -
            3538944 / 55 * x ^ 8 + 3145728 / 11 * x ^ 9) - 4 / 5 * x ≤ 0 := by
      rw [hfactor]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hP
    exact sub_nonpos.mp hdiff
  have hlowerPoly :
      0 ≤ 4 / 5 * x - 144 / 175 * x ^ 2 + 128 / 105 * x ^ 3 -
          512 / 231 * x ^ 4 + 4608 / 1001 * x ^ 5 -
          14336 / 13 * x ^ 6 - 7602176 / 425 * x ^ 7 -
          1572864 / 85 * x ^ 8 := by
    have hfactor :
        (4 / 5 * x - 144 / 175 * x ^ 2 + 128 / 105 * x ^ 3 -
            512 / 231 * x ^ 4 + 4608 / 1001 * x ^ 5 -
            14336 / 13 * x ^ 6 - 7602176 / 425 * x ^ 7 -
            1572864 / 85 * x ^ 8) -
          (4 / 5 * x - 144 / 175 * x ^ 2) =
        -128 * x ^ 3 / 1276275 *
          (184504320 * x ^ 5 + 178354176 * x ^ 4 + 10995600 * x ^ 3 -
            45900 * x ^ 2 + 22100 * x - 12155) := by ring
    have hdiff : 0 ≤
        (4 / 5 * x - 144 / 175 * x ^ 2 + 128 / 105 * x ^ 3 -
            512 / 231 * x ^ 4 + 4608 / 1001 * x ^ 5 -
            14336 / 13 * x ^ 6 - 7602176 / 425 * x ^ 7 -
            1572864 / 85 * x ^ 8) -
          (4 / 5 * x - 144 / 175 * x ^ 2) := by
      rw [hfactor]
      have hcoeff : -128 * x ^ 3 / 1276275 ≤ 0 := by
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (pow_nonneg hx0.le 3))
          (by norm_num)
      exact mul_nonneg_of_nonpos_of_nonpos hcoeff hR
    have hbase : 0 ≤ 4 / 5 * x - 144 / 175 * x ^ 2 := by
      have hcoef : 0 ≤ (4 / 5 : ℝ) - 144 / 175 * x := by
        nlinarith
      nlinarith [mul_nonneg hx0.le hcoef]
    linarith
  exact ⟨hlowerPoly.trans hlower, hupper.trans hupperPoly⟩

theorem upperPoly_next_le_lowerPoly (k : ℕ) :
    upperPoly
        (TraceEuclidean.PoitouDegreeEleven.poitouY /
          (((k + 4 : ℕ) : ℝ) ^ 2)) ≤
      lowerPoly
        (TraceEuclidean.PoitouDegreeEleven.poitouY /
          (((k + 3 : ℕ) : ℝ) ^ 2)) := by
  rw [← sub_nonneg]
  dsimp [upperPoly, lowerPoly,
    TraceEuclidean.PoitouDegreeEleven.poitouY]
  push_cast
  field_simp
  ring_nf
  positivity

/-- The small arguments used in the alternating part of Poitou's `L₁`. -/
def smallL (k : ℕ) : ℝ :=
  TraceEuclidean.PoitouDegreeEleven.poitouLClosed
    (TraceEuclidean.PoitouDegreeEleven.poitouY /
      (((k + 3 : ℕ) : ℝ) ^ 2))

theorem smallL_antitone : Antitone smallL := by
  apply antitone_nat_of_succ_le
  intro k
  let x₀ : ℝ := TraceEuclidean.PoitouDegreeEleven.poitouY /
    (((k + 3 : ℕ) : ℝ) ^ 2)
  let x₁ : ℝ := TraceEuclidean.PoitouDegreeEleven.poitouY /
    (((k + 4 : ℕ) : ℝ) ^ 2)
  have hx₀pos : 0 < x₀ := by
    dsimp [x₀, TraceEuclidean.PoitouDegreeEleven.poitouY]
    positivity
  have hx₁pos : 0 < x₁ := by
    dsimp [x₁, TraceEuclidean.PoitouDegreeEleven.poitouY]
    positivity
  have hx₀c : x₀ ≤ (1351 / 18000 : ℝ) := by
    dsimp [x₀, TraceEuclidean.PoitouDegreeEleven.poitouY]
    apply (div_le_iff₀ (by positivity :
      0 < (((k + 3 : ℕ) : ℝ) ^ 2))).2
    have hk : (3 : ℝ) ≤ ((k + 3 : ℕ) : ℝ) := by norm_num
    nlinarith [sq_nonneg (((k + 3 : ℕ) : ℝ) - 3)]
  have hx₁c : x₁ ≤ (1351 / 18000 : ℝ) := by
    dsimp [x₁, TraceEuclidean.PoitouDegreeEleven.poitouY]
    apply (div_le_iff₀ (by positivity :
      0 < (((k + 4 : ℕ) : ℝ) ^ 2))).2
    have hk : (3 : ℝ) ≤ ((k + 4 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 3 ≤ k + 4)
    nlinarith [sq_nonneg (((k + 4 : ℕ) : ℝ) - 3)]
  have hu := poitouLClosed_le_upperCrude hx₁pos (by nlinarith : 4 * x₁ < 1)
  have hl := lowerCrude_le_poitouLClosed hx₀pos (by nlinarith : 4 * x₀ < 1)
  rw [upperCrude_eq_poly hx₁pos] at hu
  rw [lowerCrude_eq_poly hx₀pos] at hl
  change TraceEuclidean.PoitouDegreeEleven.poitouLClosed x₁ ≤
    upperPoly x₁ at hu
  change lowerPoly x₀ ≤
    TraceEuclidean.PoitouDegreeEleven.poitouLClosed x₀ at hl
  change TraceEuclidean.PoitouDegreeEleven.poitouLClosed x₁ ≤
    TraceEuclidean.PoitouDegreeEleven.poitouLClosed x₀
  have hpoly : upperPoly x₁ ≤ lowerPoly x₀ := by
    simpa [x₀, x₁] using upperPoly_next_le_lowerPoly k
  exact hu.trans (hpoly.trans hl)

/-- A sharp lower bound for the only large negative term in Poitou's
alternating series.  The proof uses the atanh series for `log (1 + y)` and
the identity `arctan s + arctan ((1 - s) / (1 + s)) = pi / 4`. -/
theorem poitouLClosed_quarter_lower :
    (11616055 / 100000000 : ℝ) <
      TraceEuclidean.PoitouDegreeEleven.poitouLClosed
        (TraceEuclidean.PoitouDegreeEleven.poitouY / 4) := by
  let y : ℝ := TraceEuclidean.PoitouDegreeEleven.poitouY
  let x : ℝ := y / 4
  let s : ℝ := Real.sqrt y
  let q : ℝ := (1 - s) / (1 + s)
  let q₀ : ℝ := 977622789 / 10000000000
  let z : ℝ := 1351 / 5351
  have hy0 : 0 < y := by
    norm_num [y, TraceEuclidean.PoitouDegreeEleven.poitouY]
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hs0 : 0 < s := by
    exact Real.sqrt_pos.2 hy0
  have hsSq : s ^ 2 = y := by
    exact Real.sq_sqrt hy0.le
  have hy1 : y < 1 := by
    norm_num [y, TraceEuclidean.PoitouDegreeEleven.poitouY]
  have hs1 : s < 1 := by
    nlinarith
  have hsUpper : s < (8218880703 / 10000000000 : ℝ) := by
    simpa [s, y] using
      TraceEuclidean.PoitouDegreeEleven.sqrt_y_bounds.2
  have hqden : 0 < 1 + s := by positivity
  have hq0 : 0 < q := by
    dsimp [q]
    exact div_pos (by linarith) hqden
  have hq1 : q < 1 := by
    dsimp [q]
    exact (div_lt_one hqden).2 (by linarith)
  have hq₀0 : 0 ≤ q₀ := by norm_num [q₀]
  have hq₀1 : q₀ < 1 := by norm_num [q₀]
  have hq₀q : q₀ < q := by
    dsimp [q, q₀]
    rw [lt_div_iff₀ hqden]
    nlinarith
  have hprod : s * q < 1 := by
    calc
      s * q < 1 * q := mul_lt_mul_of_pos_right hs1 hq0
      _ < 1 := by simpa using hq1
  have hratio : (s + q) / (1 - s * q) = 1 := by
    apply (div_eq_one_iff_eq (ne_of_gt (sub_pos.mpr hprod))).2
    dsimp [q]
    field_simp [ne_of_gt hqden]
    ring
  have hadd := Real.arctan_add hprod
  rw [hratio, Real.arctan_one] at hadd
  have hatanLower := arctan_lower hq₀0 hq₀1 4
  have hatanLower' :
      (∑ n ∈ range 8, (-1 : ℝ) ^ n * atanTerm q₀ n) <
        Real.arctan q := by
    exact hatanLower.trans_lt (Real.arctan_strictMono hq₀q)
  have hatanUpper :
      Real.arctan s <
        (3.14159265358979323847 : ℝ) / 4 -
          ∑ n ∈ range 8, (-1 : ℝ) ^ n * atanTerm q₀ n := by
    linarith [Real.pi_lt_d20]
  have hz0 : 0 ≤ z := by norm_num [z]
  have hz1 : z < 1 := by norm_num [z]
  have hlog := Real.sum_range_le_log_div hz0 hz1 8
  have hzratio : (1 + z) / (1 - z) = 1 + y := by
    norm_num [z, y, TraceEuclidean.PoitouDegreeEleven.poitouY]
  rw [hzratio] at hlog
  have hfour : 1 + 4 * x = 1 + y := by dsimp [x]; ring
  have hlog' :
      2 * ∑ i ∈ range 8, z ^ (2 * i + 1) / (2 * i + 1) ≤
        Real.log (1 + 4 * x) := by
    rw [hfour]
    nlinarith [hlog]
  have hsxLower :
      (8218880702 / 10000000000 : ℝ) / 2 < Real.sqrt x := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num [x, y, TraceEuclidean.PoitouDegreeEleven.poitouY]
  have hsqrtArg : 2 * Real.sqrt x = s := by
    have hxSq := Real.sq_sqrt hx0.le
    have hsx0 := Real.sqrt_nonneg x
    nlinarith
  have hB : 0 < 3 / (80 * x ^ 3) + 3 / (4 * x ^ 2) := by positivity
  have hlogMul := mul_le_mul_of_nonneg_left hlog' hB.le
  have hnum : 0 < 3 / x + 12 / 5 := by positivity
  have hC :
      (3 / x + 12 / 5) / Real.sqrt x <
        (3 / x + 12 / 5) /
          ((8218880702 / 10000000000 : ℝ) / 2) := by
    exact div_lt_div_of_pos_left hnum (by norm_num) hsxLower
  have hatan0 : 0 < Real.arctan s := Real.arctan_pos.mpr hs0
  have hcup : 0 <
      (3 / x + 12 / 5) /
        ((8218880702 / 10000000000 : ℝ) / 2) := by positivity
  have hprodUpper :
      ((3 / x + 12 / 5) / Real.sqrt x) * Real.arctan s <
        ((3 / x + 12 / 5) /
          ((8218880702 / 10000000000 : ℝ) / 2)) *
          ((3.14159265358979323847 : ℝ) / 4 -
            ∑ n ∈ range 8, (-1 : ℝ) ^ n * atanTerm q₀ n) := by
    calc
      ((3 / x + 12 / 5) / Real.sqrt x) * Real.arctan s <
          ((3 / x + 12 / 5) /
            ((8218880702 / 10000000000 : ℝ) / 2)) *
            Real.arctan s := mul_lt_mul_of_pos_right hC hatan0
      _ < _ := mul_lt_mul_of_pos_left hatanUpper hcup
  have hrat :
      (11616055 / 100000000 : ℝ) <
        -3 / (20 * x ^ 2) + 33 / (10 * x) + 2 +
          (3 / (80 * x ^ 3) + 3 / (4 * x ^ 2)) *
            (2 * ∑ i ∈ range 8, z ^ (2 * i + 1) / (2 * i + 1)) -
          ((3 / x + 12 / 5) /
            ((8218880702 / 10000000000 : ℝ) / 2)) *
            ((3.14159265358979323847 : ℝ) / 4 -
              ∑ n ∈ range 8, (-1 : ℝ) ^ n * atanTerm q₀ n) := by
    norm_num [x, y, z, q₀, atanTerm, Finset.sum_range_succ,
      TraceEuclidean.PoitouDegreeEleven.poitouY]
  rw [← hsqrtArg] at hprodUpper
  change (11616055 / 100000000 : ℝ) <
    -3 / (20 * x ^ 2) + 33 / (10 * x) + 2 +
      (3 / (80 * x ^ 3) + 3 / (4 * x ^ 2)) * Real.log (1 + 4 * x) -
      ((3 / x + 12 / 5) / Real.sqrt x) *
        Real.arctan (2 * Real.sqrt x)
  linarith

theorem poitouLClosed_nine_upper :
    TraceEuclidean.PoitouDegreeEleven.poitouLClosed
        (TraceEuclidean.PoitouDegreeEleven.poitouY / 9) <
      (5586350 / 100000000 : ℝ) := by
  have hx0 : 0 <
      TraceEuclidean.PoitouDegreeEleven.poitouY / 9 := by
    norm_num [TraceEuclidean.PoitouDegreeEleven.poitouY]
  have h := poitouLClosed_le_upperFine hx0 (by
    norm_num [TraceEuclidean.PoitouDegreeEleven.poitouY])
  rw [upperFine_eq_poly hx0] at h
  have hp : fineUpperPoly
      (TraceEuclidean.PoitouDegreeEleven.poitouY / 9) <
        (5586350 / 100000000 : ℝ) := by
    norm_num [fineUpperPoly, TraceEuclidean.PoitouDegreeEleven.poitouY]
  exact h.trans_lt hp

theorem poitouLClosed_sixteen_lower :
    (3239357 / 100000000 : ℝ) <
      TraceEuclidean.PoitouDegreeEleven.poitouLClosed
        (TraceEuclidean.PoitouDegreeEleven.poitouY / 16) := by
  have hx0 : 0 <
      TraceEuclidean.PoitouDegreeEleven.poitouY / 16 := by
    norm_num [TraceEuclidean.PoitouDegreeEleven.poitouY]
  have h := lowerFine_le_poitouLClosed hx0 (by
    norm_num [TraceEuclidean.PoitouDegreeEleven.poitouY])
  rw [lowerFine_eq_poly hx0] at h
  have hp : (3239357 / 100000000 : ℝ) < fineLowerPoly
      (TraceEuclidean.PoitouDegreeEleven.poitouY / 16) := by
    norm_num [fineLowerPoly, TraceEuclidean.PoitouDegreeEleven.poitouY]
  exact hp.trans_le h

theorem poitouLClosed_twentyFive_upper :
    TraceEuclidean.PoitouDegreeEleven.poitouLClosed
        (TraceEuclidean.PoitouDegreeEleven.poitouY / 25) <
      (2103818 / 100000000 : ℝ) := by
  have hx0 : 0 <
      TraceEuclidean.PoitouDegreeEleven.poitouY / 25 := by
    norm_num [TraceEuclidean.PoitouDegreeEleven.poitouY]
  have h := poitouLClosed_le_upperFine hx0 (by
    norm_num [TraceEuclidean.PoitouDegreeEleven.poitouY])
  rw [upperFine_eq_poly hx0] at h
  have hp : fineUpperPoly
      (TraceEuclidean.PoitouDegreeEleven.poitouY / 25) <
        (2103818 / 100000000 : ℝ) := by
    norm_num [fineUpperPoly, TraceEuclidean.PoitouDegreeEleven.poitouY]
  exact h.trans_lt hp

def firstPoitouTerm (k : ℕ) : ℝ :=
  TraceEuclidean.PoitouDegreeEleven.poitouLClosed
      (TraceEuclidean.PoitouDegreeEleven.poitouY /
        ((2 * k + 1 : ℕ) : ℝ) ^ 2) /
    ((2 * k + 1 : ℕ) : ℝ)

def alternatingPoitouTerm (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k *
    TraceEuclidean.PoitouDegreeEleven.poitouLClosed
      (TraceEuclidean.PoitouDegreeEleven.poitouY /
        ((k + 1 : ℕ) : ℝ) ^ 2)

theorem summable_firstPoitouTerm : Summable firstPoitouTerm := by
  apply (summable_nat_add_iff 1).mp
  have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (3 : ℕ)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hi : Function.Injective (fun k : ℕ => 2 * k + 3) := by
    intro a b hab
    exact Nat.mul_left_cancel (by omega) (Nat.add_right_cancel hab)
  have hmajor : Summable (fun k : ℕ =>
      (4 / 5 * TraceEuclidean.PoitouDegreeEleven.poitouY) /
        (((2 * k + 3 : ℕ) : ℝ) ^ 3)) := by
    have hc := hp.comp_injective hi
    have hm := hc.mul_left
      (4 / 5 * TraceEuclidean.PoitouDegreeEleven.poitouY)
    simpa [Function.comp_def, div_eq_mul_inv, mul_assoc] using hm
  apply hmajor.of_norm_bounded
  intro k
  let d : ℝ := ((2 * k + 3 : ℕ) : ℝ)
  let x : ℝ := TraceEuclidean.PoitouDegreeEleven.poitouY / d ^ 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hx0 : 0 < x := by
    dsimp [x, TraceEuclidean.PoitouDegreeEleven.poitouY]
    positivity
  have hxc : x ≤ (1351 / 18000 : ℝ) := by
    dsimp [x, d, TraceEuclidean.PoitouDegreeEleven.poitouY]
    apply (div_le_iff₀ (by positivity :
      0 < (((2 * k + 3 : ℕ) : ℝ) ^ 2))).2
    have hk : (3 : ℝ) ≤ ((2 * k + 3 : ℕ) : ℝ) := by
      norm_num
    nlinarith [sq_nonneg (((2 * k + 3 : ℕ) : ℝ) - 3)]
  have hL := poitouLClosed_small_bounds hx0 hxc
  rw [show firstPoitouTerm (k + 1) =
      TraceEuclidean.PoitouDegreeEleven.poitouLClosed x / d by
    simp [firstPoitouTerm, x, d, Nat.mul_add]
    ring]
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hL.1 hd.le)]
  calc
    TraceEuclidean.PoitouDegreeEleven.poitouLClosed x / d ≤
        (4 / 5 * x) / d := div_le_div_of_nonneg_right hL.2 hd.le
    _ = (4 / 5 * TraceEuclidean.PoitouDegreeEleven.poitouY) / d ^ 3 := by
      dsimp [x]
      field_simp
    _ = (4 / 5 * TraceEuclidean.PoitouDegreeEleven.poitouY) /
        (((2 * k + 3 : ℕ) : ℝ) ^ 3) := by rfl

theorem summable_alternatingPoitouTerm : Summable alternatingPoitouTerm := by
  apply (summable_nat_add_iff 2).mp
  have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℕ)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hi : Function.Injective (fun k : ℕ => k + 3) := by
    intro a b hab
    exact Nat.add_right_cancel hab
  have hmajor : Summable (fun k : ℕ =>
      (4 / 5 * TraceEuclidean.PoitouDegreeEleven.poitouY) /
        (((k + 3 : ℕ) : ℝ) ^ 2)) := by
    have hc := hp.comp_injective hi
    have hm := hc.mul_left
      (4 / 5 * TraceEuclidean.PoitouDegreeEleven.poitouY)
    simpa [Function.comp_def, div_eq_mul_inv, mul_assoc] using hm
  apply hmajor.of_norm_bounded
  intro k
  let d : ℝ := ((k + 3 : ℕ) : ℝ)
  let x : ℝ := TraceEuclidean.PoitouDegreeEleven.poitouY / d ^ 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hx0 : 0 < x := by
    dsimp [x, TraceEuclidean.PoitouDegreeEleven.poitouY]
    positivity
  have hxc : x ≤ (1351 / 18000 : ℝ) := by
    dsimp [x, d, TraceEuclidean.PoitouDegreeEleven.poitouY]
    apply (div_le_iff₀ (by positivity :
      0 < (((k + 3 : ℕ) : ℝ) ^ 2))).2
    have hk : (3 : ℝ) ≤ ((k + 3 : ℕ) : ℝ) := by
      norm_num
    nlinarith [sq_nonneg (((k + 3 : ℕ) : ℝ) - 3)]
  have hL := poitouLClosed_small_bounds hx0 hxc
  rw [show alternatingPoitouTerm (k + 2) =
      (-1 : ℝ) ^ k *
        TraceEuclidean.PoitouDegreeEleven.poitouLClosed x by
    simp [alternatingPoitouTerm, x, d, pow_add]
    ring]
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg hL.1]
  calc
    TraceEuclidean.PoitouDegreeEleven.poitouLClosed x ≤ 4 / 5 * x := hL.2
    _ = (4 / 5 * TraceEuclidean.PoitouDegreeEleven.poitouY) / d ^ 2 := by
      dsimp [x]
      field_simp
    _ = (4 / 5 * TraceEuclidean.PoitouDegreeEleven.poitouY) /
        (((k + 3 : ℕ) : ℝ) ^ 2) := by rfl

end
end TraceEuclidean.PoitouSeriesBounds
