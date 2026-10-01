import TraceEuclidean.PoitouFiniteSums

/-!
# Closed numerical certificate for Poitou's degree-eleven row

This file combines the analytic point bounds, two kernel-checked finite sums,
and a telescoping tail estimate.  It proves the formerly assumed
`PoitouL1UpperCertificate`.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

open scoped BigOperators
open Finset Filter

namespace TraceEuclidean.PoitouDegreeElevenClosed

open TraceEuclidean.PoitouDegreeEleven
open TraceEuclidean.PoitouSeriesBounds

private theorem cubeTail151 :
    (∑' k : ℕ, 1 / (((k + 151 : ℕ) : ℝ) ^ 3)) ≤
      (1 / (150 * 151) : ℝ) := by
  let a : ℕ → ℝ := fun k =>
    1 / (((k + 150 : ℕ) : ℝ)) - 1 / (((k + 151 : ℕ) : ℝ))
  have hcomp (k : ℕ) :
      1 / (((k + 151 : ℕ) : ℝ) ^ 3) ≤ a k - a (k + 1) := by
    dsimp [a]
    push_cast
    field_simp
    ring_nf
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have hk2 : (0 : ℝ) ≤ (k : ℝ) ^ 2 := sq_nonneg _
    have hk3 : (0 : ℝ) ≤ (k : ℝ) ^ 3 := by positivity
    nlinarith
  have hnonneg (k : ℕ) : 0 ≤ a k - a (k + 1) :=
    (by positivity : 0 ≤ 1 / (((k + 151 : ℕ) : ℝ) ^ 3)).trans (hcomp k)
  have h150 : Tendsto
      (fun k : ℕ => 1 / (((k + 150 : ℕ) : ℝ))) atTop (nhds 0) := by
    simpa [Function.comp_def, Nat.cast_add] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat 150)
  have h151 : Tendsto
      (fun k : ℕ => 1 / (((k + 151 : ℕ) : ℝ))) atTop (nhds 0) := by
    simpa [Function.comp_def, Nat.cast_add] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat 151)
  have ha : Tendsto a atTop (nhds 0) := by
    simpa [a] using h150.sub h151
  have hpartial (m : ℕ) :
      (∑ k ∈ range m, (a k - a (k + 1))) = a 0 - a m := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [sum_range_succ, ih]
        ring
  have ht : Tendsto
      (fun m => ∑ k ∈ range m, (a k - a (k + 1)))
      atTop (nhds (a 0)) := by
    simpa [hpartial] using (tendsto_const_nhds.sub ha)
  have htel : HasSum (fun k => a k - a (k + 1)) (a 0) :=
    (hasSum_iff_tendsto_nat_of_nonneg hnonneg (a 0)).2 ht
  have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (3 : ℕ)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hi : Function.Injective (fun k : ℕ => k + 151) := by
    intro i j h
    exact Nat.add_right_cancel h
  have hcube : Summable (fun k : ℕ =>
      1 / (((k + 151 : ℕ) : ℝ) ^ 3)) := by
    simpa [Function.comp_def] using hp.comp_injective hi
  have hle := hcube.tsum_le_tsum hcomp htel.summable
  rw [htel.tsum_eq] at hle
  norm_num [a] at hle ⊢
  exact hle

private theorem firstTailUpper :
    (∑' k : ℕ, firstPoitouTerm (k + 151)) ≤
      (4 / 5 * poitouY) / (8 * 150 * 151) := by
  let c : ℝ := 4 / 5 * poitouY
  have hc : 0 ≤ c := by norm_num [c, poitouY]
  have hmajor : Summable (fun k : ℕ =>
      c / 8 * (1 / (((k + 151 : ℕ) : ℝ) ^ 3))) := by
    have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (3 : ℕ)) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have hi : Function.Injective (fun k : ℕ => k + 151) := by
      intro i j h
      exact Nat.add_right_cancel h
    have hshift : Summable (fun k : ℕ =>
        1 / (((k + 151 : ℕ) : ℝ) ^ 3)) := by
      simpa [Function.comp_def] using hp.comp_injective hi
    exact hshift.mul_left (c / 8)
  have htail : Summable (fun k : ℕ => firstPoitouTerm (k + 151)) :=
    (summable_nat_add_iff 151).2 summable_firstPoitouTerm
  have hterm (k : ℕ) :
      firstPoitouTerm (k + 151) ≤
        c / 8 * (1 / (((k + 151 : ℕ) : ℝ) ^ 3)) := by
    let n : ℕ := k + 151
    let d : ℝ := ((2 * n + 1 : ℕ) : ℝ)
    let x : ℝ := poitouY / d ^ 2
    have hn : 0 < n := by dsimp [n]; omega
    have hd : 0 < d := by dsimp [d]; positivity
    have hx : 0 < x := by dsimp [x, poitouY]; positivity
    have hxc : x ≤ (1351 / 18000 : ℝ) := by
      dsimp [x, d, poitouY]
      apply (div_le_iff₀ (by positivity :
        0 < (((2 * (k + 151) + 1 : ℕ) : ℝ) ^ 2))).2
      norm_num
      have hk : (3 : ℝ) ≤ ((2 * (k + 151) + 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 3 ≤ 2 * (k + 151) + 1)
      have hsq : (9 : ℝ) ≤ ((2 * (k + 151) + 1 : ℕ) : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (((2 * (k + 151) + 1 : ℕ) : ℝ) - 3)]
      push_cast at hsq
      nlinarith
    have hL := (poitouLClosed_small_bounds hx hxc).2
    have hfirst : firstPoitouTerm (k + 151) = poitouLClosed x / d := by
      simp [firstPoitouTerm, n, d, x, Nat.mul_add]
    rw [hfirst]
    calc
      poitouLClosed x / d ≤ (4 / 5 * x) / d :=
        div_le_div_of_nonneg_right hL hd.le
      _ = c / d ^ 3 := by
        dsimp [x, c]
        field_simp
      _ ≤ c / (((2 * n : ℕ) : ℝ) ^ 3) := by
        have hdn : ((2 * n : ℕ) : ℝ) ≤ d := by
          dsimp [d]
          exact_mod_cast (by omega : 2 * n ≤ 2 * n + 1)
        exact div_le_div_of_nonneg_left hc (by positivity)
          (pow_le_pow_left₀ (by positivity) hdn 3)
      _ = c / 8 * (1 / (((k + 151 : ℕ) : ℝ) ^ 3)) := by
        dsimp [n]
        push_cast
        field_simp
        ring
  have hsum := htail.tsum_le_tsum hterm hmajor
  calc
    (∑' k : ℕ, firstPoitouTerm (k + 151)) ≤
        ∑' k : ℕ, c / 8 * (1 / (((k + 151 : ℕ) : ℝ) ^ 3)) := hsum
    _ = c / 8 * (∑' k : ℕ, 1 / (((k + 151 : ℕ) : ℝ) ^ 3)) := by
      rw [tsum_mul_left]
    _ ≤ c / 8 * (1 / (150 * 151 : ℝ)) :=
      mul_le_mul_of_nonneg_left cubeTail151 (by positivity)
    _ = (4 / 5 * poitouY) / (8 * 150 * 151) := by
      dsimp [c]
      ring

private theorem alternating_odd_partial (f : ℕ → ℝ) (m : ℕ) :
    (∑ k ∈ range (2 * m + 1), (-1 : ℝ) ^ k * f k) =
      f 0 + ∑ j ∈ range m, (f (2 * j + 2) - f (2 * j + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega]
      rw [sum_range_succ, sum_range_succ, ih, sum_range_succ]
      simp [pow_add]
      ring

theorem firstPoitouSumUpper :
    (∑' k : ℕ, firstPoitouTerm k) < (367963 / 1000000 : ℝ) := by
  have hfirstThree :
      (∑ k ∈ range 3, firstPoitouTerm k) <
        (2105281197815083333790761031 /
            6164616377500000000000000000 : ℝ) +
          (5586350 / 100000000 : ℝ) / 3 +
          (2103818 / 100000000 : ℝ) / 5 := by
    have h0 := poitouLClosed_y_upper
    have h1 := poitouLClosed_nine_upper
    have h2 := poitouLClosed_twentyFive_upper
    norm_num [Finset.sum_range_succ, firstPoitouTerm] at h0 h1 h2 ⊢
    linarith
  have hfinite :
      (∑ k ∈ range 148, firstPoitouTerm (k + 3)) ≤
        (362056 / 100000000 : ℝ) := by
    have hterm (k : ℕ) :
        firstPoitouTerm (k + 3) ≤
          upperPoly (poitouY / (((2 * k + 7 : ℕ) : ℝ) ^ 2)) /
            ((2 * k + 7 : ℕ) : ℝ) := by
      have hx : 0 < poitouY / (((2 * k + 7 : ℕ) : ℝ) ^ 2) := by
        norm_num [poitouY]
        positivity
      have hx4 : 4 * (poitouY / (((2 * k + 7 : ℕ) : ℝ) ^ 2)) < 1 := by
        rw [show 4 * (poitouY / (((2 * k + 7 : ℕ) : ℝ) ^ 2)) =
          (4 * poitouY) / (((2 * k + 7 : ℕ) : ℝ) ^ 2) by ring]
        apply (div_lt_iff₀ (by positivity :
          0 < (((2 * k + 7 : ℕ) : ℝ) ^ 2))).2
        norm_num [poitouY]
        have hk : (7 : ℝ) ≤ ((2 * k + 7 : ℕ) : ℝ) := by norm_num
        have hsq : (49 : ℝ) ≤ ((2 * k + 7 : ℕ) : ℝ) ^ 2 := by
          nlinarith [sq_nonneg (((2 * k + 7 : ℕ) : ℝ) - 7)]
        push_cast at hsq
        nlinarith
      have hL := poitouLClosed_le_upperPoly hx hx4
      have hd : 0 ≤ ((2 * k + 7 : ℕ) : ℝ) := by positivity
      have hdiv := div_le_div_of_nonneg_right hL hd
      have hindex : 2 * (k + 3) + 1 = 2 * k + 7 := by omega
      simpa [firstPoitouTerm, hindex] using hdiv
    calc
      (∑ k ∈ range 148, firstPoitouTerm (k + 3)) ≤
          ∑ k ∈ range 148,
            upperPoly (poitouY / (((2 * k + 7 : ℕ) : ℝ) ^ 2)) /
              ((2 * k + 7 : ℕ) : ℝ) := by
        exact sum_le_sum fun k _ => hterm k
      _ ≤ (362056 / 100000000 : ℝ) := by
        have hset : Icc 0 147 = range 148 := by
          ext k
          simp
          omega
        rw [← hset]
        convert TraceEuclidean.PoitouFiniteSums.firstFiniteUpper using 1 <;>
          norm_num
  have hpartial :
      (∑ k ∈ range 151, firstPoitouTerm k) <
        (2105281197815083333790761031 /
            6164616377500000000000000000 : ℝ) +
          (5586350 / 100000000 : ℝ) / 3 +
          (2103818 / 100000000 : ℝ) / 5 +
          (362056 / 100000000 : ℝ) := by
    have hsplit :
        (∑ k ∈ range 151, firstPoitouTerm k) =
          (∑ k ∈ range 3, firstPoitouTerm k) +
            ∑ k ∈ range 148, firstPoitouTerm (k + 3) := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Finset.sum_range_add firstPoitouTerm 3 148)
    rw [hsplit]
    linarith
  have hseries := summable_firstPoitouTerm.sum_add_tsum_nat_add 151
  calc
    (∑' k : ℕ, firstPoitouTerm k) =
        (∑ k ∈ range 151, firstPoitouTerm k) +
          ∑' k : ℕ, firstPoitouTerm (k + 151) := by
      simpa [Nat.add_comm] using hseries.symm
    _ <
        ((2105281197815083333790761031 /
              6164616377500000000000000000 : ℝ) +
            (5586350 / 100000000 : ℝ) / 3 +
            (2103818 / 100000000 : ℝ) / 5 +
            (362056 / 100000000 : ℝ)) +
          (4 / 5 * poitouY) / (8 * 150 * 151) :=
      add_lt_add_of_lt_of_le hpartial firstTailUpper
    _ < (367963 / 1000000 : ℝ) := by
      norm_num [poitouY]

theorem alternatingPoitouSumUpper :
    (∑' k : ℕ, alternatingPoitouTerm k) <
      (261322 / 1000000 : ℝ) := by
  have hshift : Summable (fun k : ℕ => alternatingPoitouTerm (k + 2)) :=
    (summable_nat_add_iff 2).2 summable_alternatingPoitouTerm
  have hsmall : Summable (fun k : ℕ => (-1 : ℝ) ^ k * smallL k) := by
    simpa [alternatingPoitouTerm, smallL, pow_add, Nat.add_assoc] using hshift
  have hlimit := hsmall.hasSum.tendsto_sum_nat
  have halt :
      (∑' k : ℕ, (-1 : ℝ) ^ k * smallL k) ≤
        ∑ k ∈ range 399, (-1 : ℝ) ^ k * smallL k := by
    simpa using smallL_antitone.tendsto_le_alternating_series hlimit 199
  rw [alternating_odd_partial smallL 199] at halt
  have hzero :
      smallL 0 < (5586350 / 100000000 : ℝ) := by
    convert poitouLClosed_nine_upper using 1 <;> norm_num [smallL]
  have hpairZero :
      smallL 2 - smallL 1 <
        (2103818 / 100000000 : ℝ) -
          (3239357 / 100000000 : ℝ) := by
    have h5 := poitouLClosed_twentyFive_upper
    have h4 := poitouLClosed_sixteen_lower
    norm_num [smallL] at h5 h4 ⊢
    linarith
  have hpair (k : ℕ) (hk : k ∈ Icc 1 198) :
      smallL (2 * k + 2) - smallL (2 * k + 1) ≤
        upperPoly (poitouY / (((2 * k + 5 : ℕ) : ℝ) ^ 2)) -
          lowerPoly (poitouY / (((2 * k + 4 : ℕ) : ℝ) ^ 2)) := by
    have hodd0 : 0 < poitouY / (((2 * k + 5 : ℕ) : ℝ) ^ 2) := by
      norm_num [poitouY]
      positivity
    have heven0 : 0 < poitouY / (((2 * k + 4 : ℕ) : ℝ) ^ 2) := by
      norm_num [poitouY]
      positivity
    have hodd4 : 4 * (poitouY / (((2 * k + 5 : ℕ) : ℝ) ^ 2)) < 1 := by
      rw [show 4 * (poitouY / (((2 * k + 5 : ℕ) : ℝ) ^ 2)) =
        (4 * poitouY) / (((2 * k + 5 : ℕ) : ℝ) ^ 2) by ring]
      apply (div_lt_iff₀ (by positivity :
        0 < (((2 * k + 5 : ℕ) : ℝ) ^ 2))).2
      norm_num [poitouY]
      have hkNat : 1 ≤ k := (mem_Icc.mp hk).1
      have hk5Nat : 7 ≤ 2 * k + 5 := by omega
      have hk5 : (7 : ℝ) ≤ ((2 * k + 5 : ℕ) : ℝ) := by
        exact_mod_cast hk5Nat
      have hsq : (49 : ℝ) ≤ ((2 * k + 5 : ℕ) : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (((2 * k + 5 : ℕ) : ℝ) - 7)]
      push_cast at hsq
      nlinarith
    have heven4 : 4 * (poitouY / (((2 * k + 4 : ℕ) : ℝ) ^ 2)) < 1 := by
      rw [show 4 * (poitouY / (((2 * k + 4 : ℕ) : ℝ) ^ 2)) =
        (4 * poitouY) / (((2 * k + 4 : ℕ) : ℝ) ^ 2) by ring]
      apply (div_lt_iff₀ (by positivity :
        0 < (((2 * k + 4 : ℕ) : ℝ) ^ 2))).2
      norm_num [poitouY]
      have hkNat : 1 ≤ k := (mem_Icc.mp hk).1
      have hk4Nat : 6 ≤ 2 * k + 4 := by omega
      have hk4 : (6 : ℝ) ≤ ((2 * k + 4 : ℕ) : ℝ) := by
        exact_mod_cast hk4Nat
      have hsq : (36 : ℝ) ≤ ((2 * k + 4 : ℕ) : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (((2 * k + 4 : ℕ) : ℝ) - 6)]
      push_cast at hsq
      nlinarith
    have hodd := poitouLClosed_le_upperPoly hodd0 hodd4
    have heven := lowerPoly_le_poitouLClosed heven0 heven4
    have hoddIndex : (2 * k + 2) + 3 = 2 * k + 5 := by omega
    have hevenIndex : (2 * k + 1) + 3 = 2 * k + 4 := by omega
    simpa [smallL, hoddIndex, hevenIndex] using sub_le_sub hodd heven
  have hpairsTail :
      (∑ k ∈ Icc 1 198,
          (smallL (2 * k + 2) - smallL (2 * k + 1))) ≤
        (-853693 / 100000000 : ℝ) := by
    calc
      (∑ k ∈ Icc 1 198,
          (smallL (2 * k + 2) - smallL (2 * k + 1))) ≤
          ∑ k ∈ Icc 1 198,
            (upperPoly (poitouY / (((2 * k + 5 : ℕ) : ℝ) ^ 2)) -
              lowerPoly (poitouY / (((2 * k + 4 : ℕ) : ℝ) ^ 2))) := by
        exact sum_le_sum hpair
      _ ≤ (-853693 / 100000000 : ℝ) :=
        by
          convert TraceEuclidean.PoitouFiniteSums.alternatingPairsUpper using 1 <;>
            norm_num
  have hpairs :
      (∑ j ∈ range 199, (smallL (2 * j + 2) - smallL (2 * j + 1))) <
        ((2103818 / 100000000 : ℝ) -
          (3239357 / 100000000 : ℝ)) +
          (-853693 / 100000000 : ℝ) := by
    have hset : range 199 = insert 0 (Icc 1 198) := by
      ext k
      simp
      omega
    rw [hset, sum_insert (by simp)]
    linarith
  have hsmallUpper :
      (∑' k : ℕ, (-1 : ℝ) ^ k * smallL k) <
        (5586350 / 100000000 : ℝ) +
          ((2103818 / 100000000 : ℝ) -
            (3239357 / 100000000 : ℝ)) +
          (-853693 / 100000000 : ℝ) := by
    linarith
  have hfirstTwo :
      (∑ k ∈ range 2, alternatingPoitouTerm k) <
        (2105281197815083333790761031 /
            6164616377500000000000000000 : ℝ) -
          (11616055 / 100000000 : ℝ) := by
    have h1 := poitouLClosed_y_upper
    have h2 := poitouLClosed_quarter_lower
    norm_num [Finset.sum_range_succ, alternatingPoitouTerm] at h1 h2 ⊢
    linarith
  have hseries := summable_alternatingPoitouTerm.sum_add_tsum_nat_add 2
  have htailEq :
      (∑' k : ℕ, alternatingPoitouTerm (k + 2)) =
        ∑' k : ℕ, (-1 : ℝ) ^ k * smallL k := by
    apply tsum_congr
    intro k
    simp [alternatingPoitouTerm, smallL, pow_add, Nat.add_assoc]
  calc
    (∑' k : ℕ, alternatingPoitouTerm k) =
        (∑ k ∈ range 2, alternatingPoitouTerm k) +
          ∑' k : ℕ, alternatingPoitouTerm (k + 2) := hseries.symm
    _ = (∑ k ∈ range 2, alternatingPoitouTerm k) +
          ∑' k : ℕ, (-1 : ℝ) ^ k * smallL k := by rw [htailEq]
    _ <
        ((2105281197815083333790761031 /
              6164616377500000000000000000 : ℝ) -
            (11616055 / 100000000 : ℝ)) +
          ((5586350 / 100000000 : ℝ) +
            ((2103818 / 100000000 : ℝ) -
              (3239357 / 100000000 : ℝ)) +
            (-853693 / 100000000 : ℝ)) :=
      add_lt_add hfirstTwo hsmallUpper
    _ < (261322 / 1000000 : ℝ) := by norm_num

/-- The optimized degree-eleven `L₁` certificate, now proved without a
native-code decision procedure. -/
theorem poitouL1_upper_certificate : PoitouL1UpperCertificate := by
  have hfirst := firstPoitouSumUpper
  have halt := alternatingPoitouSumUpper
  dsimp [PoitouL1UpperCertificate, poitouL1]
  change (∑' k : ℕ, firstPoitouTerm k) +
      (∑' k : ℕ, alternatingPoitouTerm k) < (629291 / 1000000 : ℝ)
  linarith

theorem degreeElevenRootDiscriminantInput_of_poitouFormula
    (hFormula : PoitouDegreeElevenFormulaInput) :
    TraceEuclidean.DegreeElevenRootDiscriminantInput :=
  degreeElevenRootDiscriminantInput_of_poitou hFormula
    poitouL1_upper_certificate

end TraceEuclidean.PoitouDegreeElevenClosed
