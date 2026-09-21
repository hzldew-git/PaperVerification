import Mathlib

/-!
Kernel-checked finite consequences of the admissible-pair tables in the frozen
Trace-Euclidean v15 input (SHA-256
`83a236e93648ce0802f8a0d3022de63710d089f3a4f7e61214a4c855459597b5`).

The rational-interval verifier establishes that these are exactly the pairs in
the `1 ≤ n ≤ 34`, `1 ≤ d ≤ 14` grid which satisfy the numerical necessary
condition.  This module independently checks the finite table, its row and
column maxima, and the consequences quoted after equation (4.5).  It does not
internalize the cited field-discriminant lower bounds or the analytic interval
proofs for `π` and `exp`.
-/

namespace TraceEuclidean

/-- The 24 pairs retained by the classic-integral necessary condition.  The
order is degree first and rank second, as in the public exact verifier. -/
def v15ClassicAdmissiblePairs : List (ℕ × ℕ) :=
  [(1, 1), (2, 1), (3, 1), (4, 1), (5, 1), (6, 1),
   (7, 1), (8, 1), (9, 1), (10, 1), (11, 1), (12, 1),
   (1, 2), (2, 2), (3, 2), (4, 2), (5, 2),
   (1, 3), (2, 3), (3, 3),
   (1, 4), (2, 4), (1, 5), (1, 6)]

/-- The 63 pairs retained by the integral necessary condition. -/
def v15IntegralAdmissiblePairs : List (ℕ × ℕ) :=
  [(1, 1), (2, 1), (3, 1), (4, 1), (5, 1), (6, 1),
   (7, 1), (8, 1), (9, 1), (10, 1), (11, 1), (12, 1),
   (13, 1), (14, 1), (15, 1), (16, 1), (17, 1), (18, 1),
   (19, 1), (20, 1), (21, 1), (22, 1), (23, 1), (24, 1),
   (25, 1), (26, 1), (27, 1), (28, 1), (29, 1),
   (1, 2), (2, 2), (3, 2), (4, 2), (5, 2), (6, 2),
   (7, 2), (8, 2), (9, 2), (10, 2), (11, 2), (12, 2),
   (1, 3), (2, 3), (3, 3), (4, 3), (5, 3), (6, 3), (7, 3),
   (1, 4), (2, 4), (3, 4), (4, 4), (5, 4),
   (1, 5), (2, 5), (3, 5), (4, 5),
   (1, 6), (2, 6), (3, 6),
   (2, 7), (2, 8), (2, 9)]

/-- Maximum retained rank at a fixed degree, computed from a pair table. -/
def v15TableRankBound (pairs : List (ℕ × ℕ)) (d : ℕ) : ℕ :=
  (pairs.filter fun p ↦ p.2 == d).foldl (fun bound p ↦ max bound p.1) 0

/-- Maximum retained degree at a fixed rank, computed from a pair table. -/
def v15TableDegreeBound (pairs : List (ℕ × ℕ)) (n : ℕ) : ℕ :=
  (pairs.filter fun p ↦ p.1 == n).foldl (fun bound p ↦ max bound p.2) 0

theorem v15_classic_table_pair_count : v15ClassicAdmissiblePairs.length = 24 := by
  decide

theorem v15_integral_table_pair_count : v15IntegralAdmissiblePairs.length = 63 := by
  decide

/-- Table 2: the fourteen rank bounds, one for each degree `1, …, 14`. -/
theorem v15_classic_rank_bounds_by_degree :
    (List.range 14).map
        (fun i ↦ v15TableRankBound v15ClassicAdmissiblePairs (i + 1)) =
      [12, 5, 3, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide

/-- Table 2: the thirty-four degree bounds, one for each rank `1, …, 34`. -/
theorem v15_classic_degree_bounds_by_rank :
    (List.range 34).map
        (fun i ↦ v15TableDegreeBound v15ClassicAdmissiblePairs (i + 1)) =
      [6, 4, 3, 2, 2, 1, 1, 1, 1, 1, 1, 1,
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide

/-- Table 4: the fourteen rank bounds, one for each degree `1, …, 14`. -/
theorem v15_integral_rank_bounds_by_degree :
    (List.range 14).map
        (fun i ↦ v15TableRankBound v15IntegralAdmissiblePairs (i + 1)) =
      [29, 12, 7, 5, 4, 3, 2, 2, 2, 0, 0, 0, 0, 0] := by
  decide

/-- Table 4: the thirty-four degree bounds, one for each rank `1, …, 34`. -/
theorem v15_integral_degree_bounds_by_rank :
    (List.range 34).map
        (fun i ↦ v15TableDegreeBound v15IntegralAdmissiblePairs (i + 1)) =
      [6, 9, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2,
       1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
       0, 0, 0, 0, 0] := by
  decide

/-- Every retained classic-integral pair has rank at most 12 and degree at
most 6; both bounds occur in the table. -/
theorem v15_classic_table_exact_global_maxima :
    (12, 1) ∈ v15ClassicAdmissiblePairs ∧
      (1, 6) ∈ v15ClassicAdmissiblePairs ∧
      ∀ n d, (n, d) ∈ v15ClassicAdmissiblePairs → n ≤ 12 ∧ d ≤ 6 := by
  constructor
  · decide
  constructor
  · decide
  intro n d h
  simp [v15ClassicAdmissiblePairs] at h
  omega

/-- Every retained integral pair has rank at most 29 and degree at most 9;
both bounds occur in the table. -/
theorem v15_integral_table_exact_global_maxima :
    (29, 1) ∈ v15IntegralAdmissiblePairs ∧
      (2, 9) ∈ v15IntegralAdmissiblePairs ∧
      ∀ n d, (n, d) ∈ v15IntegralAdmissiblePairs → n ≤ 29 ∧ d ≤ 9 := by
  constructor
  · decide
  constructor
  · decide
  intro n d h
  simp [v15IntegralAdmissiblePairs] at h
  omega

/-- In the integral table, degrees 7, 8, and 9 retain exactly rank 2. -/
theorem v15_integral_table_degree_seven_to_nine {n d : ℕ}
    (h : (n, d) ∈ v15IntegralAdmissiblePairs) (hd : 7 ≤ d) :
    n = 2 ∧ d ≤ 9 := by
  simp [v15IntegralAdmissiblePairs] at h
  omega

/-- For positive degree at least two, the integral table already gives the
rank bound 12 used in Remark 1.4(iv). -/
theorem v15_integral_table_rank_le_twelve_of_degree_ge_two {n d : ℕ}
    (h : (n, d) ∈ v15IntegralAdmissiblePairs) (hd : 2 ≤ d) :
    n ≤ 12 := by
  simp [v15IntegralAdmissiblePairs] at h
  omega

/-- Combining the integral table with any independent degree-one rank bound
at most 10 gives the manuscript's overall rank bound 12. -/
theorem v15_integral_table_overall_rank_le_twelve {n d : ℕ}
    (h : (n, d) ∈ v15IntegralAdmissiblePairs)
    (hDegreeOne : d = 1 → n ≤ 10) :
    n ≤ 12 := by
  by_cases hd : d = 1
  · exact (hDegreeOne hd).trans (by omega)
  · exact v15_integral_table_rank_le_twelve_of_degree_ge_two h (by
      have hpos := (v15_integral_table_exact_global_maxima.2.2 n d h).2
      have : 0 < d := by
        simp [v15IntegralAdmissiblePairs] at h
        omega
      omega)

/-- Both extracted tables lie inside the finite grid proved in Corollary 4.3. -/
theorem v15_admissible_tables_inside_finite_grid :
    (∀ n d, (n, d) ∈ v15ClassicAdmissiblePairs →
      1 ≤ n ∧ n ≤ 34 ∧ 1 ≤ d ∧ d ≤ 14) ∧
    (∀ n d, (n, d) ∈ v15IntegralAdmissiblePairs →
      1 ≤ n ∧ n ≤ 34 ∧ 1 ≤ d ∧ d ≤ 14) := by
  constructor <;> intro n d h
  · simp [v15ClassicAdmissiblePairs] at h
    omega
  · simp [v15IntegralAdmissiblePairs] at h
    omega

end TraceEuclidean
