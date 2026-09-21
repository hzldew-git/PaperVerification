import TraceEuclidean.V15AnalyticTable
import TraceEuclidean.V15OdlyzkoBridge

/-!
Class-level bridge from the cited field-discriminant bounds to the analytic
`H(n,d)` conditions and the two certified finite tables.  The source bounds
are explicit premises; their consequences are proved in Lean.
-/

namespace TraceEuclidean

noncomputable section

theorem v15BetaPower_pos (n d : ℕ) : 0 < v15BetaPower n d := by
  unfold v15BetaPower
  split_ifs
  · exact mul_pos (v15AlgebraicBetaPower_pos n d) (Real.exp_pos _)
  · exact v15AlgebraicBetaPower_pos n d

/-- The power used for a rank `n` lattice is the `n`-th power of the
degree-sized root-discriminant contribution. -/
theorem v15BetaPower_eq_one_pow (n d : ℕ) :
    v15BetaPower n d = v15BetaPower 1 d ^ n := by
  unfold v15BetaPower
  by_cases hd : 12 ≤ d
  · simp only [hd, if_true]
    rw [v15AlgebraicBetaPower_eq_degree_pow,
      v15AlgebraicBetaPower_eq_degree_pow]
    simp only [pow_one, Nat.cast_one, mul_one, mul_pow]
    rw [← Real.exp_nat_mul]
    congr 2
    ring
  · simp only [hd, if_false]
    rw [v15AlgebraicBetaPower_eq_degree_pow,
      v15AlgebraicBetaPower_eq_degree_pow, pow_one]

/-- Exact minima/root-discriminant estimates used in degrees at most eleven.
This remains an explicit external arithmetic input. -/
def V15SmallDegreeDiscriminantInput : Prop :=
  ∀ c : GlobalLatticeClass, c.degree ≤ 11 →
    v15BetaPower 1 c.degree ≤
      ((|c.fieldCode.discriminant| : ℤ) : ℝ)

/-- All field-discriminant estimates needed by the Section 4 tables. -/
def V15SectionFourDiscriminantInput : Prop :=
  ∀ c : GlobalLatticeClass,
    v15BetaPower 1 c.degree ≤
      ((|c.fieldCode.discriminant| : ℤ) : ℝ)

/-- The finite-degree input and Odlyzko's Table 4 row jointly supply the
piecewise `β_d` lower bound used in the manuscript. -/
theorem v15_sectionFourDiscriminantInput_of_sources
    (hSmall : V15SmallDegreeDiscriminantInput)
    (hTable : V15OdlyzkoTable4Input) :
    V15SectionFourDiscriminantInput := by
  intro c
  by_cases hd : c.degree ≤ 11
  · exact hSmall c hd
  · have hd12 : 12 ≤ c.degree := by omega
    have hd9 : ¬ c.degree ≤ 9 := by omega
    have hd10 : c.degree ≠ 10 := by omega
    have hd11 : c.degree ≠ 11 := by omega
    have h := (hTable c).le
    simpa [v15BetaPower, v15AlgebraicBetaPower, hd12, hd9, hd10,
      hd11] using h

private theorem v15_betaPower_le_discriminant_pow
    (hDisc : V15SectionFourDiscriminantInput)
    (c : GlobalLatticeClass) :
    v15BetaPower c.rank c.degree ≤
      ((|c.fieldCode.discriminant| : ℤ) : ℝ) ^ c.rank := by
  rw [v15BetaPower_eq_one_pow]
  exact pow_le_pow_left₀ (v15BetaPower_pos 1 c.degree).le (hDisc c) _

/-- A classic trace-Euclidean class satisfies the exact analytic table
condition once the cited field-discriminant bound is supplied. -/
theorem v15_classic_analyticH_necessary
    (hDisc : V15SectionFourDiscriminantInput)
    (c : GlobalLatticeClass)
    (hE : c.IsClassicTraceEuclidean (c.degree : ℝ)) :
    (1 : ℝ) ≤ v15AnalyticH c.rank c.degree := by
  have hd := c.degree_pos_v15
  have hbeta := v15_betaPower_le_discriminant_pow hDisc c
  have hvolume := GlobalFiniteness.classic_discriminant_pow_le_trace
    (c.degree : ℝ) c.rank c.degree c (by exact_mod_cast hd)
    ⟨hE, rfl, rfl⟩
  unfold v15AnalyticH
  apply (le_div_iff₀ (v15BetaPower_pos c.rank c.degree)).2
  simpa only [one_mul] using hbeta.trans hvolume

/-- Above rank one, an integral trace-Euclidean class satisfies the exact
`2^(-nd)` analytic table condition. -/
theorem v15_integral_analyticH_necessary_of_rank_ne_one
    (hDisc : V15SectionFourDiscriminantInput)
    (c : GlobalLatticeClass)
    (hE : c.IsIntegralTraceEuclidean (c.degree : ℝ))
    (hn1 : c.rank ≠ 1) :
    v15IntegralThreshold c.rank c.degree ≤
      v15AnalyticH c.rank c.degree := by
  have hd := c.degree_pos_v15
  have hbeta := v15_betaPower_le_discriminant_pow hDisc c
  have hvolume := GlobalFiniteness.integral_discriminant_pow_le_trace
    (c.degree : ℝ) c.rank c.degree c (by exact_mod_cast hd)
    ⟨hE, rfl, rfl⟩
  have hbound :
      v15BetaPower c.rank c.degree ≤
        (2 : ℝ) ^ (c.rank * c.degree) *
          (euclideanUnitBallVolume (c.rank * c.degree) ^ (2 : ℕ) *
            (c.degree : ℝ) ^ (c.rank * c.degree)) := by
    calc
      v15BetaPower c.rank c.degree ≤
          ((|c.fieldCode.discriminant| : ℤ) : ℝ) ^ c.rank := hbeta
      _ ≤ euclideanUnitBallVolume (c.rank * c.degree) ^ (2 : ℕ) *
          (2 * (c.degree : ℝ)) ^ (c.rank * c.degree) := hvolume
      _ = (2 : ℝ) ^ (c.rank * c.degree) *
          (euclideanUnitBallVolume (c.rank * c.degree) ^ (2 : ℕ) *
            (c.degree : ℝ) ^ (c.rank * c.degree)) := by
        rw [mul_pow]
        ring
  unfold v15IntegralThreshold v15AnalyticH
  simp only [hn1, if_false]
  apply (div_le_div_iff₀
    (pow_pos (by norm_num : (0 : ℝ) < 2) (c.rank * c.degree))
    (v15BetaPower_pos c.rank c.degree)).2
  simpa only [one_mul, mul_comm] using hbound

/-- The rank-one classic-integrality theorem supplies the special integral
threshold `H(1,d) ≥ 1`. -/
theorem v15_integral_analyticH_necessary
    (hDisc : V15SectionFourDiscriminantInput)
    (hRankOne : V15RankOneClassicInput)
    (c : GlobalLatticeClass)
    (hE : c.IsIntegralTraceEuclidean (c.degree : ℝ)) :
    v15IntegralThreshold c.rank c.degree ≤
      v15AnalyticH c.rank c.degree := by
  by_cases hn1 : c.rank = 1
  · have hclassic : c.IsClassicTraceEuclidean (c.degree : ℝ) :=
      ⟨hRankOne c hn1, hE⟩
    have h := v15_classic_analyticH_necessary hDisc c hclassic
    simp only [v15IntegralThreshold, hn1, if_true]
    simpa only [hn1] using h
  · exact v15_integral_analyticH_necessary_of_rank_ne_one
      hDisc c hE hn1

/-- Every classic class in the proved finite grid belongs to exactly one of
the 24 analytically admissible pairs. -/
theorem v15_classic_pair_mem_of_sources
    (hSmall : V15SmallDegreeDiscriminantInput)
    (hTable : V15OdlyzkoTable4Input)
    (c : GlobalLatticeClass)
    (hE : c.IsClassicTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15ClassicAdmissiblePairs := by
  have hDisc := v15_sectionFourDiscriminantInput_of_sources hSmall hTable
  apply (v15_classic_analytic_grid_iff_mem c.rank c.degree c.rank_pos
    (v15_integral_rank_le_34 c hE.2) c.degree_pos_v15
    (v15_classic_degree_le_14_of_odlyzko
      (v15_odlyzko_degree_input_of_table4 hTable) c hE)).mp
  exact v15_classic_analyticH_necessary hDisc c hE

/-- Every integral class in the proved finite grid belongs to exactly one of
the 63 analytically admissible pairs. -/
theorem v15_integral_pair_mem_of_sources
    (hSmall : V15SmallDegreeDiscriminantInput)
    (hTable : V15OdlyzkoTable4Input)
    (hRankOne : V15RankOneClassicInput)
    (c : GlobalLatticeClass)
    (hE : c.IsIntegralTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15IntegralAdmissiblePairs := by
  have hDisc := v15_sectionFourDiscriminantInput_of_sources hSmall hTable
  apply (v15_integral_analytic_grid_iff_mem c.rank c.degree c.rank_pos
    (v15_integral_rank_le_34 c hE) c.degree_pos_v15
    (v15_integral_degree_le_14_of_odlyzko
      (v15_odlyzko_degree_input_of_table4 hTable) hRankOne c hE)).mp
  exact v15_integral_analyticH_necessary hDisc hRankOne c hE

end

end TraceEuclidean
