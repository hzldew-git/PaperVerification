import TraceEuclidean.V15AnalyticTable
import TraceEuclidean.V15DegreeThreeDiscriminant
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

/-- Degree one is discharged internally by mathlib's Minkowski bound, rather
than being included in the external small-degree data. -/
theorem v15_degree_one_discriminant_bound
    (c : GlobalLatticeClass) (hd : c.degree = 1) :
    v15BetaPower 1 c.degree ≤
      ((|c.fieldCode.discriminant| : ℤ) : ℝ) := by
  have h := c.minkowski_discriminant_lower_bound
  rw [hd] at h ⊢
  norm_num [v15BetaPower, v15AlgebraicBetaPower,
    v15MinimumDiscriminant,
    totallyRealMinkowskiDiscriminantLowerBound] at h ⊢
  exact h

/-- Exact minimum-discriminant input in degrees two through nine.  A complete
enumeration certificate for the cited tables is still external. -/
def V15DegreeTwoToNineMinimumInput : Prop :=
  ∀ (K : CodedNumberField), NumberField.IsTotallyReal K.1 →
    let d := Module.finrank ℚ K.1
    2 ≤ d → d ≤ 9 →
      (v15MinimumDiscriminant d : ℝ) ≤
        ((|K.discriminant| : ℤ) : ℝ)

/-- The residual exact minimum-discriminant input in degrees three through
nine.  The degree-two row is proved internally in
`V15DegreeTwoDiscriminant`. -/
def V15DegreeThreeToNineMinimumInput : Prop :=
  ∀ (K : CodedNumberField), NumberField.IsTotallyReal K.1 →
    let d := Module.finrank ℚ K.1
    3 ≤ d → d ≤ 9 →
      (v15MinimumDiscriminant d : ℝ) ≤
        ((|K.discriminant| : ℤ) : ℝ)

/-- The residual exact minimum-discriminant input in degrees four through
nine, after replacing the cubic table row by the more structural Hunter
certificate. -/
def V15DegreeFourToNineMinimumInput : Prop :=
  ∀ (K : CodedNumberField), NumberField.IsTotallyReal K.1 →
    let d := Module.finrank ℚ K.1
    4 ≤ d → d ≤ 9 →
      (v15MinimumDiscriminant d : ℝ) ≤
        ((|K.discriminant| : ℤ) : ℝ)

/-- The cubic Hunter certificate and the residual degree-four to degree-nine
source input imply the earlier degree-three to degree-nine interface. -/
theorem v15_degreeThreeToNineMinimumInput_of_hunterCertificate
    (hHunter : V15DegreeThreeHunterCertificateInput)
    (hMin : V15DegreeFourToNineMinimumInput) :
    V15DegreeThreeToNineMinimumInput := by
  intro K hreal
  dsimp only
  intro hd3 hd9
  by_cases hdegree : Module.finrank ℚ K.1 = 3
  · simpa [hdegree, v15MinimumDiscriminant] using
      v15_coded_degree_three_discriminant_ge_49_of_hunterCertificate
        hHunter K hreal hdegree
  · exact hMin K hreal (by omega) hd9

/-- The internally proved quadratic bound and the residual degree-three to
degree-nine source input imply the earlier combined interface. -/
theorem v15_degreeTwoToNineMinimumInput_of_threeToNine
    (hMin : V15DegreeThreeToNineMinimumInput) :
    V15DegreeTwoToNineMinimumInput := by
  intro K hreal
  dsimp only
  intro hd2 hd9
  by_cases hdegree : Module.finrank ℚ K.1 = 2
  · simpa [hdegree, v15MinimumDiscriminant] using
      v15_coded_degree_two_discriminant_ge_five K hreal hdegree
  · exact hMin K hreal (by omega) hd9

/-- Voight's empty degree-ten range at root discriminant at most fourteen,
stated in the exact form needed by the Section 4 calculation. -/
def V15DegreeTenRootDiscriminantInput : Prop :=
  ∀ (K : CodedNumberField), NumberField.IsTotallyReal K.1 →
    Module.finrank ℚ K.1 = 10 →
      (14 : ℝ) ^ (10 : ℕ) < ((|K.discriminant| : ℤ) : ℝ)

/-- The optimized unconditional degree-eleven bound `δ_F > 14.083`, separated
from the weaker value in the online November 1976 Table 2. -/
def V15DegreeElevenRootDiscriminantInput : Prop :=
  ∀ (K : CodedNumberField), NumberField.IsTotallyReal K.1 →
    Module.finrank ℚ K.1 = 11 →
      (14083 / 1000 : ℝ) ^ (11 : ℕ) <
        ((|K.discriminant| : ℤ) : ℝ)

/-- Exact minima/root-discriminant estimates used in degrees at most eleven.
This remains an explicit external arithmetic input. -/
def V15SmallDegreeDiscriminantInput : Prop :=
  ∀ c : GlobalLatticeClass, c.degree ≤ 11 →
    v15BetaPower 1 c.degree ≤
      ((|c.fieldCode.discriminant| : ℤ) : ℝ)

/-- The three literature-facing field inputs, together with the internal
degree-one argument, imply the earlier class-level small-degree premise. -/
theorem v15_smallDegreeDiscriminantInput_of_literature
    (hMin : V15DegreeTwoToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput) :
    V15SmallDegreeDiscriminantInput := by
  intro c hd11
  by_cases hd1 : c.degree = 1
  · exact v15_degree_one_discriminant_bound c hd1
  have hd2 : 2 ≤ c.degree := by
    have hd0 := c.degree_pos_v15
    omega
  have hfin : Module.finrank ℚ c.fieldCode.1 = c.degree := by
    change Module.finrank ℚ c.representative.field.1 = c.degree
    exact c.representative_degree
  by_cases hd9 : c.degree ≤ 9
  · have h := hMin c.fieldCode c.representative.totallyReal
      (hfin ▸ hd2) (hfin ▸ hd9)
    rw [hfin] at h
    have hd12 : ¬ 12 ≤ c.degree := by omega
    simpa [v15BetaPower, v15AlgebraicBetaPower, hd9, hd12] using h
  by_cases hd10 : c.degree = 10
  · have h := hTen c.fieldCode c.representative.totallyReal (hfin.trans hd10)
    have hd12 : ¬ 12 ≤ c.degree := by omega
    simpa [v15BetaPower, v15AlgebraicBetaPower, hd9, hd10, hd12] using h.le
  · have hd11eq : c.degree = 11 := by omega
    have h := hEleven c.fieldCode c.representative.totallyReal
      (hfin.trans hd11eq)
    have hd12 : ¬ 12 ≤ c.degree := by omega
    simpa [v15BetaPower, v15AlgebraicBetaPower, hd9, hd10, hd11eq,
      hd12] using h.le

/-- Literature-facing small-degree assembly with the quadratic row removed
from the external premises. -/
theorem v15_smallDegreeDiscriminantInput_of_reduced_literature
    (hMin : V15DegreeThreeToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput) :
    V15SmallDegreeDiscriminantInput :=
  v15_smallDegreeDiscriminantInput_of_literature
    (v15_degreeTwoToNineMinimumInput_of_threeToNine hMin)
    hTen hEleven

/-- Small-degree assembly with the quadratic row internal and the cubic row
reduced to the normalized Hunter certificate. -/
theorem v15_smallDegreeDiscriminantInput_of_hunterCertificate
    (hHunter : V15DegreeThreeHunterCertificateInput)
    (hMin : V15DegreeFourToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput) :
    V15SmallDegreeDiscriminantInput :=
  v15_smallDegreeDiscriminantInput_of_reduced_literature
    (v15_degreeThreeToNineMinimumInput_of_hunterCertificate
      hHunter hMin)
    hTen hEleven

/-- All field-discriminant estimates needed by the Section 4 tables. -/
def V15SectionFourDiscriminantInput : Prop :=
  ∀ c : GlobalLatticeClass,
    v15BetaPower 1 c.degree ≤
      ((|c.fieldCode.discriminant| : ℤ) : ℝ)

/-- The finite-degree input and Table 4 from degree twelve onward jointly
supply the piecewise `β_d` lower bound used in the manuscript. -/
theorem v15_sectionFourDiscriminantInput_of_reduced_sources
    (hSmall : V15SmallDegreeDiscriminantInput)
    (hTable : V15OdlyzkoTable4InputFrom 12) :
    V15SectionFourDiscriminantInput := by
  intro c
  by_cases hd : c.degree ≤ 11
  · exact hSmall c hd
  · have hd12 : 12 ≤ c.degree := by omega
    have hd9 : ¬ c.degree ≤ 9 := by omega
    have hd10 : c.degree ≠ 10 := by omega
    have hd11 : c.degree ≠ 11 := by omega
    have h := (hTable c hd12).le
    simpa [v15BetaPower, v15AlgebraicBetaPower, hd12, hd9, hd10,
      hd11] using h

/-- Compatibility endpoint for the earlier unrestricted source premises. -/
theorem v15_sectionFourDiscriminantInput_of_sources
    (hSmall : V15SmallDegreeDiscriminantInput)
    (hTable : V15OdlyzkoTable4Input) :
    V15SectionFourDiscriminantInput :=
  v15_sectionFourDiscriminantInput_of_reduced_sources hSmall
    (v15_odlyzkoTable4InputFrom_of_full hTable 12)

/-- Literature-facing assembly of all Section 4 discriminant inputs. -/
theorem v15_sectionFourDiscriminantInput_of_literature
    (hMin : V15DegreeTwoToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput)
    (hDescription : V15OdlyzkoTable4DescriptionInput) :
    V15SectionFourDiscriminantInput :=
  v15_sectionFourDiscriminantInput_of_reduced_sources
    (v15_smallDegreeDiscriminantInput_of_literature hMin hTen hEleven)
    (v15_odlyzkoTable4InputFrom_of_description hDescription 12)

/-- Section 4 assembly whose remaining small-degree minimum input begins in
degree three. -/
theorem v15_sectionFourDiscriminantInput_of_reduced_literature
    (hMin : V15DegreeThreeToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput)
    (hDescription : V15OdlyzkoTable4DescriptionInput) :
    V15SectionFourDiscriminantInput :=
  v15_sectionFourDiscriminantInput_of_reduced_sources
    (v15_smallDegreeDiscriminantInput_of_reduced_literature
      hMin hTen hEleven)
    (v15_odlyzkoTable4InputFrom_of_description hDescription 12)

/-- Section 4 assembly with the degree-three exact table row replaced by the
normalized Hunter certificate. -/
theorem v15_sectionFourDiscriminantInput_of_hunterCertificate
    (hHunter : V15DegreeThreeHunterCertificateInput)
    (hMin : V15DegreeFourToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput)
    (hDescription : V15OdlyzkoTable4DescriptionInput) :
    V15SectionFourDiscriminantInput :=
  v15_sectionFourDiscriminantInput_of_reduced_sources
    (v15_smallDegreeDiscriminantInput_of_hunterCertificate
      hHunter hMin hTen hEleven)
    (v15_odlyzkoTable4InputFrom_of_description hDescription 12)

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
theorem v15_classic_pair_mem_of_reduced_sources
    (hSmall : V15SmallDegreeDiscriminantInput)
    (hTable : V15OdlyzkoTable4InputFrom 12)
    (c : GlobalLatticeClass)
    (hE : c.IsClassicTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15ClassicAdmissiblePairs := by
  have hDisc := v15_sectionFourDiscriminantInput_of_reduced_sources hSmall hTable
  have hTable15 : V15OdlyzkoTable4InputFrom 15 :=
    hTable.mono (by norm_num)
  apply (v15_classic_analytic_grid_iff_mem c.rank c.degree c.rank_pos
    (v15_integral_rank_le_34 c hE.2) c.degree_pos_v15
    (v15_classic_degree_le_14_of_odlyzko
      (v15_odlyzko_degree_input_of_table4_from_fifteen hTable15) c hE)).mp
  exact v15_classic_analyticH_necessary hDisc c hE

/-- Compatibility endpoint for the earlier unrestricted source premises. -/
theorem v15_classic_pair_mem_of_sources
    (hSmall : V15SmallDegreeDiscriminantInput)
    (hTable : V15OdlyzkoTable4Input)
    (c : GlobalLatticeClass)
    (hE : c.IsClassicTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15ClassicAdmissiblePairs :=
  v15_classic_pair_mem_of_reduced_sources hSmall
    (v15_odlyzkoTable4InputFrom_of_full hTable 12) c hE

/-- Literature-facing classic table-membership endpoint. -/
theorem v15_classic_pair_mem_of_literature
    (hMin : V15DegreeTwoToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput)
    (hDescription : V15OdlyzkoTable4DescriptionInput)
    (c : GlobalLatticeClass)
    (hE : c.IsClassicTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15ClassicAdmissiblePairs :=
  v15_classic_pair_mem_of_reduced_sources
    (v15_smallDegreeDiscriminantInput_of_literature hMin hTen hEleven)
    (v15_odlyzkoTable4InputFrom_of_description hDescription 12) c hE

/-- Literature-facing classic table membership with degree two discharged
internally. -/
theorem v15_classic_pair_mem_of_reduced_literature
    (hMin : V15DegreeThreeToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput)
    (hDescription : V15OdlyzkoTable4DescriptionInput)
    (c : GlobalLatticeClass)
    (hE : c.IsClassicTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15ClassicAdmissiblePairs :=
  v15_classic_pair_mem_of_reduced_sources
    (v15_smallDegreeDiscriminantInput_of_reduced_literature
      hMin hTen hEleven)
    (v15_odlyzkoTable4InputFrom_of_description hDescription 12) c hE

/-- Literature-facing classic table membership with the cubic source boundary
reduced to the normalized Hunter certificate. -/
theorem v15_classic_pair_mem_of_hunterCertificate
    (hHunter : V15DegreeThreeHunterCertificateInput)
    (hMin : V15DegreeFourToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput)
    (hDescription : V15OdlyzkoTable4DescriptionInput)
    (c : GlobalLatticeClass)
    (hE : c.IsClassicTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15ClassicAdmissiblePairs :=
  v15_classic_pair_mem_of_reduced_sources
    (v15_smallDegreeDiscriminantInput_of_hunterCertificate
      hHunter hMin hTen hEleven)
    (v15_odlyzkoTable4InputFrom_of_description hDescription 12) c hE

/-- Every integral class in the proved finite grid belongs to exactly one of
the 63 analytically admissible pairs. -/
theorem v15_integral_pair_mem_of_reduced_sources
    (hSmall : V15SmallDegreeDiscriminantInput)
    (hTable : V15OdlyzkoTable4InputFrom 12)
    (hRankOne : V15RankOneClassicInput)
    (c : GlobalLatticeClass)
    (hE : c.IsIntegralTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15IntegralAdmissiblePairs := by
  have hDisc := v15_sectionFourDiscriminantInput_of_reduced_sources hSmall hTable
  have hTable15 : V15OdlyzkoTable4InputFrom 15 :=
    hTable.mono (by norm_num)
  apply (v15_integral_analytic_grid_iff_mem c.rank c.degree c.rank_pos
    (v15_integral_rank_le_34 c hE) c.degree_pos_v15
    (v15_integral_degree_le_14_of_odlyzko
      (v15_odlyzko_degree_input_of_table4_from_fifteen hTable15)
      hRankOne c hE)).mp
  exact v15_integral_analyticH_necessary hDisc hRankOne c hE

/-- Compatibility endpoint for the earlier unrestricted source premises. -/
theorem v15_integral_pair_mem_of_sources
    (hSmall : V15SmallDegreeDiscriminantInput)
    (hTable : V15OdlyzkoTable4Input)
    (hRankOne : V15RankOneClassicInput)
    (c : GlobalLatticeClass)
    (hE : c.IsIntegralTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15IntegralAdmissiblePairs :=
  v15_integral_pair_mem_of_reduced_sources hSmall
    (v15_odlyzkoTable4InputFrom_of_full hTable 12) hRankOne c hE

/-- Literature-facing integral table-membership endpoint. -/
theorem v15_integral_pair_mem_of_literature
    (hMin : V15DegreeTwoToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput)
    (hDescription : V15OdlyzkoTable4DescriptionInput)
    (hRankOne : V15RankOneClassicInput)
    (c : GlobalLatticeClass)
    (hE : c.IsIntegralTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15IntegralAdmissiblePairs :=
  v15_integral_pair_mem_of_reduced_sources
    (v15_smallDegreeDiscriminantInput_of_literature hMin hTen hEleven)
    (v15_odlyzkoTable4InputFrom_of_description hDescription 12)
    hRankOne c hE

/-- Literature-facing integral table membership with degree two discharged
internally. -/
theorem v15_integral_pair_mem_of_reduced_literature
    (hMin : V15DegreeThreeToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput)
    (hDescription : V15OdlyzkoTable4DescriptionInput)
    (hRankOne : V15RankOneClassicInput)
    (c : GlobalLatticeClass)
    (hE : c.IsIntegralTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15IntegralAdmissiblePairs :=
  v15_integral_pair_mem_of_reduced_sources
    (v15_smallDegreeDiscriminantInput_of_reduced_literature
      hMin hTen hEleven)
    (v15_odlyzkoTable4InputFrom_of_description hDescription 12)
    hRankOne c hE

/-- Literature-facing integral table membership with the cubic source
boundary reduced to the normalized Hunter certificate. -/
theorem v15_integral_pair_mem_of_hunterCertificate
    (hHunter : V15DegreeThreeHunterCertificateInput)
    (hMin : V15DegreeFourToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput)
    (hDescription : V15OdlyzkoTable4DescriptionInput)
    (hRankOne : V15RankOneClassicInput)
    (c : GlobalLatticeClass)
    (hE : c.IsIntegralTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15IntegralAdmissiblePairs :=
  v15_integral_pair_mem_of_reduced_sources
    (v15_smallDegreeDiscriminantInput_of_hunterCertificate
      hHunter hMin hTen hEleven)
    (v15_odlyzkoTable4InputFrom_of_description hDescription 12)
    hRankOne c hE

end

end TraceEuclidean
