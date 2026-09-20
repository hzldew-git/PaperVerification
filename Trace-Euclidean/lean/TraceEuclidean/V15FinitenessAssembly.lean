import TraceEuclidean.GlobalFiniteness
import TraceEuclidean.GammaVolumeBounds

/-!
V15 variable-threshold finite-grid assembly. The strict root-discriminant
proof is in `V15StrictDiscriminant`, and the published Odlyzko row is connected
to the degree cutoff in `V15OdlyzkoBridge`. This module keeps the intermediate
inputs explicit.
-/

namespace TraceEuclidean

noncomputable section

theorem GlobalLatticeClass.degree_pos_v15 (c : GlobalLatticeClass) :
    0 < c.degree := by
  rw [← c.representative_degree]
  unfold GlobalLatticePresentation.degree
  exact Module.finrank_pos

/-- A Stirling bound with the trace threshold equal to the varying degree. -/
theorem v15_ball_degree_bound (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (c : ℝ) (hc : 0 ≤ c) :
    euclideanUnitBallVolume (n * d) ^ (2 : ℕ) *
      (c * (d : ℝ)) ^ (n * d) ≤
        ((2 * c * Real.pi * Real.exp 1) / (n : ℝ)) ^ (n * d) := by
  have hU := euclideanUnitBallVolume_sq_le (n * d) (Nat.mul_pos hn hd)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  calc
    euclideanUnitBallVolume (n * d) ^ (2 : ℕ) *
        (c * (d : ℝ)) ^ (n * d) ≤
        ((2 * Real.pi * Real.exp 1) / ((n : ℝ) * d)) ^ (n * d) *
          (c * (d : ℝ)) ^ (n * d) := by
            exact mul_le_mul_of_nonneg_right
              (by simpa only [Nat.cast_mul] using hU) (pow_nonneg (by positivity) _)
    _ = ((2 * c * Real.pi * Real.exp 1) / (n : ℝ)) ^ (n * d) := by
      rw [← mul_pow]
      congr 1
      field_simp

private theorem four_pi_e_lt_35 : 4 * Real.pi * Real.exp 1 < 35 := by
  have hpi : Real.pi < (22 / 7 : ℝ) := by linarith [Real.pi_lt_d4]
  have he : Real.exp 1 < (11 / 4 : ℝ) := by
    linarith [Real.exp_one_lt_d9]
  calc
    4 * Real.pi * Real.exp 1 < 4 * (22 / 7 : ℝ) * Real.exp 1 := by
      nlinarith [mul_pos (sub_pos.mpr hpi) (Real.exp_pos 1)]
    _ < 4 * (22 / 7 : ℝ) * (11 / 4 : ℝ) := by
      gcongr
    _ < 35 := by norm_num

/-- The uniform rank part of Corollary 4.4, proved from the existing
projective covolume bound and the formal Stirling estimate. -/
theorem v15_integral_rank_le_34 (c : GlobalLatticeClass)
    (hE : c.IsIntegralTraceEuclidean (c.degree : ℝ)) :
    c.rank ≤ 34 := by
  let n := c.rank
  let d := c.degree
  have hn : 0 < n := c.rank_pos
  have hd : 0 < d := c.degree_pos_v15
  have hbound := GlobalFiniteness.integral_discriminant_pow_le_trace
    (d : ℝ) n d c (by exact_mod_cast hd)
    ⟨hE, rfl, rfl⟩
  have hvolume :
      euclideanUnitBallVolume (n * d) ^ (2 : ℕ) *
          (2 * (d : ℝ)) ^ (n * d) ≤
        ((4 * Real.pi * Real.exp 1) / (n : ℝ)) ^ (n * d) := by
    convert v15_ball_degree_bound n d hn hd 2 (by norm_num) using 1; ring
  have hDpos : 0 < ((|c.fieldCode.discriminant| : ℤ) : ℝ) :=
    (totallyRealMinkowskiDiscriminantLowerBound_pos hd).trans_le
      c.minkowski_discriminant_lower_bound
  have hDge : (1 : ℝ) ≤ ((|c.fieldCode.discriminant| : ℤ) : ℝ) := by
    have hInt : (0 : ℤ) < |c.fieldCode.discriminant| := by
      exact_mod_cast hDpos
    exact_mod_cast (show (1 : ℤ) ≤ |c.fieldCode.discriminant| by omega)
  have hpowge : (1 : ℝ) ≤
      ((|c.fieldCode.discriminant| : ℤ) : ℝ) ^ n := one_le_pow₀ hDge
  by_contra hnot
  have hn35 : 35 ≤ n := by omega
  have hnR : (35 : ℝ) ≤ n := by exact_mod_cast hn35
  have hbase : (4 * Real.pi * Real.exp 1) / (n : ℝ) < 1 := by
    apply (div_lt_one (by exact_mod_cast hn)).2
    linarith [four_pi_e_lt_35]
  have hpow : ((4 * Real.pi * Real.exp 1) / (n : ℝ)) ^ (n * d) < 1 :=
    pow_lt_one₀ (by positivity) hbase (Nat.ne_of_gt (Nat.mul_pos hn hd))
  exact (not_lt_of_ge hpowge) ((hbound.trans hvolume).trans_lt hpow)

/-- The source's unconditional Odlyzko row, stated as a field-only numerical
input on every coded class field. The current project has no Lean proof of it. -/
def V15OdlyzkoDegreeInput : Prop :=
  ∀ c : GlobalLatticeClass, 15 ≤ c.degree →
    (2 * Real.pi * Real.exp 1) ^ c.degree <
      ((|c.fieldCode.discriminant| : ℤ) : ℝ)

private theorem degree_le_fourteen_of_discriminant_power
    (hOdlyzko : V15OdlyzkoDegreeInput) (c : GlobalLatticeClass)
    (hbound : ((|c.fieldCode.discriminant| : ℤ) : ℝ) ^ c.rank ≤
      (2 * Real.pi * Real.exp 1) ^ (c.rank * c.degree)) :
    c.degree ≤ 14 := by
  by_contra hnot
  have hd15 : 15 ≤ c.degree := by omega
  have hOd := hOdlyzko c hd15
  have hOdPow :
      (2 * Real.pi * Real.exp 1) ^ (c.rank * c.degree) <
        ((|c.fieldCode.discriminant| : ℤ) : ℝ) ^ c.rank := by
    simpa only [← pow_mul, Nat.mul_comm] using
      (pow_lt_pow_left₀ hOd (by positivity) c.rank_pos.ne')
  exact (not_lt_of_ge hbound) hOdPow

theorem v15_classic_degree_le_14_of_odlyzko
    (hOdlyzko : V15OdlyzkoDegreeInput)
    (c : GlobalLatticeClass)
    (hE : c.IsClassicTraceEuclidean (c.degree : ℝ)) :
    c.degree ≤ 14 := by
  have hn := c.rank_pos
  have hd := c.degree_pos_v15
  have hdisc := GlobalFiniteness.classic_discriminant_pow_le_trace
    (c.degree : ℝ) c.rank c.degree c (by exact_mod_cast hd)
    ⟨hE, rfl, rfl⟩
  have hvol := v15_ball_degree_bound c.rank c.degree hn hd 1 (by norm_num)
  have hbase : (2 * Real.pi * Real.exp 1) / (c.rank : ℝ) ≤
      2 * Real.pi * Real.exp 1 := by
    apply (div_le_iff₀ (by exact_mod_cast hn)).2
    have hnR : (1 : ℝ) ≤ c.rank := by exact_mod_cast hn
    nlinarith [mul_nonneg (sub_nonneg.mpr hnR) (by positivity :
      0 ≤ 2 * Real.pi * Real.exp 1)]
  apply degree_le_fourteen_of_discriminant_power hOdlyzko c
  calc
    ((|c.fieldCode.discriminant| : ℤ) : ℝ) ^ c.rank ≤
        euclideanUnitBallVolume (c.rank * c.degree) ^ (2 : ℕ) *
          (c.degree : ℝ) ^ (c.rank * c.degree) := hdisc
    _ ≤ ((2 * Real.pi * Real.exp 1) / (c.rank : ℝ)) ^
          (c.rank * c.degree) := by simpa using hvol
    _ ≤ (2 * Real.pi * Real.exp 1) ^ (c.rank * c.degree) := by
      exact pow_le_pow_left₀ (by positivity) hbase _

/-- The rank-one norm-to-scale property, proved for all presentations in
`V15RankOneIntegral`; it is kept explicit at this intermediate endpoint. -/
def V15RankOneClassicInput : Prop :=
  ∀ c : GlobalLatticeClass, c.rank = 1 → c.IsClassicIntegral

theorem v15_integral_degree_le_14_of_odlyzko
    (hOdlyzko : V15OdlyzkoDegreeInput)
    (hRankOne : V15RankOneClassicInput)
    (c : GlobalLatticeClass)
    (hE : c.IsIntegralTraceEuclidean (c.degree : ℝ)) :
    c.degree ≤ 14 := by
  by_cases hrank : c.rank = 1
  · exact v15_classic_degree_le_14_of_odlyzko hOdlyzko c
      ⟨hRankOne c hrank, hE⟩
  have hn2 : 2 ≤ c.rank := by have := c.rank_pos; omega
  have hn := c.rank_pos
  have hd := c.degree_pos_v15
  have hdisc := GlobalFiniteness.integral_discriminant_pow_le_trace
    (c.degree : ℝ) c.rank c.degree c (by exact_mod_cast hd)
    ⟨hE, rfl, rfl⟩
  have hvol := v15_ball_degree_bound c.rank c.degree hn hd 2 (by norm_num)
  have hbase : (4 * Real.pi * Real.exp 1) / (c.rank : ℝ) ≤
      2 * Real.pi * Real.exp 1 := by
    apply (div_le_iff₀ (by exact_mod_cast hn)).2
    have hnR : (2 : ℝ) ≤ c.rank := by exact_mod_cast hn2
    nlinarith [mul_nonneg (sub_nonneg.mpr hnR) (by positivity :
      0 ≤ 2 * Real.pi * Real.exp 1)]
  apply degree_le_fourteen_of_discriminant_power hOdlyzko c
  calc
    ((|c.fieldCode.discriminant| : ℤ) : ℝ) ^ c.rank ≤
        euclideanUnitBallVolume (c.rank * c.degree) ^ (2 : ℕ) *
          (2 * (c.degree : ℝ)) ^ (c.rank * c.degree) := hdisc
    _ ≤ ((4 * Real.pi * Real.exp 1) / (c.rank : ℝ)) ^
          (c.rank * c.degree) := by convert hvol using 1; ring
    _ ≤ (2 * Real.pi * Real.exp 1) ^ (c.rank * c.degree) := by
      exact pow_le_pow_left₀ (by positivity) hbase _

/-- The fixed-pair v9 result assembles to the v15 variable-degree classic
conclusion as soon as the paper's uniform grid bounds are supplied. -/
theorem v15_classic_finite_of_grid
    (hrank : ∀ c : GlobalLatticeClass,
      c.IsClassicTraceEuclidean (c.degree : ℝ) → c.rank ≤ 34)
    (hdegree : ∀ c : GlobalLatticeClass,
      c.IsClassicTraceEuclidean (c.degree : ℝ) → c.degree ≤ 14) :
    {c : GlobalLatticeClass |
      c.IsClassicTraceEuclidean (c.degree : ℝ)}.Finite := by
  apply finite_of_finite_keys_and_fibers
    (fun c : GlobalLatticeClass ↦ c.IsClassicTraceEuclidean (c.degree : ℝ))
    (fun c ↦ (c.rank, c.degree))
    ({p : ℕ × ℕ | p.1 ≤ 34 ∧ p.2 ≤ 14})
  · exact (Set.finite_Iic 34).prod (Set.finite_Iic 14)
  · intro c hc
    exact ⟨hrank c hc, hdegree c hc⟩
  · intro p
    by_cases hd : 0 < p.2
    · apply (GlobalFiniteness.classic_fixed_pair (p.2 : ℝ)
        (by exact_mod_cast hd) p.1 p.2 (le_refl _)).subset
      intro c hc
      have hn : c.rank = p.1 := congrArg Prod.fst hc.2
      have hdeg : c.degree = p.2 := congrArg Prod.snd hc.2
      exact ⟨by simpa [hdeg] using hc.1, hn, hdeg⟩
    · apply Set.finite_empty.subset
      intro c hc
      have hdeg : c.degree = p.2 := congrArg Prod.snd hc.2
      have hpos := c.degree_pos_v15
      omega

/-- The same assembly for integral lattices. -/
theorem v15_integral_finite_of_grid
    (hrank : ∀ c : GlobalLatticeClass,
      c.IsIntegralTraceEuclidean (c.degree : ℝ) → c.rank ≤ 34)
    (hdegree : ∀ c : GlobalLatticeClass,
      c.IsIntegralTraceEuclidean (c.degree : ℝ) → c.degree ≤ 14) :
    {c : GlobalLatticeClass |
      c.IsIntegralTraceEuclidean (c.degree : ℝ)}.Finite := by
  apply finite_of_finite_keys_and_fibers
    (fun c : GlobalLatticeClass ↦ c.IsIntegralTraceEuclidean (c.degree : ℝ))
    (fun c ↦ (c.rank, c.degree))
    ({p : ℕ × ℕ | p.1 ≤ 34 ∧ p.2 ≤ 14})
  · exact (Set.finite_Iic 34).prod (Set.finite_Iic 14)
  · intro c hc
    exact ⟨hrank c hc, hdegree c hc⟩
  · intro p
    by_cases hd : 0 < p.2
    · apply (GlobalFiniteness.integral_fixed_pair (p.2 : ℝ)
        (by exact_mod_cast hd) p.1 p.2 (le_refl _)).subset
      intro c hc
      have hn : c.rank = p.1 := congrArg Prod.fst hc.2
      have hdeg : c.degree = p.2 := congrArg Prod.snd hc.2
      exact ⟨by simpa [hdeg] using hc.1, hn, hdeg⟩
    · apply Set.finite_empty.subset
      intro c hc
      have hdeg : c.degree = p.2 := congrArg Prod.snd hc.2
      have hpos := c.degree_pos_v15
      omega

/-- The sole remaining global grid input is the degree bound, obtained in
the paper from the unconditional Odlyzko discriminant table. -/
theorem v15_classic_finite_of_degree_bound
    (hdegree : ∀ c : GlobalLatticeClass,
      c.IsClassicTraceEuclidean (c.degree : ℝ) → c.degree ≤ 14) :
    {c : GlobalLatticeClass |
      c.IsClassicTraceEuclidean (c.degree : ℝ)}.Finite :=
  v15_classic_finite_of_grid
    (fun c hc ↦ v15_integral_rank_le_34 c hc.2) hdegree

theorem v15_integral_finite_of_degree_bound
    (hdegree : ∀ c : GlobalLatticeClass,
      c.IsIntegralTraceEuclidean (c.degree : ℝ) → c.degree ≤ 14) :
    {c : GlobalLatticeClass |
      c.IsIntegralTraceEuclidean (c.degree : ℝ)}.Finite :=
  v15_integral_finite_of_grid v15_integral_rank_le_34 hdegree

theorem v15_classic_finite_of_odlyzko
    (hOdlyzko : V15OdlyzkoDegreeInput) :
    {c : GlobalLatticeClass |
      c.IsClassicTraceEuclidean (c.degree : ℝ)}.Finite :=
  v15_classic_finite_of_degree_bound
    (v15_classic_degree_le_14_of_odlyzko hOdlyzko)

theorem v15_integral_finite_of_odlyzko
    (hOdlyzko : V15OdlyzkoDegreeInput)
    (hRankOne : V15RankOneClassicInput) :
    {c : GlobalLatticeClass |
      c.IsIntegralTraceEuclidean (c.degree : ℝ)}.Finite :=
  v15_integral_finite_of_degree_bound
    (v15_integral_degree_le_14_of_odlyzko hOdlyzko hRankOne)

end

end TraceEuclidean
