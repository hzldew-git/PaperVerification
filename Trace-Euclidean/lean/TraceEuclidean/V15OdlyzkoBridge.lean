import TraceEuclidean.V15FinitenessAssembly

/-!
The numerical consequence of Odlyzko's unconditional Table 4, row `b = 4`.
The published discriminant estimate is kept as an explicit external premise;
the conversion to the degree cutoff is proved here in Lean.
-/

namespace TraceEuclidean

noncomputable section

/-- Odlyzko's Table 4 row `b = 4`, in its published form for totally real
fields: `|D_F| > 36.347 ^ d * exp (-10.667)`. -/
def V15OdlyzkoTable4Input : Prop :=
  ∀ c : GlobalLatticeClass,
    (36347 / 1000 : ℝ) ^ c.degree * Real.exp (-(10667 / 1000 : ℝ)) <
      ((|c.fieldCode.discriminant| : ℤ) : ℝ)

private theorem exp_correction_lt :
    Real.exp (10667 / 15000 : ℝ) < 21 / 10 := by
  have h := Real.exp_bound' (x := (10667 / 15000 : ℝ))
    (by norm_num) (by norm_num) (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem table_base_gap :
    (2 * Real.pi * Real.exp 1) * (21 / 10 : ℝ) < 36347 / 1000 := by
  have hpi : Real.pi < (22 / 7 : ℝ) := by
    linarith [Real.pi_lt_d4]
  have he : Real.exp 1 < (11 / 4 : ℝ) := by
    linarith [Real.exp_one_lt_d9]
  nlinarith [Real.pi_pos, Real.exp_pos (1 : ℝ)]

theorem v15_odlyzko_degree_input_of_table4
    (hTable : V15OdlyzkoTable4Input) :
    V15OdlyzkoDegreeInput := by
  intro c hd
  have h15 : Real.exp (10667 / 1000 : ℝ) < (21 / 10 : ℝ) ^ 15 := by
    have hpow := pow_lt_pow_left₀ exp_correction_lt (Real.exp_nonneg _)
      (by norm_num : (15 : ℕ) ≠ 0)
    rw [← Real.exp_nat_mul] at hpow
    have harg : (↑(15 : ℕ) : ℝ) * (10667 / 15000 : ℝ) = 10667 / 1000 := by
      norm_num
    rw [harg] at hpow
    exact hpow
  have hpowmon : (21 / 10 : ℝ) ^ 15 ≤ (21 / 10 : ℝ) ^ c.degree :=
    pow_le_pow_right₀ (by norm_num) hd
  have hcorr : Real.exp (10667 / 1000 : ℝ) <
      (21 / 10 : ℝ) ^ c.degree := h15.trans_le hpowmon
  have hbase : 0 ≤ 2 * Real.pi * Real.exp 1 := by positivity
  have hcomp :
      ((2 * Real.pi * Real.exp 1) * (21 / 10 : ℝ)) ^ c.degree <
        (36347 / 1000 : ℝ) ^ c.degree :=
    pow_lt_pow_left₀ table_base_gap (by positivity) (by omega)
  have hfirst :
      (2 * Real.pi * Real.exp 1) ^ c.degree *
          Real.exp (10667 / 1000 : ℝ) <
        (36347 / 1000 : ℝ) ^ c.degree := by
    calc
      (2 * Real.pi * Real.exp 1) ^ c.degree *
          Real.exp (10667 / 1000 : ℝ) <
        (2 * Real.pi * Real.exp 1) ^ c.degree *
          (21 / 10 : ℝ) ^ c.degree :=
            mul_lt_mul_of_pos_left hcorr (pow_pos (by positivity) _)
      _ = ((2 * Real.pi * Real.exp 1) * (21 / 10 : ℝ)) ^ c.degree :=
        (mul_pow ..).symm
      _ < (36347 / 1000 : ℝ) ^ c.degree := hcomp
  have hTableC := hTable c
  have hExp : 0 < Real.exp (10667 / 1000 : ℝ) := Real.exp_pos _
  have hNeg : Real.exp (-(10667 / 1000 : ℝ)) =
      (Real.exp (10667 / 1000 : ℝ))⁻¹ := Real.exp_neg _
  rw [hNeg] at hTableC
  have hTableMul : (36347 / 1000 : ℝ) ^ c.degree <
      ((|c.fieldCode.discriminant| : ℤ) : ℝ) *
        Real.exp (10667 / 1000 : ℝ) := by
    calc
      (36347 / 1000 : ℝ) ^ c.degree =
          ((36347 / 1000 : ℝ) ^ c.degree *
            (Real.exp (10667 / 1000 : ℝ))⁻¹) *
              Real.exp (10667 / 1000 : ℝ) := by
                field_simp
      _ < ((|c.fieldCode.discriminant| : ℤ) : ℝ) *
            Real.exp (10667 / 1000 : ℝ) :=
              mul_lt_mul_of_pos_right hTableC hExp
  exact lt_of_mul_lt_mul_right (hfirst.trans hTableMul) hExp.le

theorem v15_classic_finite_of_odlyzko_table4
    (hTable : V15OdlyzkoTable4Input) :
    {c : GlobalLatticeClass |
      c.IsClassicTraceEuclidean (c.degree : ℝ)}.Finite :=
  v15_classic_finite_of_odlyzko (v15_odlyzko_degree_input_of_table4 hTable)

theorem v15_integral_finite_of_odlyzko_table4
    (hTable : V15OdlyzkoTable4Input)
    (hRankOne : V15RankOneClassicInput) :
    {c : GlobalLatticeClass |
      c.IsIntegralTraceEuclidean (c.degree : ℝ)}.Finite :=
  v15_integral_finite_of_odlyzko
    (v15_odlyzko_degree_input_of_table4 hTable) hRankOne

end

end TraceEuclidean
