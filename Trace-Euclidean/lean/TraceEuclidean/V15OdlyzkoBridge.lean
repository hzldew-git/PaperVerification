import TraceEuclidean.V15FinitenessAssembly

/-!
The numerical consequence of Odlyzko's unconditional Table 4, row `b = 4`.
The published discriminant estimate is kept as an explicit external premise;
the conversion to the degree cutoff is proved here in Lean.
-/

namespace TraceEuclidean

noncomputable section

/-- The full shape of Odlyzko's unconditional Table 4 row `b = 4` as
described with its nonnegative prime-ideal correction term `f`.  This is an
external literature input; the specialization to totally real fields is
proved below. -/
def V15OdlyzkoTable4DescriptionInput : Prop :=
  ∃ f : CodedNumberField → ℝ,
    (∀ K, 0 ≤ f K) ∧
    ∀ K,
      (36347 / 1000 : ℝ) ^ NumberField.InfinitePlace.nrRealPlaces K.1 *
          (16593 / 1000 : ℝ) ^
            (2 * NumberField.InfinitePlace.nrComplexPlaces K.1) *
          Real.exp (f K - (10667 / 1000 : ℝ)) <
      ((|K.discriminant| : ℤ) : ℝ)

/-- Before the table's upward rounding of `E`, the description gives
`E = 8b/3 = 32/3` at `b = 4`. -/
def V15OdlyzkoTable4ExactErrorInput : Prop :=
  ∃ f : CodedNumberField → ℝ,
    (∀ K, 0 ≤ f K) ∧
    ∀ K,
      (36347 / 1000 : ℝ) ^ NumberField.InfinitePlace.nrRealPlaces K.1 *
          (16593 / 1000 : ℝ) ^
            (2 * NumberField.InfinitePlace.nrComplexPlaces K.1) *
          Real.exp (f K - (32 / 3 : ℝ)) <
        ((|K.discriminant| : ℤ) : ℝ)

/-- The tabulated value `10.667` is an upward rounding of `8 · 4 / 3`. -/
theorem v15_odlyzkoTable4_error_rounding :
    (32 / 3 : ℝ) ≤ 10667 / 1000 := by
  norm_num

/-- Upward rounding of `E` weakens the lower bound in the valid direction. -/
theorem v15_odlyzkoTable4DescriptionInput_of_exactError
    (hExact : V15OdlyzkoTable4ExactErrorInput) :
    V15OdlyzkoTable4DescriptionInput := by
  rcases hExact with ⟨f, hf, hTable⟩
  refine ⟨f, hf, ?_⟩
  intro K
  have hExp : Real.exp (f K - (10667 / 1000 : ℝ)) ≤
      Real.exp (f K - (32 / 3 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    linarith [v15_odlyzkoTable4_error_rounding]
  exact (mul_le_mul_of_nonneg_left hExp (by positivity)).trans_lt (hTable K)

/-- The totally real consequence of Table 4, restricted to degrees at least
`d₀`.  This field-level interface states only the range used downstream. -/
def V15OdlyzkoTable4FieldInputFrom (d₀ : ℕ) : Prop :=
  ∀ (K : CodedNumberField), NumberField.IsTotallyReal K.1 →
    d₀ ≤ Module.finrank ℚ K.1 →
      (36347 / 1000 : ℝ) ^ Module.finrank ℚ K.1 *
          Real.exp (-(10667 / 1000 : ℝ)) <
        ((|K.discriminant| : ℤ) : ℝ)

/-- The table description, including `f ≥ 0`, implies its usual totally real
specialization.  Signature reduction and removal of the correction term are
kernel checked here. -/
theorem v15_odlyzkoTable4FieldInputFrom_of_description
    (hDescription : V15OdlyzkoTable4DescriptionInput) (d₀ : ℕ) :
    V15OdlyzkoTable4FieldInputFrom d₀ := by
  rcases hDescription with ⟨f, hf, hTable⟩
  intro K hReal _
  letI : NumberField.IsTotallyReal K.1 := hReal
  have hRow := hTable K
  rw [NumberField.IsTotallyReal.nrComplexPlaces_eq_zero,
    mul_zero, pow_zero, mul_one,
    ← NumberField.IsTotallyReal.finrank K.1] at hRow
  have hExp : Real.exp (-(10667 / 1000 : ℝ)) ≤
      Real.exp (f K - (10667 / 1000 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    linarith [hf K]
  exact (mul_le_mul_of_nonneg_left hExp (pow_nonneg (by norm_num) _)).trans_lt hRow

/-- Odlyzko's Table 4 row `b = 4`, in its published form for totally real
fields: `|D_F| > 36.347 ^ d * exp (-10.667)`. -/
def V15OdlyzkoTable4Input : Prop :=
  ∀ c : GlobalLatticeClass,
    (36347 / 1000 : ℝ) ^ c.degree * Real.exp (-(10667 / 1000 : ℝ)) <
      ((|c.fieldCode.discriminant| : ℤ) : ℝ)

/-- Class-level Table 4 input restricted to degrees at least `d₀`. -/
def V15OdlyzkoTable4InputFrom (d₀ : ℕ) : Prop :=
  ∀ c : GlobalLatticeClass, d₀ ≤ c.degree →
    (36347 / 1000 : ℝ) ^ c.degree * Real.exp (-(10667 / 1000 : ℝ)) <
      ((|c.fieldCode.discriminant| : ℤ) : ℝ)

/-- Transport the source's field-level statement to the selected field of a
global lattice class. -/
theorem v15_odlyzkoTable4InputFrom_of_field
    {d₀ : ℕ} (hField : V15OdlyzkoTable4FieldInputFrom d₀) :
    V15OdlyzkoTable4InputFrom d₀ := by
  intro c hd
  have hfin : Module.finrank ℚ c.fieldCode.1 = c.degree := by
    change Module.finrank ℚ c.representative.field.1 = c.degree
    exact c.representative_degree
  have h := hField c.fieldCode c.representative.totallyReal (hfin ▸ hd)
  exact hfin ▸ h

/-- The full class-level input implies every restricted version. -/
theorem v15_odlyzkoTable4InputFrom_of_full
    (hTable : V15OdlyzkoTable4Input) (d₀ : ℕ) :
    V15OdlyzkoTable4InputFrom d₀ := by
  intro c _
  exact hTable c

/-- A lower starting degree gives the corresponding input on any smaller
range of fields. -/
theorem V15OdlyzkoTable4InputFrom.mono
    {d₀ d₁ : ℕ} (hTable : V15OdlyzkoTable4InputFrom d₀) (h : d₀ ≤ d₁) :
    V15OdlyzkoTable4InputFrom d₁ := by
  intro c hd
  exact hTable c (h.trans hd)

/-- The source description supplies the class-level restricted input. -/
theorem v15_odlyzkoTable4InputFrom_of_description
    (hDescription : V15OdlyzkoTable4DescriptionInput) (d₀ : ℕ) :
    V15OdlyzkoTable4InputFrom d₀ :=
  v15_odlyzkoTable4InputFrom_of_field
    (v15_odlyzkoTable4FieldInputFrom_of_description hDescription d₀)

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

theorem v15_odlyzko_degree_input_of_table4_from_fifteen
    (hTable : V15OdlyzkoTable4InputFrom 15) :
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
  have hTableC := hTable c hd
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

/-- Compatibility endpoint for the unrestricted Table 4 premise. -/
theorem v15_odlyzko_degree_input_of_table4
    (hTable : V15OdlyzkoTable4Input) :
    V15OdlyzkoDegreeInput :=
  v15_odlyzko_degree_input_of_table4_from_fifteen
    (v15_odlyzkoTable4InputFrom_of_full hTable 15)

/-- The degree cutoff and classic finiteness need Table 4 only from degree
fifteen onward. -/
theorem v15_classic_finite_of_odlyzko_table4_from_fifteen
    (hTable : V15OdlyzkoTable4InputFrom 15) :
    {c : GlobalLatticeClass |
      c.IsClassicTraceEuclidean (c.degree : ℝ)}.Finite :=
  v15_classic_finite_of_odlyzko
    (v15_odlyzko_degree_input_of_table4_from_fifteen hTable)

/-- The degree cutoff and integral finiteness need Table 4 only from degree
fifteen onward. -/
theorem v15_integral_finite_of_odlyzko_table4_from_fifteen
    (hTable : V15OdlyzkoTable4InputFrom 15)
    (hRankOne : V15RankOneClassicInput) :
    {c : GlobalLatticeClass |
      c.IsIntegralTraceEuclidean (c.degree : ℝ)}.Finite :=
  v15_integral_finite_of_odlyzko
    (v15_odlyzko_degree_input_of_table4_from_fifteen hTable) hRankOne

/-- Literature-facing classic finiteness endpoint starting from the complete
Table 4 row with its nonnegative correction term. -/
theorem v15_classic_finite_of_odlyzko_table4_description
    (hDescription : V15OdlyzkoTable4DescriptionInput) :
    {c : GlobalLatticeClass |
      c.IsClassicTraceEuclidean (c.degree : ℝ)}.Finite :=
  v15_classic_finite_of_odlyzko_table4_from_fifteen
    (v15_odlyzkoTable4InputFrom_of_description hDescription 15)

/-- Literature-facing integral finiteness endpoint starting from the complete
Table 4 row with its nonnegative correction term. -/
theorem v15_integral_finite_of_odlyzko_table4_description
    (hDescription : V15OdlyzkoTable4DescriptionInput)
    (hRankOne : V15RankOneClassicInput) :
    {c : GlobalLatticeClass |
      c.IsIntegralTraceEuclidean (c.degree : ℝ)}.Finite :=
  v15_integral_finite_of_odlyzko_table4_from_fifteen
    (v15_odlyzkoTable4InputFrom_of_description hDescription 15) hRankOne

theorem v15_classic_finite_of_odlyzko_table4
    (hTable : V15OdlyzkoTable4Input) :
    {c : GlobalLatticeClass |
      c.IsClassicTraceEuclidean (c.degree : ℝ)}.Finite :=
  v15_classic_finite_of_odlyzko_table4_from_fifteen
    (v15_odlyzkoTable4InputFrom_of_full hTable 15)

theorem v15_integral_finite_of_odlyzko_table4
    (hTable : V15OdlyzkoTable4Input)
    (hRankOne : V15RankOneClassicInput) :
    {c : GlobalLatticeClass |
      c.IsIntegralTraceEuclidean (c.degree : ℝ)}.Finite :=
  v15_integral_finite_of_odlyzko_table4_from_fifteen
    (v15_odlyzkoTable4InputFrom_of_full hTable 15) hRankOne

end

end TraceEuclidean
