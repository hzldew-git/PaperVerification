import TraceEuclidean.V15BinaryCovering

/-!
The rational deep-hole argument for an arbitrary reduced integral binary
trace Gram matrix. Unlike the finite six-form radius calculation, this
necessity theorem does not assume the radius inequality in advance.
-/

namespace TraceEuclidean

noncomputable section

def V15ReducedGram (a b c : ℕ) : Prop :=
  2 ≤ a ∧ a ≤ c ∧ 2 * b ≤ a

def v15GramCostRat (a b c : ℕ)
    (x : PlanePoint ℚ) (z : IntegralPoint) : ℚ :=
  let u := x.1 - (z.1 : ℚ)
  let v := x.2 - (z.2 : ℚ)
  (a : ℚ) * u ^ 2 + 2 * b * u * v + (c : ℚ) * v ^ 2

def V15BinaryTraceEuclidean (a b c : ℕ) : Prop :=
  ∀ x : PlanePoint ℚ, ∃ z : IntegralPoint,
    v15GramCostRat a b c x z < 2

private theorem integer_consecutive_nonneg (i : ℤ) : 0 ≤ i * (i - 1) := by
  rcases le_total i 0 with hi | hi
  · exact mul_nonneg_of_nonpos_of_nonpos hi (by omega)
  · by_cases hi0 : i = 0
    · simp [hi0]
    · exact mul_nonneg (by omega) (by omega)

private theorem integer_hexagon_gap_nonneg (i j : ℤ) :
    0 ≤ i * (i - 1) + i * j + j * (j - 1) := by
  by_cases hi : 0 ≤ i
  · by_cases hj : 0 ≤ j
    · have h1 := integer_consecutive_nonneg i
      have h2 := integer_consecutive_nonneg j
      have h3 := mul_nonneg hi hj
      omega
    · have h1 := integer_consecutive_nonneg (i + j)
      have h2 : i * j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hi (by omega)
      nlinarith
  · by_cases hj : 0 ≤ j
    · have h1 := integer_consecutive_nonneg (i + j)
      have h2 : i * j ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by omega) hj
      nlinarith
    · have h1 := integer_consecutive_nonneg i
      have h2 := integer_consecutive_nonneg j
      have h3 : 0 ≤ i * j := mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
      omega

/-- Every integer lattice point lies at least as far from the circumcenter
of `0`, `e₁`, and `e₂` as those three points, for a reduced Gram form. -/
theorem v15_reduced_integer_gap_nonneg {a b c : ℕ}
    (h : V15ReducedGram a b c) (i j : ℤ) :
    0 ≤ (a : ℚ) * (i : ℚ) ^ 2 + 2 * b * (i : ℚ) * j +
      (c : ℚ) * (j : ℚ) ^ 2 - (a : ℚ) * i - (c : ℚ) * j := by
  rcases h with ⟨_, hac, hba⟩
  have hbaq : 0 ≤ (a : ℚ) - 2 * b := by
    have hbaq' : 2 * (b : ℚ) ≤ a := by exact_mod_cast hba
    linarith
  have hbc : 2 * b ≤ c := le_trans hba hac
  have hbcq : 0 ≤ (c : ℚ) - 2 * b := by
    have hbcq' : 2 * (b : ℚ) ≤ c := by exact_mod_cast hbc
    linarith
  have hbq : (0 : ℚ) ≤ 2 * b := by positivity
  have hiq : (0 : ℚ) ≤ (i : ℚ) * ((i : ℚ) - 1) := by
    exact_mod_cast integer_consecutive_nonneg i
  have hjq : (0 : ℚ) ≤ (j : ℚ) * ((j : ℚ) - 1) := by
    exact_mod_cast integer_consecutive_nonneg j
  have hgapq : (0 : ℚ) ≤
      (i : ℚ) * ((i : ℚ) - 1) + (i : ℚ) * j +
        (j : ℚ) * ((j : ℚ) - 1) := by
    exact_mod_cast integer_hexagon_gap_nonneg i j
  have h1 := mul_nonneg hbaq hiq
  have h2 := mul_nonneg hbcq hjq
  have h3 := mul_nonneg hbq hgapq
  nlinarith [h1, h2, h3]

private theorem v15_reduced_determinant_pos {a b c : ℕ}
    (h : V15ReducedGram a b c) :
    0 < (a : ℚ) * c - (b : ℚ) ^ 2 := by
  rcases h with ⟨ha, hac, hba⟩
  have hb : b < a := by omega
  have ha0 : (0 : ℚ) < a := by exact_mod_cast (show 0 < a by omega)
  have hb_lt : (b : ℚ) < a := by exact_mod_cast hb
  have hprod : 0 < ((a : ℚ) - b) * ((a : ℚ) + b) := by
    apply mul_pos
    · linarith
    · positivity
  have hacq : (a : ℚ) ≤ c := by exact_mod_cast hac
  have hmult : (a : ℚ) * a ≤ (a : ℚ) * c :=
    mul_le_mul_of_nonneg_left hacq (le_of_lt ha0)
  nlinarith

def v15RationalDeepHole (a b c : ℕ) : PlanePoint ℚ :=
  ((c : ℚ) * ((a : ℚ) - b) /
      (2 * ((a : ℚ) * c - (b : ℚ) ^ 2)),
    (a : ℚ) * ((c : ℚ) - b) /
      (2 * ((a : ℚ) * c - (b : ℚ) ^ 2)))

private theorem v15_deep_hole_linear_equations {a b c : ℕ}
    (h : V15ReducedGram a b c) :
    (a : ℚ) * (v15RationalDeepHole a b c).1 +
        (b : ℚ) * (v15RationalDeepHole a b c).2 = (a : ℚ) / 2 ∧
      (b : ℚ) * (v15RationalDeepHole a b c).1 +
        (c : ℚ) * (v15RationalDeepHole a b c).2 = (c : ℚ) / 2 := by
  have hd := ne_of_gt (v15_reduced_determinant_pos h)
  constructor
  · dsimp [v15RationalDeepHole]
    field_simp [hd]
    ring
  · dsimp [v15RationalDeepHole]
    have hd' : (c : ℚ) * a - (b : ℚ) ^ 2 ≠ 0 := by
      simpa [mul_comm] using hd
    field_simp [hd, hd']
    ring

private theorem v15_deep_hole_cost_zero {a b c : ℕ}
    (h : V15ReducedGram a b c) :
    v15GramCostRat a b c (v15RationalDeepHole a b c) (0, 0) =
      v15GramRadius a b c := by
  have hd := ne_of_gt (v15_reduced_determinant_pos h)
  dsimp [v15GramCostRat, v15RationalDeepHole, v15GramRadius]
  field_simp [hd]
  ring

/-- The rational circumcenter is a genuine deep hole for every reduced
positive binary Gram form, with respect to all of `ℤ²`. -/
theorem v15_deep_hole_lower {a b c : ℕ}
    (h : V15ReducedGram a b c) (z : IntegralPoint) :
    v15GramRadius a b c ≤
      v15GramCostRat a b c (v15RationalDeepHole a b c) z := by
  obtain ⟨h1, h2⟩ := v15_deep_hole_linear_equations h
  have hgap := v15_reduced_integer_gap_nonneg h z.1 z.2
  have hzero := v15_deep_hole_cost_zero h
  have h1z := congrArg (fun t : ℚ ↦ 2 * (z.1 : ℚ) * t) h1
  have h2z := congrArg (fun t : ℚ ↦ 2 * (z.2 : ℚ) * t) h2
  have heq :
      v15GramCostRat a b c (v15RationalDeepHole a b c) z =
        v15GramCostRat a b c (v15RationalDeepHole a b c) (0, 0) +
          ((a : ℚ) * (z.1 : ℚ) ^ 2 +
            2 * b * (z.1 : ℚ) * z.2 + (c : ℚ) * (z.2 : ℚ) ^ 2 -
            (a : ℚ) * z.1 - (c : ℚ) * z.2) := by
    dsimp [v15GramCostRat]
    nlinarith [h1z, h2z]
  rw [heq, hzero]
  linarith

/-- The direction needed for the 22-row enumeration: trace Euclideanity
forces the strict reduced-Gram covering inequality. -/
theorem v15_binary_euclidean_implies_admissible {a b c : ℕ}
    (hred : V15ReducedGram a b c)
    (heucl : V15BinaryTraceEuclidean a b c) :
    V15AdmissibleGram a b c := by
  obtain ⟨z, hz⟩ := heucl (v15RationalDeepHole a b c)
  have hrad : v15GramRadius a b c < 2 :=
    lt_of_le_of_lt (v15_deep_hole_lower hred z) hz
  have hd := v15_reduced_determinant_pos hred
  have hnum :
      (a : ℤ) * c * ((a : ℤ) + c - 2 * b) <
        8 * ((a : ℤ) * c - (b : ℤ) ^ 2) := by
    have hrad' :
        (a : ℚ) * c * ((a : ℚ) + c - 2 * b) <
          8 * ((a : ℚ) * c - (b : ℚ) ^ 2) := by
      unfold v15GramRadius at hrad
      apply (div_lt_iff₀ (by nlinarith :
        (0 : ℚ) < 4 * ((a : ℚ) * c - (b : ℚ) ^ 2))).mp at hrad
      nlinarith
    exact_mod_cast hrad'
  exact ⟨hred.1, hred.2.1, hred.2.2, hnum⟩

private theorem v15_binary_euclidean_of_real_radius {a b c : ℕ} {r : ℝ}
    (h : SquaredCoveringRadiusSpecOver (v15GramCost a b c) r)
    (hr : r < 2) : V15BinaryTraceEuclidean a b c := by
  intro x
  obtain ⟨z, hz⟩ := h.upper ((x.1 : ℝ), (x.2 : ℝ))
  refine ⟨z, ?_⟩
  have hreal : v15GramCost a b c ((x.1 : ℝ), (x.2 : ℝ)) z < 2 :=
    lt_of_le_of_lt hz hr
  have hcast :
      ((v15GramCostRat a b c x z : ℚ) : ℝ) =
        v15GramCost a b c ((x.1 : ℝ), (x.2 : ℝ)) z := by
    dsimp [v15GramCostRat, v15GramCost]
    push_cast
    ring
  rw [← hcast] at hreal
  exact_mod_cast hreal

/-- The complete constructive converse for all six surviving Gram forms. -/
theorem v15_six_binary_forms_trace_euclidean :
    V15BinaryTraceEuclidean 2 0 4 ∧
    V15BinaryTraceEuclidean 4 2 4 ∧
    V15BinaryTraceEuclidean 2 1 3 ∧
    V15BinaryTraceEuclidean 4 2 6 ∧
    V15BinaryTraceEuclidean 2 1 7 ∧
    V15BinaryTraceEuclidean 5 2 5 := by
  rcases v15_six_exact_covering_radii with
    ⟨h2, h3, h5, h5two, h13, h21⟩
  exact ⟨v15_binary_euclidean_of_real_radius h2 (by norm_num),
    v15_binary_euclidean_of_real_radius h3 (by norm_num),
    v15_binary_euclidean_of_real_radius h5 (by norm_num),
    v15_binary_euclidean_of_real_radius h5two (by norm_num),
    v15_binary_euclidean_of_real_radius h13 (by norm_num),
    v15_binary_euclidean_of_real_radius h21 (by norm_num)⟩

/-- The complete necessary Gram-row conclusion, with the paper's determinant,
parity, and first-vector norm identity stated as explicit hypotheses. -/
theorem v15_binary_necessary_six_rows {m a b c n : ℕ}
    (hm : 1 < m) (hsq : IsSquarefreeNat m)
    (hred : V15ReducedGram a b c)
    (heucl : V15BinaryTraceEuclidean a b c)
    (hn : 0 < n)
    (hdet : a * c - b ^ 2 = v15QuadraticDiscriminant m * n)
    (hpar : m % 4 ≠ 1 →
      a % 2 = 0 ∧ b % 2 = 0 ∧ c % 2 = 0)
    (htrace : V15TraceNormCondition m a n) :
    (m, a, b, c, n) ∈ v15SixSurvivingGrams := by
  apply v15_quadratic_candidate_six_rows
  · exact ⟨hm, hsq, v15_binary_euclidean_implies_admissible hred heucl,
      hn, hdet, hpar⟩
  · exact htrace

/-- Every surviving Gram row satisfies the strict rational-coordinate trace
Euclidean condition. This is a statement about Gram forms, not existence of
an ideal lattice realizing each row. -/
theorem v15_six_row_binary_sufficiency {m a b c n : ℕ}
    (hrow : (m, a, b, c, n) ∈ v15SixSurvivingGrams) :
    V15BinaryTraceEuclidean a b c := by
  rcases v15_six_binary_forms_trace_euclidean with
    ⟨h2, h3, h5, h5two, h13, h21⟩
  simp only [v15SixSurvivingGrams, List.mem_cons, List.not_mem_nil,
    or_false, Prod.mk.injEq] at hrow
  rcases hrow with h | h | h | h | h | h <;>
    rcases h with ⟨_, rfl, rfl, rfl, _⟩ <;> assumption

end

end TraceEuclidean
