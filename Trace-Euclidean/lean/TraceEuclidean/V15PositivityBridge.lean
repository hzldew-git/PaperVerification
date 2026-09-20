import TraceEuclidean.V15CoefficientClassification

/-!
For a real quadratic coefficient, positivity of the rational part and of the
field norm implies positivity of the trace quadratic form on every nonzero
field vector. This makes the rank-one positivity hypothesis explicit.
-/

namespace TraceEuclidean

open scoped NumberField nonZeroDivisors

noncomputable section

def V15RealQuadraticCoefficientPositive {m : ℕ}
    [Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r)]
    (α : RealQuadraticAlgebra m) : Prop :=
  0 < α.re ∧ 0 < Algebra.norm ℚ α

/-- Positivity under the two real embeddings `√m ↦ ±√m`, expressed in
coordinates of the concrete quadratic field. -/
def V15RealQuadraticTotallyPositive {m : ℕ}
    (α : RealQuadraticAlgebra m) : Prop :=
  0 < (α.re : ℝ) + (α.im : ℝ) * Real.sqrt m ∧
  0 < (α.re : ℝ) - (α.im : ℝ) * Real.sqrt m

theorem v15_total_positive_iff_re_norm_positive
    {m : ℕ} (hm : 1 < m)
    [Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r)]
    (α : RealQuadraticAlgebra m) :
    V15RealQuadraticTotallyPositive α ↔
      V15RealQuadraticCoefficientPositive α := by
  let p : ℝ := (α.re : ℝ) + (α.im : ℝ) * Real.sqrt m
  let q : ℝ := (α.re : ℝ) - (α.im : ℝ) * Real.sqrt m
  have hmR : (0 : ℝ) ≤ m := by positivity
  have hsqrt : (Real.sqrt (m : ℝ)) ^ 2 = m := Real.sq_sqrt hmR
  have hprod : ((Algebra.norm ℚ α : ℚ) : ℝ) = p * q := by
    rw [realQuadratic_norm]
    have hcast : (((α.re ^ 2 - (m : ℚ) * α.im ^ 2 : ℚ)) : ℝ) =
        (α.re : ℝ) ^ 2 - (m : ℝ) * (α.im : ℝ) ^ 2 := by push_cast; ring
    rw [hcast]
    dsimp [p, q]
    calc
      (α.re : ℝ) ^ 2 - (m : ℝ) * (α.im : ℝ) ^ 2 =
          (α.re : ℝ) ^ 2 - (Real.sqrt m) ^ 2 * (α.im : ℝ) ^ 2 := by
            rw [hsqrt]
      _ = ((α.re : ℝ) + (α.im : ℝ) * Real.sqrt m) *
            ((α.re : ℝ) - (α.im : ℝ) * Real.sqrt m) := by ring
  constructor
  · intro h
    obtain ⟨hp, hq⟩ := h
    have hreR : (0 : ℝ) < (α.re : ℝ) := by
      linarith
    have hnormR : (0 : ℝ) < ((Algebra.norm ℚ α : ℚ) : ℝ) := by
      rw [hprod]
      exact mul_pos hp hq
    exact ⟨(by exact_mod_cast hreR), (by exact_mod_cast hnormR)⟩
  · intro h
    obtain ⟨hreQ, hnormQ⟩ := h
    have hreR : (0 : ℝ) < (α.re : ℝ) := by exact_mod_cast hreQ
    have hnormR : (0 : ℝ) < ((Algebra.norm ℚ α : ℚ) : ℝ) := by
      exact_mod_cast hnormQ
    have hpq : 0 < p * q := by rw [← hprod]; exact hnormR
    rcases (mul_pos_iff.mp hpq) with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · exact ⟨hp, hq⟩
    · exfalso
      dsimp [p, q] at hp hq
      linarith

theorem v15_trace_positive_of_coefficient_positive
    {m : ℕ} (hm : 1 < m)
    [Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r)]
    (α x : RealQuadraticAlgebra m)
    (hα : V15RealQuadraticCoefficientPositive α)
    (hx : x ≠ 0) :
    0 < Algebra.trace ℚ (RealQuadraticAlgebra m) (α * x ^ 2) := by
  obtain ⟨hαre, hαnorm⟩ := hα
  have hmQ : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
  have hform : Algebra.trace ℚ (RealQuadraticAlgebra m) (α * x ^ 2) =
      2 * (α.re * x.re ^ 2 + 2 * (m : ℚ) * α.im * x.re * x.im +
        (m : ℚ) * α.re * x.im ^ 2) := by
    rw [realQuadratic_trace]
    simp [pow_two]
    ring
  have hcomplete : α.re *
      Algebra.trace ℚ (RealQuadraticAlgebra m) (α * x ^ 2) =
      2 * (α.re * x.re + (m : ℚ) * α.im * x.im) ^ 2 +
        2 * (m : ℚ) * (Algebra.norm ℚ α) * x.im ^ 2 := by
    rw [hform, realQuadratic_norm]
    ring
  have hmul : 0 < α.re *
      Algebra.trace ℚ (RealQuadraticAlgebra m) (α * x ^ 2) := by
    rw [hcomplete]
    by_cases hv : x.im = 0
    · have hu : x.re ≠ 0 := by
        intro hu
        apply hx
        apply QuadraticAlgebra.ext
        · simpa using hu
        · simpa using hv
      have hprod : α.re * x.re ≠ 0 :=
        mul_ne_zero (ne_of_gt hαre) hu
      rw [hv]
      norm_num
      nlinarith [sq_pos_of_ne_zero hprod]
    · have hvSq : 0 < x.im ^ 2 := sq_pos_of_ne_zero hv
      have hterm : 0 < (2 : ℚ) * m * (Algebra.norm ℚ α) * x.im ^ 2 := by
        positivity
      nlinarith [sq_nonneg (α.re * x.re + (m : ℚ) * α.im * x.im)]
  by_contra hnot
  have hnonpos : Algebra.trace ℚ (RealQuadraticAlgebra m) (α * x ^ 2) ≤ 0 :=
    le_of_not_gt hnot
  exact (not_le_of_gt hmul) (mul_nonpos_of_nonneg_of_nonpos hαre.le hnonpos)

theorem v15_ideal_trace_positive_of_coefficient_positive
    {m : ℕ} (hm : 1 < m)
    [Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r)]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra m)))
      (RealQuadraticAlgebra m))
    (α : RealQuadraticAlgebra m)
    (hα : V15RealQuadraticCoefficientPositive α) :
    V15IdealTracePositive I α := by
  intro x hx
  apply v15_trace_positive_of_coefficient_positive hm α x hα
  intro hz
  apply hx
  exact Subtype.ext hz

/-- Theorem 1.7 with a single explicit coefficient-positivity hypothesis. -/
theorem v15_rank_one_real_quadratic_classification_positive
    {m : ℕ} (hm : 1 < m) (hsq : IsSquarefreeNat m) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare hm hsq⟩
    ∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra m)))
        (RealQuadraticAlgebra m)) (hI : I ≠ 0)
      (α : RealQuadraticAlgebra m),
      V15RealQuadraticCoefficientPositive α →
      v15ValueFractionalIdeal I α ≤ 1 →
      (V15IdealTraceEuclidean I α ↔ V15SixFreeIsometryClass I α) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  intro I hI α hα hint
  exact v15_rank_one_real_quadratic_classification hm hsq I hI α
    hα.2 hint (v15_ideal_trace_positive_of_coefficient_positive hm I α hα)

/-- Theorem 1.7 stated with positivity under both real embeddings and the
manuscript's integrality condition `α I² ⊆ 𝓞_F`. -/
theorem v15_rank_one_real_quadratic_classification_totally_positive
    {m : ℕ} (hm : 1 < m) (hsq : IsSquarefreeNat m) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare hm hsq⟩
    ∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra m)))
        (RealQuadraticAlgebra m)) (hI : I ≠ 0)
      (α : RealQuadraticAlgebra m),
      V15RealQuadraticTotallyPositive α →
      v15ValueFractionalIdeal I α ≤ 1 →
      (V15IdealTraceEuclidean I α ↔ V15SixFreeIsometryClass I α) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  intro I hI α hα hint
  exact v15_rank_one_real_quadratic_classification_positive hm hsq I hI α
    ((v15_total_positive_iff_re_norm_positive hm α).mp hα) hint

end

end TraceEuclidean
