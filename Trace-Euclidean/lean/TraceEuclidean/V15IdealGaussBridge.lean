import TraceEuclidean.V15GaussBasis
import TraceEuclidean.V15IdealNormQuotient
/-!
The integer-valued quadratic trace form of a positive rank-one fractional
ideal, prepared for the direct two-dimensional Gauss reduction theorem.
-/
namespace TraceEuclidean
open Module
open scoped NumberField nonZeroDivisors
noncomputable section
variable {F : Type*} [Field F] [NumberField F]
/-- The integral cross-trace of two ideal vectors. -/
def v15IdealCrossTraceInt
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (α : F)
    (hint : v15ValueFractionalIdeal I α ≤ 1) (x y : I.coeToSubmodule) : ℤ := by
  have hvalue : IsIntegral ℤ (α * (x : F) * (y : F)) :=
    v15_value_integral_of_ideal_integral I α hint x.2 y.2
  have htrace : IsIntegral ℤ
      (Algebra.trace ℚ F (α * (x : F) * (y : F))) :=
    Algebra.isIntegral_trace hvalue
  exact Classical.choose (IsIntegrallyClosed.isIntegral_iff.mp htrace)
theorem v15_ideal_cross_trace_int_cast
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (α : F)
    (hint : v15ValueFractionalIdeal I α ≤ 1) (x y : I.coeToSubmodule) :
    (v15IdealCrossTraceInt I α hint x y : ℚ) =
      Algebra.trace ℚ F (α * (x : F) * (y : F)) := by
  have hvalue : IsIntegral ℤ (α * (x : F) * (y : F)) :=
    v15_value_integral_of_ideal_integral I α hint x.2 y.2
  have htrace : IsIntegral ℤ
      (Algebra.trace ℚ F (α * (x : F) * (y : F))) :=
    Algebra.isIntegral_trace hvalue
  exact Classical.choose_spec (IsIntegrallyClosed.isIntegral_iff.mp htrace)
def v15IdealTraceNat
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (α : F)
    (hint : v15ValueFractionalIdeal I α ≤ 1) (x : I.coeToSubmodule) : ℕ :=
  (v15IdealCrossTraceInt I α hint x x).toNat
def V15IdealTracePositive
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
     (α : F) : Prop :=
  ∀ x : I.coeToSubmodule, x ≠ 0 → 0 < Algebra.trace ℚ F (α * (x : F) ^ 2)
theorem v15_ideal_trace_nat_cast
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (α : F)
    (hint : v15ValueFractionalIdeal I α ≤ 1)
    (hpositive : V15IdealTracePositive I α) (x : I.coeToSubmodule) :
    (v15IdealTraceNat I α hint x : ℚ) =
      Algebra.trace ℚ F (α * (x : F) ^ 2) := by
  have htrace_nonneg : (0 : ℚ) ≤
      Algebra.trace ℚ F (α * (x : F) ^ 2) := by
    unfold V15IdealTracePositive at hpositive
    by_cases hx : x = 0
    · subst x
      simp
    · exact (hpositive x hx).le
  have hcross_nonneg : 0 ≤ v15IdealCrossTraceInt I α hint x x := by
    have hq := v15_ideal_cross_trace_int_cast I α hint x x
    have hq' : (0 : ℚ) ≤ (v15IdealCrossTraceInt I α hint x x : ℚ) := by
      rw [hq]
      simpa only [pow_two, mul_assoc] using htrace_nonneg
    exact_mod_cast hq'
  have hnat := Int.toNat_of_nonneg hcross_nonneg
  change (((v15IdealCrossTraceInt I α hint x x).toNat : ℕ) : ℚ) = _
  have hcast : (((v15IdealCrossTraceInt I α hint x x).toNat : ℕ) : ℚ) =
      (v15IdealCrossTraceInt I α hint x x : ℚ) := by
    exact_mod_cast hnat
  rw [hcast, v15_ideal_cross_trace_int_cast]
  ring
theorem v15_ideal_trace_nat_neg
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (α : F)
    (hint : v15ValueFractionalIdeal I α ≤ 1)
    (hpositive : V15IdealTracePositive I α) (x : I.coeToSubmodule) :
    v15IdealTraceNat I α hint (-x) = v15IdealTraceNat I α hint x := by
  apply Nat.cast_injective (R := ℚ)
  rw [v15_ideal_trace_nat_cast I α hint hpositive,
    v15_ideal_trace_nat_cast I α hint hpositive]
  simp only [Submodule.coe_neg]
  ring
theorem v15_ideal_cross_trace_int_neg
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (α : F)
    (hint : v15ValueFractionalIdeal I α ≤ 1) (x y : I.coeToSubmodule) :
    v15IdealCrossTraceInt I α hint x (-y) =
      -v15IdealCrossTraceInt I α hint x y := by
  apply Int.cast_injective (α := ℚ)
  rw [Int.cast_neg, v15_ideal_cross_trace_int_cast,
    v15_ideal_cross_trace_int_cast]
  simp only [Submodule.coe_neg]
  have heq : α * (x : F) * (-(y : F)) =
      -(α * (x : F) * (y : F)) := by ring
  rw [heq, map_neg]
theorem v15_ideal_trace_nat_add
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (α : F)
    (hint : v15ValueFractionalIdeal I α ≤ 1)
    (hpositive : V15IdealTracePositive I α) (x y : I.coeToSubmodule) :
    (v15IdealTraceNat I α hint (x + y) : ℤ) =
      (v15IdealTraceNat I α hint x : ℤ) +
        (v15IdealTraceNat I α hint y : ℤ) +
          2 * v15IdealCrossTraceInt I α hint x y := by
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [v15_ideal_trace_nat_cast I α hint hpositive,
    v15_ideal_trace_nat_cast I α hint hpositive,
    v15_ideal_trace_nat_cast I α hint hpositive,
    v15_ideal_cross_trace_int_cast]
  simp only [Submodule.coe_add]
  have heq : α * ((x : F) + (y : F)) ^ 2 =
      α * (x : F) ^ 2 + α * (y : F) ^ 2 +
        (α * (x : F) * (y : F) + α * (x : F) * (y : F)) := by ring
  rw [heq, map_add, map_add, map_add]
  ring
theorem v15_ideal_trace_nat_sub
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (α : F)
    (hint : v15ValueFractionalIdeal I α ≤ 1)
    (hpositive : V15IdealTracePositive I α) (x y : I.coeToSubmodule) :
    (v15IdealTraceNat I α hint (x - y) : ℤ) =
      (v15IdealTraceNat I α hint x : ℤ) +
        (v15IdealTraceNat I α hint y : ℤ) -
          2 * v15IdealCrossTraceInt I α hint x y := by
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [v15_ideal_trace_nat_cast I α hint hpositive,
    v15_ideal_trace_nat_cast I α hint hpositive,
    v15_ideal_trace_nat_cast I α hint hpositive,
    v15_ideal_cross_trace_int_cast]
  simp only [Submodule.coe_sub]
  have heq : α * ((x : F) - (y : F)) ^ 2 =
      α * (x : F) ^ 2 + α * (y : F) ^ 2 -
        (α * (x : F) * (y : F) + α * (x : F) * (y : F)) := by ring
  rw [heq, map_sub, map_add, map_add]
  ring
/-- A positive integral trace form on an arbitrary fractional ideal admits
an integral basis with the signed Gauss inequalities. -/
theorem v15_actual_ideal_gauss_basis
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (hdegree : Module.finrank ℚ F = 2) (α : F)
    (hint : v15ValueFractionalIdeal I α ≤ 1)
    (hpositive : V15IdealTracePositive I α) :
    ∃ B : Basis (Fin 2) ℤ I.coeToSubmodule,
      v15IdealTraceNat I α hint (B 0) ≤
        v15IdealTraceNat I α hint (B 1) ∧
      0 ≤ v15IdealCrossTraceInt I α hint (B 0) (B 1) ∧
      2 * v15IdealCrossTraceInt I α hint (B 0) (B 1) ≤
        (v15IdealTraceNat I α hint (B 0) : ℤ) :=
  v15_exists_gauss_basis (v15IdealZBasis I hI hdegree)
    (v15IdealTraceNat I α hint) (v15IdealCrossTraceInt I α hint)
    (v15_ideal_trace_nat_neg I α hint hpositive)
    (v15_ideal_trace_nat_add I α hint hpositive)
    (v15_ideal_trace_nat_sub I α hint hpositive)
    (v15_ideal_cross_trace_int_neg I α hint)
end
end TraceEuclidean
