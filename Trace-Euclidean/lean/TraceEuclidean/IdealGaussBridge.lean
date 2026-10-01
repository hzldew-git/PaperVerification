import TraceEuclidean.GaussBasis
import TraceEuclidean.IdealNormQuotient
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
def idealCrossTraceInt
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (α : F)
    (hint : valueFractionalIdeal I α ≤ 1) (x y : I.coeToSubmodule) : ℤ := by
  have hvalue : IsIntegral ℤ (α * (x : F) * (y : F)) :=
    value_integral_of_ideal_integral I α hint x.2 y.2
  have htrace : IsIntegral ℤ
      (Algebra.trace ℚ F (α * (x : F) * (y : F))) :=
    Algebra.isIntegral_trace hvalue
  exact Classical.choose (IsIntegrallyClosed.isIntegral_iff.mp htrace)
theorem ideal_cross_trace_int_cast
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (α : F)
    (hint : valueFractionalIdeal I α ≤ 1) (x y : I.coeToSubmodule) :
    (idealCrossTraceInt I α hint x y : ℚ) =
      Algebra.trace ℚ F (α * (x : F) * (y : F)) := by
  have hvalue : IsIntegral ℤ (α * (x : F) * (y : F)) :=
    value_integral_of_ideal_integral I α hint x.2 y.2
  have htrace : IsIntegral ℤ
      (Algebra.trace ℚ F (α * (x : F) * (y : F))) :=
    Algebra.isIntegral_trace hvalue
  exact Classical.choose_spec (IsIntegrallyClosed.isIntegral_iff.mp htrace)
def idealTraceNat
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (α : F)
    (hint : valueFractionalIdeal I α ≤ 1) (x : I.coeToSubmodule) : ℕ :=
  (idealCrossTraceInt I α hint x x).toNat
def IdealTracePositive
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
     (α : F) : Prop :=
  ∀ x : I.coeToSubmodule, x ≠ 0 → 0 < Algebra.trace ℚ F (α * (x : F) ^ 2)
theorem ideal_trace_nat_cast
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (α : F)
    (hint : valueFractionalIdeal I α ≤ 1)
    (hpositive : IdealTracePositive I α) (x : I.coeToSubmodule) :
    (idealTraceNat I α hint x : ℚ) =
      Algebra.trace ℚ F (α * (x : F) ^ 2) := by
  have htrace_nonneg : (0 : ℚ) ≤
      Algebra.trace ℚ F (α * (x : F) ^ 2) := by
    unfold IdealTracePositive at hpositive
    by_cases hx : x = 0
    · subst x
      simp
    · exact (hpositive x hx).le
  have hcross_nonneg : 0 ≤ idealCrossTraceInt I α hint x x := by
    have hq := ideal_cross_trace_int_cast I α hint x x
    have hq' : (0 : ℚ) ≤ (idealCrossTraceInt I α hint x x : ℚ) := by
      rw [hq]
      simpa only [pow_two, mul_assoc] using htrace_nonneg
    exact_mod_cast hq'
  have hnat := Int.toNat_of_nonneg hcross_nonneg
  change (((idealCrossTraceInt I α hint x x).toNat : ℕ) : ℚ) = _
  have hcast : (((idealCrossTraceInt I α hint x x).toNat : ℕ) : ℚ) =
      (idealCrossTraceInt I α hint x x : ℚ) := by
    exact_mod_cast hnat
  rw [hcast, ideal_cross_trace_int_cast]
  ring
theorem ideal_trace_nat_neg
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (α : F)
    (hint : valueFractionalIdeal I α ≤ 1)
    (hpositive : IdealTracePositive I α) (x : I.coeToSubmodule) :
    idealTraceNat I α hint (-x) = idealTraceNat I α hint x := by
  apply Nat.cast_injective (R := ℚ)
  rw [ideal_trace_nat_cast I α hint hpositive,
    ideal_trace_nat_cast I α hint hpositive]
  simp only [Submodule.coe_neg]
  ring
theorem ideal_cross_trace_int_neg
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (α : F)
    (hint : valueFractionalIdeal I α ≤ 1) (x y : I.coeToSubmodule) :
    idealCrossTraceInt I α hint x (-y) =
      -idealCrossTraceInt I α hint x y := by
  apply Int.cast_injective (α := ℚ)
  rw [Int.cast_neg, ideal_cross_trace_int_cast,
    ideal_cross_trace_int_cast]
  simp only [Submodule.coe_neg]
  have heq : α * (x : F) * (-(y : F)) =
      -(α * (x : F) * (y : F)) := by ring
  rw [heq, map_neg]
theorem ideal_trace_nat_add
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (α : F)
    (hint : valueFractionalIdeal I α ≤ 1)
    (hpositive : IdealTracePositive I α) (x y : I.coeToSubmodule) :
    (idealTraceNat I α hint (x + y) : ℤ) =
      (idealTraceNat I α hint x : ℤ) +
        (idealTraceNat I α hint y : ℤ) +
          2 * idealCrossTraceInt I α hint x y := by
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [ideal_trace_nat_cast I α hint hpositive,
    ideal_trace_nat_cast I α hint hpositive,
    ideal_trace_nat_cast I α hint hpositive,
    ideal_cross_trace_int_cast]
  simp only [Submodule.coe_add]
  have heq : α * ((x : F) + (y : F)) ^ 2 =
      α * (x : F) ^ 2 + α * (y : F) ^ 2 +
        (α * (x : F) * (y : F) + α * (x : F) * (y : F)) := by ring
  rw [heq, map_add, map_add, map_add]
  ring
theorem ideal_trace_nat_sub
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (α : F)
    (hint : valueFractionalIdeal I α ≤ 1)
    (hpositive : IdealTracePositive I α) (x y : I.coeToSubmodule) :
    (idealTraceNat I α hint (x - y) : ℤ) =
      (idealTraceNat I α hint x : ℤ) +
        (idealTraceNat I α hint y : ℤ) -
          2 * idealCrossTraceInt I α hint x y := by
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [ideal_trace_nat_cast I α hint hpositive,
    ideal_trace_nat_cast I α hint hpositive,
    ideal_trace_nat_cast I α hint hpositive,
    ideal_cross_trace_int_cast]
  simp only [Submodule.coe_sub]
  have heq : α * ((x : F) - (y : F)) ^ 2 =
      α * (x : F) ^ 2 + α * (y : F) ^ 2 -
        (α * (x : F) * (y : F) + α * (x : F) * (y : F)) := by ring
  rw [heq, map_sub, map_add, map_add]
  ring
/-- A positive integral trace form on an arbitrary fractional ideal admits
an integral basis with the signed Gauss inequalities. -/
theorem actual_ideal_gauss_basis
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (hdegree : Module.finrank ℚ F = 2) (α : F)
    (hint : valueFractionalIdeal I α ≤ 1)
    (hpositive : IdealTracePositive I α) :
    ∃ B : Basis (Fin 2) ℤ I.coeToSubmodule,
      idealTraceNat I α hint (B 0) ≤
        idealTraceNat I α hint (B 1) ∧
      0 ≤ idealCrossTraceInt I α hint (B 0) (B 1) ∧
      2 * idealCrossTraceInt I α hint (B 0) (B 1) ≤
        (idealTraceNat I α hint (B 0) : ℤ) :=
  exists_gauss_basis (idealZBasis I hI hdegree)
    (idealTraceNat I α hint) (idealCrossTraceInt I α hint)
    (ideal_trace_nat_neg I α hint hpositive)
    (ideal_trace_nat_add I α hint hpositive)
    (ideal_trace_nat_sub I α hint hpositive)
    (ideal_cross_trace_int_neg I α hint)
end
end TraceEuclidean
