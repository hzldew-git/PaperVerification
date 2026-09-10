import TraceEuclidean.NumberFieldLattice
import TraceEuclidean.QuadraticClassification

/-!
The explicit bridge between an actual quadratic number field and the two
coordinate lattices used by the classification proof.
-/

namespace TraceEuclidean

open scoped NumberField

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- The field definition with its rational-valued trace before casting to `ℝ`. -/
def IsFieldTwoTraceEuclideanRat : Prop :=
  ∀ x : F, ∃ y : 𝓞 F,
    Algebra.trace ℚ F ((x - (y : F)) ^ 2) < 2

theorem fieldTwoTraceEuclideanRat_iff_real :
    IsFieldTwoTraceEuclideanRat (F := F) ↔
      IsFieldTraceEuclidean (F := F) 2 := by
  constructor
  · intro h x
    obtain ⟨y, hy⟩ := h x
    refine ⟨y, ?_⟩
    exact_mod_cast hy
  · intro h x
    obtain ⟨y, hy⟩ := h x
    refine ⟨y, ?_⟩
    exact_mod_cast hy

/--
The standard integral-basis presentation of `ℚ(√m)`.  Its fields record the
linear coordinates, the bijection between algebraic integers and `ℤ²`, and
the trace-square calculation.  This isolates the one algebraic number theory
bridge not currently supplied by mathlib.
-/
structure RealQuadraticCoordinateModel (F : Type*) [Field F] [NumberField F]
    (m : ℕ) where
  coordinates : F ≃ₗ[ℚ] RationalPoint
  integerCoordinates : (𝓞 F) ≃+ IntegralPoint
  trace_formula : ∀ x : F, ∀ y : 𝓞 F,
    Algebra.trace ℚ F ((x - (y : F)) ^ 2) =
      realQuadraticCostRat m (coordinates x) (integerCoordinates y)

namespace RealQuadraticCoordinateModel

theorem field_iff_coordinate {m : ℕ}
    (M : RealQuadraticCoordinateModel F m) :
    IsFieldTwoTraceEuclideanRat (F := F) ↔
      CoordinateTwoTraceEuclidean m := by
  constructor
  · intro h x
    obtain ⟨y, hy⟩ := h (M.coordinates.symm x)
    refine ⟨M.integerCoordinates y, ?_⟩
    rw [M.trace_formula] at hy
    simpa using hy
  · intro h x
    obtain ⟨z, hz⟩ := h (M.coordinates x)
    let y : 𝓞 F := M.integerCoordinates.symm z
    refine ⟨y, ?_⟩
    rw [M.trace_formula]
    simpa only [y, AddEquiv.apply_symm_apply] using hz

/-- Theorem 1.8 after supplying the standard real-quadratic coordinate model. -/
theorem field_two_trace_euclidean_iff {m : ℕ}
    (M : RealQuadraticCoordinateModel F m)
    (hm : 1 < m) (hsq : IsSquarefreeNat m) :
    IsFieldTraceEuclidean (F := F) 2 ↔
      m = 2 ∨ m = 5 ∨ m = 13 := by
  rw [← fieldTwoTraceEuclideanRat_iff_real, M.field_iff_coordinate]
  exact coordinate_two_trace_euclidean_iff hm hsq

end RealQuadraticCoordinateModel

end


end TraceEuclidean
