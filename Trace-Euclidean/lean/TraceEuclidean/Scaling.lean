import Mathlib

/-!
Scaling a quadratic form by a nonzero scalar neither creates nor destroys an
isometry.  This is the precise replacement for identifying the two class
symbols in the manuscript proof.
-/

namespace TraceEuclidean

/-- Preservation of a form-valued function by an equivalence. -/
def PreservesForm {R V W : Type*} (Q : V → R) (Q' : W → R)
    (e : V ≃ W) : Prop :=
  ∀ x, Q' (e x) = Q x

/-- Scalar multiplication of a form-valued function. -/
def scaleForm {R V : Type*} [Mul R] (c : R) (Q : V → R) : V → R :=
  fun x ↦ c * Q x

/-- Isometry expressed without choosing a preferred equivalence. -/
def IsometricForms {R V W : Type*} (Q : V → R) (Q' : W → R) : Prop :=
  ∃ e : V ≃ W, PreservesForm Q Q' e

theorem preserves_scaled_iff {R V W : Type*} [MonoidWithZero R] [IsCancelMulZero R]
    {c : R} (hc : c ≠ 0) {Q : V → R} {Q' : W → R} (e : V ≃ W) :
    PreservesForm (scaleForm c Q) (scaleForm c Q') e ↔
      PreservesForm Q Q' e := by
  constructor
  · intro h x
    exact mul_left_cancel₀ hc (h x)
  · intro h x
    simp only [scaleForm, h x]

theorem isometric_scaled_iff {R V W : Type*} [MonoidWithZero R] [IsCancelMulZero R]
    {c : R} (hc : c ≠ 0) {Q : V → R} {Q' : W → R} :
    IsometricForms (scaleForm c Q) (scaleForm c Q') ↔
      IsometricForms Q Q' := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, (preserves_scaled_iff hc e).mp he⟩
  · rintro ⟨e, he⟩
    exact ⟨e, (preserves_scaled_iff hc e).mpr he⟩

/-- The factor-two instance used for integral quadratic lattices. -/
theorem two_scaled_isometric_iff {V W : Type*} {Q : V → ℝ} {Q' : W → ℝ} :
    IsometricForms (scaleForm 2 Q) (scaleForm 2 Q') ↔
      IsometricForms Q Q' := by
  exact isometric_scaled_iff (by norm_num : (2 : ℝ) ≠ 0)

end TraceEuclidean
