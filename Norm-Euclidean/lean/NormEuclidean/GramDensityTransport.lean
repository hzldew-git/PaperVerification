import NormEuclidean.BinaryCongruenceDensity
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Integral basis invariance of binary Gram congruence counts

All matrices satisfying the actual Gram equation are retained, including
singular solutions at degenerate congruence levels. Invertible integral
basis changes act by conjugation. A unit scalar cancels from the equation.
-/

noncomputable section

namespace NormEuclidean.GramDensityTransport

open scoped Matrix

variable {R : Type*} [CommRing R]

/-- The actual full Gram solution set for an arbitrary binary matrix. -/
def Solutions (G : Matrix (Fin 2) (Fin 2) R) :=
  {M : Matrix (Fin 2) (Fin 2) R // M.transpose * G * M = G}

/-- The normalized full congruence count, with the binary factor one half. -/
def density (G : Matrix (Fin 2) (Fin 2) R) : ℝ :=
  (Nat.card (Solutions G) : ℝ) / (2 * Nat.card R)

private theorem transpose_cancel (P : (Matrix (Fin 2) (Fin 2) R)ˣ)
    (A : Matrix (Fin 2) (Fin 2) R) :
    (P⁻¹ : (Matrix (Fin 2) (Fin 2) R)ˣ).val.transpose * (P.val.transpose * A) = A := by
  rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv,
    Matrix.transpose_one, Matrix.one_mul]

private def conjugate (P : (Matrix (Fin 2) (Fin 2) R)ˣ)
    (G : Matrix (Fin 2) (Fin 2) R) (M : Solutions G) :
    Solutions (P.val.transpose * G * P.val) :=
  ⟨(P⁻¹ : (Matrix (Fin 2) (Fin 2) R)ˣ).val * M.val * P.val, by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left,
      transpose_cancel]
    simpa only [Matrix.mul_assoc] using congrArg
      (fun A ↦ P.val.transpose * A * P.val) M.property⟩

/-- Conjugation gives a literal equivalence of the two full Gram solution sets. -/
def basisEquiv (G : Matrix (Fin 2) (Fin 2) R)
    (P : (Matrix (Fin 2) (Fin 2) R)ˣ) :
    Solutions G ≃ Solutions (P.val.transpose * G * P.val) where
  toFun := conjugate P G
  invFun M := ⟨P.val * M.val * (P⁻¹ : (Matrix (Fin 2) (Fin 2) R)ˣ).val, by
    have h := (conjugate P⁻¹ (P.val.transpose * G * P.val) M).property
    simpa only [conjugate, inv_inv, Matrix.mul_assoc, transpose_cancel,
      Units.mul_inv_cancel_right] using h⟩
  left_inv M := by
    apply Subtype.ext
    simp only [conjugate, Matrix.mul_assoc, Units.mul_inv_cancel_left,
      Units.mul_inv_cancel_right]
  right_inv M := by
    apply Subtype.ext
    simp only [conjugate, Matrix.mul_assoc, Units.inv_mul_cancel_left,
      Units.inv_mul_cancel_right]

/-- A unit multiple of a Gram matrix has exactly the same solutions. -/
def unitEquiv (G : Matrix (Fin 2) (Fin 2) R) (a : Rˣ) :
    Solutions G ≃ Solutions ((a : R) • G) where
  toFun M := ⟨M.val, by
    rw [Matrix.mul_smul, Matrix.smul_mul, M.property]⟩
  invFun M := ⟨M.val, by
    have h : (a : R) • (M.val.transpose * G * M.val) = (a : R) • G := by
      simpa only [Matrix.mul_smul, Matrix.smul_mul] using M.property
    have hi := congrArg (fun A ↦ (a⁻¹ : Rˣ).val • A) h
    simpa only [smul_smul, Units.inv_mul, one_smul] using hi⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Integral basis changes preserve the normalized full congruence count. -/
theorem density_basis (G : Matrix (Fin 2) (Fin 2) R)
    (P : (Matrix (Fin 2) (Fin 2) R)ˣ) : density (P.val.transpose * G * P.val) = density G := by
  unfold density
  rw [← Nat.card_congr (basisEquiv G P)]

/-- Unit rescaling preserves the normalized full congruence count. -/
theorem density_unit (G : Matrix (Fin 2) (Fin 2) R) (a : Rˣ) :
    density ((a : R) • G) = density G := by
  unfold density
  rw [← Nat.card_congr (unitEquiv G a)]

/-- Agreement with the preceding norm-model density definition. -/
theorem density_norm_model (d : R) :
    density (BinaryCongruenceDensity.gram d) = BinaryCongruenceDensity.selfDensity R d := rfl

/-- Over a local ring, nonzero Gram determinant forces every counted matrix
to be invertible, even when the determinant is a nonunit at a ramified level. -/
theorem solution_isUnit [IsLocalRing R] (G : Matrix (Fin 2) (Fin 2) R)
    (hG : G.det ≠ 0) (M : Solutions G) : IsUnit M.val := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  have hd := congrArg Matrix.det M.property
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  by_contra hn
  have hsq : ¬ IsUnit (M.val.det ^ 2) := by simpa [pow_two] using hn
  have hu := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (M.val.det ^ 2) hsq
  apply hG
  apply hu.mul_right_cancel
  linear_combination -hd

end NormEuclidean.GramDensityTransport
