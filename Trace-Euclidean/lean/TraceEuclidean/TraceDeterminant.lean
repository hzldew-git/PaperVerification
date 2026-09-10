import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Norm.Transitivity

/-!
Determinant of a scalar-restricted bilinear form.  If a bilinear form over a
finite field extension has Gram matrix `G`, then the determinant of its trace
form is the discriminant of the extension to the power of the form rank,
times the field norm of `det G`.

This is the algebraic block-determinant identity used in the trace-lattice
covolume calculation.  It is stated independently of number fields and
lattices so that its trust boundary is entirely in Lean and mathlib.
-/

namespace TraceEuclidean

open Matrix
open Module

noncomputable section

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
variable [Fintype κ] [DecidableEq κ]

/-- The block matrix of the trace form in the tower basis. -/
def traceBlockMatrix (b : Basis ι K F) (G : Matrix κ κ F) :
    Matrix (κ × ι) (κ × ι) K :=
  fun ia jb ↦ Algebra.trace K F (b ia.2 * b jb.2 * G ia.1 jb.1)

/-- Multiplying the left-regular blocks by the trace matrix gives the trace
Gram blocks. -/
theorem traceBlockMatrix_eq_mul (b : Basis ι K F) (G : Matrix κ κ F) :
    traceBlockMatrix b G =
      Matrix.kronecker (1 : Matrix κ κ K) (Algebra.traceMatrix K b) *
        ((G.map (Algebra.leftMulMatrix b)).comp κ κ ι ι K) := by
  ext ⟨i, a⟩ ⟨j, c⟩
  simp only [traceBlockMatrix, Matrix.mul_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.comp_apply, Matrix.map_apply,
    Matrix.one_apply]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp only [ite_mul, one_mul, zero_mul]
  have h := congrFun (Algebra.traceMatrix_of_basis_mulVec b (G i j * b c)) a
  simpa [Matrix.mulVec, dotProduct, Algebra.leftMulMatrix_eq_repr_mul,
    mul_assoc, mul_comm, mul_left_comm] using h.symm

/-- Determinant formula for the trace block matrix. -/
theorem det_traceBlockMatrix (b : Basis ι K F) (G : Matrix κ κ F) :
    (traceBlockMatrix b G).det =
      Algebra.discr K b ^ Fintype.card κ * Algebra.norm K G.det := by
  rw [traceBlockMatrix_eq_mul, Matrix.det_mul]
  unfold Matrix.kronecker
  rw [Matrix.det_kronecker]
  simp only [Matrix.det_one, one_pow, one_mul]
  have hcomp :
      (Algebra.leftMulMatrix b G.det).det =
        ((G.map (Algebra.leftMulMatrix b)).comp κ κ ι ι K).det := by
    simpa using
      (Matrix.det_det (M := G) (Algebra.leftMulMatrix b).toRingHom)
  rw [← hcomp]
  rw [← Algebra.norm_eq_matrix_det b]
  rfl

end

end TraceEuclidean
