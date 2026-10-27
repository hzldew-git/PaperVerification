import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Determinant norms and scalar extension

The equality on scalar-extended global elements is checked directly from
the base-changed multiplication matrix. It does not require a completion
factorization, a local-global theorem, or any norm-index statement.
-/

noncomputable section

namespace NormEuclidean.ScalarExtensionNorm

open scoped TensorProduct

variable {K F E : Type*} [Field K] [CommRing F] [Algebra K F]
  [CommRing E] [Algebra K E] [FiniteDimensional K E]

/-- The multiplication matrix of a scalar-extended element is the image of the
original multiplication matrix under the scalar embedding. -/
theorem leftMulMatrix_baseChange (x : E) :
    Algebra.leftMulMatrix ((Module.finBasis K E).baseChange F) ((1 : F) ⊗ₜ[K] x) =
      (Algebra.leftMulMatrix (Module.finBasis K E) x).map (algebraMap K F) := by
  ext i j
  simp only [Algebra.leftMulMatrix_eq_repr_mul, Module.Basis.baseChange_apply,
    Algebra.TensorProduct.tmul_mul_tmul, Module.Basis.baseChange_repr_tmul,
    Matrix.map_apply, Algebra.smul_def, mul_one]

/-- The determinant norm commutes with scalar extension on global elements. -/
theorem norm_one_tmul (x : E) :
    Algebra.norm F ((1 : F) ⊗ₜ[K] x) = algebraMap K F (Algebra.norm K x) := by
  rw [Algebra.norm_eq_matrix_det ((Module.finBasis K E).baseChange F),
    leftMulMatrix_baseChange, Algebra.norm_eq_matrix_det (Module.finBasis K E)]
  exact ((algebraMap K F).map_det _).symm

end NormEuclidean.ScalarExtensionNorm
