import NormEuclidean.ChapterX.ScalarExtensionNorm
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Scalar extension of the concrete quadratic algebra

The tensor product is identified with the quadratic algebra over the new
base field, whether the parameter stays nonsquare or becomes a square.
This algebraic comparison does not assert a factorization by places.
-/

noncomputable section

namespace NormEuclidean.QuadraticScalarExtension

open scoped TensorProduct QuadraticAlgebra

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Extending the two coordinates gives the natural map of quadratic algebras. -/
def coordinateMap (theta : K) :
    QuadraticAlgebra K theta 0 →ₐ[K] QuadraticAlgebra F (algebraMap K F theta) 0 where
  toFun z := ⟨algebraMap K F z.re, algebraMap K F z.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' z w := by ext <;> simp
  map_mul' z w := by ext <;> simp [map_add, map_mul]
  commutes' a := by
    rw [IsScalarTower.algebraMap_apply K F
      (QuadraticAlgebra F (algebraMap K F theta) 0)]
    ext <;> simp

/-- The universal scalar-extension map to the quadratic algebra over `F`. -/
def comparison (theta : K) :
    F ⊗[K] QuadraticAlgebra K theta 0 →ₐ[F]
      QuadraticAlgebra F (algebraMap K F theta) 0 :=
  Algebra.TensorProduct.lift
    (Algebra.ofId F (QuadraticAlgebra F (algebraMap K F theta) 0))
    (coordinateMap theta) (fun _ _ ↦ mul_comm ..)

/-- Pure tensors are mapped by scaling the two extended coordinates. -/
theorem comparison_tmul (theta : K) (a : F) (z : QuadraticAlgebra K theta 0) :
    comparison theta (a ⊗ₜ[K] z) = a • coordinateMap theta z := by
  simp [comparison, Algebra.smul_def]

/-- Every pair of coordinates comes from the tensors on `1` and `sqrt(theta)`. -/
theorem comparison_surjective (theta : K) :
    Function.Surjective (comparison (F := F) theta) := by
  intro z
  refine ⟨z.re ⊗ₜ[K] (1 : QuadraticAlgebra K theta 0) +
    z.im ⊗ₜ[K] (⟨0, 1⟩ : QuadraticAlgebra K theta 0), ?_⟩
  rw [map_add, comparison_tmul, comparison_tmul]
  ext <;> simp [coordinateMap]

/-- The scalar-extension comparison is bijective because both sides have
dimension two. This does not use a dimension formula for completed fields. -/
theorem comparison_bijective (theta : K) :
    Function.Bijective (comparison (F := F) theta) := by
  have hd : Module.finrank F (F ⊗[K] QuadraticAlgebra K theta 0) =
      Module.finrank F (QuadraticAlgebra F (algebraMap K F theta) 0) := by
    simp only [Module.finrank_baseChange, QuadraticAlgebra.finrank_eq_two]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr
    (comparison_surjective theta), comparison_surjective theta⟩

/-- Scalar extension of a quadratic algebra, including its split specialization. -/
def equiv (theta : K) :
    (F ⊗[K] QuadraticAlgebra K theta 0) ≃ₐ[F]
      QuadraticAlgebra F (algebraMap K F theta) 0 :=
  AlgEquiv.ofBijective (comparison theta) (comparison_bijective theta)

/-- The norm of the extended global element is the extended global norm,
computed in the actual quadratic algebra over `F`. -/
theorem norm_coordinateMap (theta : K) (z : QuadraticAlgebra K theta 0) :
    Algebra.norm F (coordinateMap (F := F) theta z) =
      algebraMap K F (Algebra.norm K z) := by
  calc
    _ = Algebra.norm F (equiv (F := F) theta (1 ⊗ₜ[K] z)) := by
      simp [equiv, comparison_tmul]
    _ = Algebra.norm F ((1 : F) ⊗ₜ[K] z) := Algebra.norm_eq_of_algEquiv _ _
    _ = _ := ScalarExtensionNorm.norm_one_tmul z

end NormEuclidean.QuadraticScalarExtension
