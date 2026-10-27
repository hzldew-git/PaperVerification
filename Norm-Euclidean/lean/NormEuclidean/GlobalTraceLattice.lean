import NormEuclidean.TraceTensorDuality
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
# The global codifferent after actual integral scalar extension

The global integer lattice and its actual trace-dual fractional ideal
are extended into the genuine tensor algebra. The scalar-extended
trace dual is proved equal to the extension of that global codifferent,
without a local integrality or trace-comparison premise.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.GlobalTraceLattice

open Module NumberField Algebra
open scoped NumberField TensorProduct nonZeroDivisors

variable (F : Type*) [Field F] [NumberField F]
variable (A : Type*) [Field A] [Algebra ℚ A]

/-- The canonical global inclusion into the actual scalar extension, as an integer-linear map. -/
def inclusion : F →ₗ[ℤ] A ⊗[ℚ] F :=
  (Algebra.TensorProduct.includeRight : F →ₐ[ℚ] A ⊗[ℚ] F).toLinearMap.restrictScalars ℤ

theorem inclusion_apply (x : F) : inclusion F A x = 1 ⊗ₜ[ℚ] x := rfl

/-- The global integer lattice in its original fraction field. -/
def integers : Submodule ℤ F := (1 : Submodule (𝓞 F) F).restrictScalars ℤ

/-- The literal global trace codifferent, not a newly prescribed lattice. -/
def codifferent : Submodule ℤ F :=
  (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) :
    Submodule (𝓞 F) F).restrictScalars ℤ

theorem integers_span : integers F = Submodule.span ℤ (Set.range (integralBasis F)) := by
  ext x
  simpa only [integers, Submodule.restrictScalars_mem, Submodule.mem_one, RingHom.mem_range]
    using (mem_span_integralBasis F (x := x)).symm

theorem codifferent_span :
    codifferent F = Submodule.span ℤ (Set.range (integralBasis F).traceDual) := by
  change ((FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) :
    Submodule (𝓞 F) F).restrictScalars ℤ) = _
  rw [FractionalIdeal.coe_dual_one]
  exact Submodule.traceDual_span_of_basis (K := ℚ) ℤ 1 (integralBasis F) (integers_span F)

variable (R : Type*) [CommRing R] [Algebra R A]

/-- Integral scalar extension of an actual global lattice, inside the actual tensor algebra. -/
def extend (I : Submodule ℤ F) : Submodule R (A ⊗[ℚ] F) :=
  Submodule.span R (inclusion F A '' (I : Set F))

/-- Extension of a finitely generated span is the span of its actual tensor images. -/
theorem extend_span (s : Set F) :
    extend F A R (Submodule.span ℤ s) = Submodule.span R (inclusion F A '' s) := by
  unfold extend
  rw [← Submodule.map_coe, Submodule.map_span, Submodule.span_span_of_tower]

/-- The extended global integers have the literal base-changed integral basis. -/
theorem extend_integers : extend F A R (integers F) =
    Submodule.span R (Set.range (Algebra.TensorProduct.basis A (integralBasis F))) := by
  rw [integers_span, extend_span]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_range, inclusion_apply, Algebra.TensorProduct.basis_apply]
  exact ⟨fun ⟨y, ⟨i, hi⟩, hy⟩ ↦ ⟨i, hi ▸ hy⟩, fun ⟨i, hi⟩ ↦ ⟨_, ⟨i, rfl⟩, hi⟩⟩

/-- The same basis statement is proved for the actual global codifferent. -/
theorem extend_codifferent : extend F A R (codifferent F) =
    Submodule.span R (Set.range (Algebra.TensorProduct.basis A (integralBasis F).traceDual)) := by
  rw [codifferent_span, extend_span]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_range, inclusion_apply, Algebra.TensorProduct.basis_apply]
  exact ⟨fun ⟨y, ⟨i, hi⟩, hy⟩ ↦ ⟨i, hi ▸ hy⟩, fun ⟨i, hi⟩ ↦ ⟨_, ⟨i, rfl⟩, hi⟩⟩

/-- Trace duality commutes with integral completion at the full tensor-lattice level. -/
theorem dual_extend_integers :
    (Algebra.traceForm A (A ⊗[ℚ] F)).dualSubmodule (extend F A R (integers F)) =
      extend F A R (codifferent F) := by
  rw [extend_integers, extend_codifferent, TraceTensorDuality.dual_span]

end NormEuclidean.GlobalTraceLattice
