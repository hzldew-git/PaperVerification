import NormEuclidean.HilbertIdeleArtin
import NormEuclidean.BinaryDiscriminantField
import NormEuclidean.QuadraticUnramifiedArithmetic

/-!
# Idelic norm correction from an actual quadratic Hilbert field equality

The sole arithmetic input is equality of the root field with the ordinary
Hilbert class field. Its degree, unramifiedness, unit norm lifting, and the
principal-times-norm kernel are derived without a Euclidean lattice.
-/

noncomputable section

namespace NormEuclidean.HilbertQuadraticNorm

open ExtensionIdeleNorm QuadraticExtensionNorm FullIdeleClassKernel
open scoped NumberField IntermediateField

variable {K : Type} [Field K] [NumberField K]
  (theta : Kˣ) (htheta : ¬IsSquare theta) (r : SeparableClosure K)
  (hr : r ^ 2 = algebraMap K (SeparableClosure K) (theta : K))
  (hfield : K⟮r⟯ = HilbertClassFieldArithmetic.field K)

/-- The concrete quadratic algebra is the actual Hilbert field over the base. -/
def equiv :
    letI := quadraticExtensionField theta htheta
    QuadraticAlgebra K (theta : K) 0 ≃ₐ[K] HilbertClassFieldArithmetic.field K := by
  letI := quadraticExtensionField theta htheta
  exact (QuadraticRootFields.equivAdjoin theta htheta r hr).trans
    (IntermediateField.equivOfEq hfield)

include theta htheta r hr hfield

/-- Equality with the nonsplit quadratic root field forces ordinary class number two. -/
theorem class_number_two : NumberField.classNumber K = 2 := by
  rw [← HilbertClassFieldArithmetic.degree_eq_class_number, ← hfield]
  exact QuadraticRootFields.finrank_adjoin theta htheta r hr

/-- The algebra identification preserves the determinant norm used in the idele chain. -/
theorem norm_equiv :
    letI := quadraticExtensionField theta htheta
    ∀ z : QuadraticAlgebra K (theta : K) 0,
      Algebra.norm K (equiv theta htheta r hr hfield z) = Algebra.norm K z := by
  letI := quadraticExtensionField theta htheta
  exact Algebra.norm_eq_of_algEquiv (equiv theta htheta r hr hfield)

/-- Both finite unramifiedness and splitting at infinity follow from the field equality. -/
theorem everywhere_unramified :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    ClassFieldTheory.IsEverywhereUnramified K (QuadraticAlgebra K (theta : K) 0) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  exact (ClassFieldTheory.isEverywhereUnramified_iff_of_algEquiv K
    (QuadraticAlgebra K (theta : K) 0) (HilbertClassFieldArithmetic.field K)
    (equiv theta htheta r hr hfield)).mpr
      (HilbertClassFieldArithmetic.specification K).1

/-- Every ordinary unit idele has a genuine quadratic extension norm preimage. -/
theorem unitIdeles_le_norm :
    unitIdeles ≤ (quadraticExtensionIdeleNorm theta htheta).range := by
  have hunram := everywhere_unramified theta htheta r hr hfield
  exact QuadraticUnramifiedArithmetic.unitIdeles_le_norm theta htheta
    hunram.1 hunram.2.isUnramified

/-- The actual principal-times-norm subgroup equals the ordinary ideal class kernel. -/
theorem principal_norm_eq_kernel :
    idelePrincipalEmbedding.range ⊔ (quadraticExtensionIdeleNorm theta htheta).range =
      (FullIdeleClassKernel.classHom (K := K)).ker :=
  FullIdeleClassKernel.principal_norm_eq_kernel theta htheta
    (class_number_two theta htheta r hr hfield)
    (unitIdeles_le_norm theta htheta r hr hfield)

/-- Actual quadratic idele norms lie in the Hilbert Artin kernel without Euclidean data. -/
theorem artin_norm (i : NumberFieldIdele K)
    (hi : i ∈ (quadraticExtensionIdeleNorm theta htheta).range) :
    HilbertIdeleArtin.artin K i = 1 := by
  change i ∈ (HilbertIdeleArtin.artin K).ker
  rw [HilbertIdeleArtin.ker_eq, ← principal_norm_eq_kernel theta htheta r hr hfield]
  exact (show (quadraticExtensionIdeleNorm theta htheta).range ≤
    idelePrincipalEmbedding.range ⊔ (quadraticExtensionIdeleNorm theta htheta).range from
      le_sup_right) hi

end NormEuclidean.HilbertQuadraticNorm
