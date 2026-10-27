import NormEuclidean.ChapterX.SquareIdeleIndex
import NormEuclidean.ChapterX.QuadraticNormPrimeChain

/-!
# O'Meara 65:21 for actual quadratic number-field ideles

The separating primes, strict subgroup chain, initial square index and
norm-index lower bound are all proved. The remaining admissible core
is chosen internally, so the final theorem has no arithmetic-index premise.
-/

noncomputable section

namespace NormEuclidean.QuadraticGlobalNormIndex

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm
open scoped NumberField

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- A genuine quadratic extension has global principal-times-norm idele index exactly two. -/
theorem index_two (theta : Kˣ) (htheta : ¬ IsSquare theta) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    (idelePrincipalEmbedding.range ⊔ (extensionIdeleNorm (K := K)
      (E := QuadraticAlgebra K theta.val 0)).range).index = 2 := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  obtain ⟨S, hS, _, _, htwo, hunit, hprincipal⟩ :=
    exists_admissible_common_core (E := QuadraticAlgebra K theta.val 0)
      theta ∅ Set.finite_empty
  exact QuadraticNormPrimeChain.index_two_of_square_index theta htheta S hS htwo hunit
    (hprincipal S le_rfl).1 (SquareIdeleIndex.index S hS htwo (hprincipal S le_rfl).1)

end NormEuclidean.QuadraticGlobalNormIndex
