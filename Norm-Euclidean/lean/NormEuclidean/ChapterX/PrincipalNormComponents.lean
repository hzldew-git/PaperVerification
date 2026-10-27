import NormEuclidean.ChapterX.InfiniteCompletedNorm
import NormEuclidean.ChapterX.QuadraticCompletedNorm

/-!
# Principal idele comparison at the proved places

The comparison is unconditional at all infinite places and at nonsplit
finite places of the quadratic extension. The general finite theorem retains
only the explicit injectivity obligation for the actual tensor comparison.
-/

noncomputable section

namespace NormEuclidean.PrincipalNormComponents

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm
open scoped NumberField

universe u
variable {K E : Type u} [Field K] [NumberField K]
  [Field E] [NumberField E] [Algebra K E]

/-- The actual global field norm on units. -/
def globalNormUnits : Eˣ →* Kˣ := Units.map (Algebra.norm K)

/-- Finite evaluation of a principal idele is the embedded global unit. -/
theorem finiteComponent_principal (p : HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    ideleFiniteComponent p (idelePrincipalEmbedding x) =
      Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom x := rfl

/-- Infinite evaluation of a principal idele is the embedded global unit. -/
theorem infiniteComponent_principal (v : NumberField.InfinitePlace K) (x : Kˣ) :
    ideleInfiniteComponent v (idelePrincipalEmbedding x) =
      Units.map (algebraMap K v.Completion).toMonoidHom x := rfl

open scoped NormEuclidean.InfiniteCompletedNorm NumberField.LiesOver

/-- The assembled idele norm commutes with the principal embedding
at every infinite place. No local or global norm principle is assumed. -/
theorem infinite_principal_norm (v : NumberField.InfinitePlace K) (x : Eˣ) :
    ideleInfiniteComponent v (extensionIdeleNorm (K := K) (idelePrincipalEmbedding x)) =
      ideleInfiniteComponent v (idelePrincipalEmbedding (globalNormUnits (K := K) x)) := by
  apply Units.ext
  rw [ideleInfiniteComponent_extensionIdeleNorm]
  change ((∏ w : InfinitePlacesAbove (E := E) v,
    infinitePlaceAboveNormUnits v w (ideleInfiniteComponent w.1 (idelePrincipalEmbedding x)) :
      v.Completionˣ) : v.Completion) = _
  rw [Units.coe_prod]
  exact InfiniteCompletedNorm.norm_global v (x : E)

open scoped NormEuclidean.CompletedExtensionProduct

/-- For a general finite place, injectivity of the actual completed tensor
comparison is precisely the remaining input to principal-norm compatibility. -/
theorem finite_principal_norm_of_injective (p : HeightOneSpectrum (𝓞 K))
    (hinj : Function.Injective (CompletedExtensionProduct.comparison (E := E) p)) (x : Eˣ) :
    ideleFiniteComponent p (extensionIdeleNorm (K := K) (idelePrincipalEmbedding x)) =
      ideleFiniteComponent p (idelePrincipalEmbedding (globalNormUnits (K := K) x)) := by
  apply Units.ext
  rw [ideleFiniteComponent_extensionIdeleNorm]
  change ((∏ w : FinitePlacesAbove (E := E) p,
    finitePlaceAboveNormUnits p w (ideleFiniteComponent w.1 (idelePrincipalEmbedding x)) :
      (p.adicCompletion K)ˣ) : p.adicCompletion K) = _
  rw [Units.coe_prod]
  exact CompletedNormComparison.norm_global_of_injective p hinj (x : E)

/-- Principal-norm compatibility at a nonsplit finite quadratic place,
with tensor injectivity proved from the local nonsquare parameter. -/
theorem finite_principal_norm_nonsplit (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 K))
    (hlocal : ¬ IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta)) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    ∀ x : (QuadraticAlgebra K (theta : K) 0)ˣ,
      ideleFiniteComponent p (extensionIdeleNorm (K := K) (idelePrincipalEmbedding x)) =
        ideleFiniteComponent p (idelePrincipalEmbedding (globalNormUnits (K := K) x)) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  exact finite_principal_norm_of_injective p
    (QuadraticCompletedNorm.comparison_injective_of_nonsquare theta htheta p hlocal)

end NormEuclidean.PrincipalNormComponents
