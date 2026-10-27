import NormEuclidean.ChapterX.CompletedExtensionProduct
import NormEuclidean.ChapterX.ScalarExtensionNorm
import NormEuclidean.ChapterX.ProductNorm

/-!
# Norm transport along the actual finite-completion comparison

The still separate injectivity obligation is explicit. Surjectivity,
scalar-extension compatibility, and the dependent product norm formula
are already proved and are not supplied as hypotheses.
-/

noncomputable section

namespace NormEuclidean.CompletedNormComparison

open IsDedekindDomain ExtensionIdeleNorm CompletedExtensionProduct
open scoped NumberField TensorProduct NormEuclidean.CompletedExtensionProduct

universe u
variable {K E : Type u} [Field K] [NumberField K]
  [Field E] [NumberField E] [Algebra K E]

/-- Injectivity is the sole outstanding condition for transporting norms
through the actual product of finite completions. -/
theorem norm_comparison_of_injective (p : HeightOneSpectrum (𝓞 K))
    (hinj : Function.Injective (comparison (E := E) p))
    (y : p.adicCompletion K ⊗[K] E) :
    (∏ w : FinitePlacesAbove (E := E) p,
      Algebra.norm (p.adicCompletion K) (comparison p y w)) =
        Algebra.norm (p.adicCompletion K) y := by
  let e := AlgEquiv.ofBijective (comparison (E := E) p) ⟨hinj, comparison_surjective p⟩
  rw [← ProductNorm.norm_pi]
  exact Algebra.norm_eq_of_algEquiv e y

/-- Once injectivity is proved, the product of completed norms of a global
element is its global field norm embedded at the base place. -/
theorem norm_global_of_injective (p : HeightOneSpectrum (𝓞 K))
    (hinj : Function.Injective (comparison (E := E) p)) (x : E) :
    (∏ w : FinitePlacesAbove (E := E) p,
      Algebra.norm (p.adicCompletion K) (algebraMap E (w.1.adicCompletion E) x)) =
        algebraMap K (p.adicCompletion K) (Algebra.norm K x) := by
  have h := norm_comparison_of_injective p hinj ((1 : p.adicCompletion K) ⊗ₜ[K] x)
  simpa only [comparison_tmul, map_one, one_mul, ScalarExtensionNorm.norm_one_tmul] using h

end NormEuclidean.CompletedNormComparison
