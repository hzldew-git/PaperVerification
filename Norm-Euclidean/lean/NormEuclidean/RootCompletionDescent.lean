import NormEuclidean.InfiniteUnramifiedSquareClasses

/-!
# Square roots descend through actual degree-one finite completions

The extension is any actual number field, rather than a supplied quadratic
algebra. This lets a degree-two field choose its presentation internally.
-/

noncomputable section

namespace NormEuclidean.RootCompletionDescent

open IsDedekindDomain ExtensionIdeleNorm
open scoped NumberField NormEuclidean.CompletedExtensionProduct

universe u
variable {K E : Type u} [Field K] [NumberField K]
  [Field E] [NumberField E] [Algebra K E]

/-- A root in the global extension descends at any actual degree-one completion. -/
theorem isSquare_of_degree_one (eta : Kˣ) (s : E)
    (hs : s ^ 2 = algebraMap K E (eta : K)) (p : HeightOneSpectrum (𝓞 K))
    (w : FinitePlacesAbove (E := E) p)
    (hw : Module.finrank (p.adicCompletion K) (w.1.adicCompletion E) = 1) :
    IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom eta) := by
  apply InfiniteUnramifiedSquareClasses.isSquare_of_local_degree_one hw _
    (algebraMap E (w.1.adicCompletion E) s)
  rw [← map_pow, hs]
  exact (finitePlaceAboveCompletionMap_global p w (eta : K)).symm

end NormEuclidean.RootCompletionDescent
