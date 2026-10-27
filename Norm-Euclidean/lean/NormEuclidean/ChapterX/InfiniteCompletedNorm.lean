import NormEuclidean.ChapterX.ExtensionNormComponents
import NormEuclidean.ChapterX.MixedScalarWeakApproximation
import NormEuclidean.ChapterX.ScalarExtensionNorm
import NormEuclidean.ChapterX.ProductNorm
import Mathlib.NumberTheory.NumberField.Completion.Ramification

/-!
# Completed product factorization and norms at infinite places

Weak approximation gives a dense image, finite-dimensional closedness gives
surjectivity, and the proved infinite-place degree sum gives injectivity.
All factors are the actual extension completions above the base place.
-/

noncomputable section

namespace NormEuclidean.InfiniteCompletedNorm

open ExtensionIdeleNorm NumberField
open scoped NumberField TensorProduct NormEuclidean.ExtensionPlaces

universe u
variable {K E : Type u} [Field K] [NumberField K]
  [Field E] [NumberField E] [Algebra K E]

scoped instance componentLiesOver (v : InfinitePlace K) (w : InfinitePlacesAbove (E := E) v) :
    w.1.1.LiesOver v.1 := ⟨congrArg Subtype.val w.2⟩

open scoped NumberField.LiesOver

scoped instance componentFinite (v : InfinitePlace K) (w : InfinitePlacesAbove (E := E) v) :
    Module.Finite v.Completion w.1.Completion := infinitePlaceAbove_moduleFinite v w

/-- All extension completions above one infinite place, with their canonical algebra. -/
abbrev Product (v : InfinitePlace K) := (w : InfinitePlacesAbove (E := E) v) → w.1.Completion

/-- The canonical completed scalar-extension map at an infinite place. -/
def comparison (v : InfinitePlace K) :
    v.Completion ⊗[K] E →ₐ[v.Completion] Product (E := E) v :=
  AlgHom.pi fun w ↦ Algebra.TensorProduct.lift
    (Algebra.algHom v.Completion v.Completion w.1.Completion)
    (Algebra.algHom K E w.1.Completion) (fun _ _ ↦ mul_comm ..)

/-- Pure tensors map to the product of the base and extension embeddings. -/
theorem comparison_tmul (v : InfinitePlace K) (a : v.Completion) (x : E)
    (w : InfinitePlacesAbove (E := E) v) :
    comparison v (a ⊗ₜ[K] x) w =
      infinitePlaceAboveCompletionMap v w a * algebraMap E w.1.Completion x := rfl

/-- The diagonal extension field is dense in the complete infinite fiber. -/
theorem denseRange_diagonal (v : InfinitePlace K) :
    DenseRange (fun x : E ↦ fun w : InfinitePlacesAbove (E := E) v ↦
      algebraMap E w.1.Completion x) := by
  let q : InfinitePlacesAbove (E := E) v → MixedScalarWeakApproximation.Place E :=
    fun w ↦ .inr w.1
  exact MixedScalarWeakApproximation.denseRange_diagonal_of_injective q
    (fun _ _ h ↦ Subtype.ext (Sum.inr_injective h))

/-- The completed comparison has dense image. -/
theorem comparison_denseRange (v : InfinitePlace K) :
    DenseRange (comparison (E := E) v) := by
  apply (denseRange_diagonal (E := E) v).mono
  rintro _ ⟨x, rfl⟩
  refine ⟨1 ⊗ₜ[K] x, ?_⟩
  funext w
  simp only [comparison_tmul, map_one, one_mul]

/-- The completed comparison is onto by density and finite-dimensional closedness. -/
theorem comparison_surjective (v : InfinitePlace K) :
    Function.Surjective (comparison (E := E) v) := by
  letI := infiniteCompletionNontriviallyNormedField v
  rw [← Set.range_eq_univ]
  have hc : IsClosed (Set.range (comparison (E := E) v)) := by
    change IsClosed ((comparison (E := E) v).toLinearMap.range : Set (Product (E := E) v))
    exact (comparison v).toLinearMap.range.closed_of_finiteDimensional
  exact hc.closure_eq.symm.trans (comparison_denseRange (E := E) v).closure_range

/-- The actual infinite fiber has the same indices as the places-over set
in mathlib's independent degree-sum theorem. -/
def fiberEquiv (v : InfinitePlace K) :
    InfinitePlacesAbove (E := E) v ≃ v.placesOver E where
  toFun w := ⟨w.1, inferInstanceAs (w.1.1.LiesOver v.1)⟩
  invFun w := by
    letI : w.1.1.LiesOver v.1 := w.2
    exact ⟨w.1, InfinitePlace.LiesOver.comap_eq w.1 v⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The sum of the actual completed extension degrees equals the global degree. -/
theorem local_degrees_eq (v : InfinitePlace K) :
    (∑ w : InfinitePlacesAbove (E := E) v,
      Module.finrank v.Completion w.1.Completion) = Module.finrank K E := by
  classical
  have hf : (∑ w : InfinitePlacesAbove (E := E) v,
      Module.finrank v.Completion w.1.Completion) =
      ∑ w : v.placesOver E, v.inertiaDeg w.1 := by
    apply Fintype.sum_equiv (fiberEquiv (E := E) v)
    intro w
    exact (InfinitePlace.inertiaDeg_eq_finrank v w.1).symm
  rw [hf]
  calc
    _ = ∑ w ∈ (v.placesOver E).toFinset, v.inertiaDeg w :=
      (Finset.sum_toFinset_eq_subtype (fun w ↦ w ∈ v.placesOver E)
        (fun w ↦ v.inertiaDeg w)).symm
    _ = _ := InfinitePlace.sum_inertiaDeg_eq_finrank K E v

/-- Independent degree equality upgrades surjectivity to an actual algebra equivalence. -/
def equiv (v : InfinitePlace K) :
    (v.Completion ⊗[K] E) ≃ₐ[v.Completion] Product (E := E) v := by
  have hd : Module.finrank v.Completion (v.Completion ⊗[K] E) =
      Module.finrank v.Completion (Product (E := E) v) := by
    simp only [Product, Module.finrank_baseChange, Module.finrank_pi_fintype, local_degrees_eq]
  exact AlgEquiv.ofBijective (comparison v)
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := (comparison (E := E) v).toLinearMap) hd).mpr
      (comparison_surjective v), comparison_surjective v⟩

/-- The norm on all infinite factors is the scalar-extended determinant norm. -/
theorem norm_comparison (v : InfinitePlace K) (y : v.Completion ⊗[K] E) :
    (∏ w : InfinitePlacesAbove (E := E) v,
      Algebra.norm v.Completion (comparison v y w)) = Algebra.norm v.Completion y := by
  rw [← ProductNorm.norm_pi]
  simpa only [equiv, AlgEquiv.ofBijective_apply] using Algebra.norm_eq_of_algEquiv (equiv v) y

/-- Products of actual completed norms agree with the global norm on global elements,
at every infinite place, without a Hasse, split, or degree-sum assumption. -/
theorem norm_global (v : InfinitePlace K) (x : E) :
    (∏ w : InfinitePlacesAbove (E := E) v,
      Algebra.norm v.Completion (algebraMap E w.1.Completion x)) =
        algebraMap K v.Completion (Algebra.norm K x) := by
  have h := norm_comparison v ((1 : v.Completion) ⊗ₜ[K] x)
  simpa only [comparison_tmul, map_one, one_mul, ScalarExtensionNorm.norm_one_tmul] using h

end NormEuclidean.InfiniteCompletedNorm
