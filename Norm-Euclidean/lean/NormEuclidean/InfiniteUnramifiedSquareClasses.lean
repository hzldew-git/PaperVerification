import NormEuclidean.ChapterX.CompletedNormImages

/-!
# Square parameters at actual unramified infinite places

An unramified infinite extension completion has local degree one. The
quadratic generator therefore descends to the base completion, proving
the square condition used by the ordinary idele class correction.
-/

noncomputable section

namespace NormEuclidean.InfiniteUnramifiedSquareClasses

open ExtensionIdeleNorm QuadraticExtensionNorm
open scoped NumberField NumberField.LiesOver NormEuclidean.ExtensionPlaces
  NormEuclidean.InfiniteCompletedNorm QuadraticAlgebra

/-- A square root in an extension of local degree one descends to the base field. -/
theorem isSquare_of_local_degree_one {F B : Type*} [Field F] [Field B] [Algebra F B]
    (hdegree : Module.finrank F B = 1) (a : Fˣ) (x : B)
    (hx : x ^ 2 = algebraMap F B (a : F)) : IsSquare a := by
  obtain ⟨r, hr⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hdegree).2 x
  have hr2 : r ^ 2 = (a : F) := (algebraMap F B).injective (by rw [map_pow, hr, hx])
  have hr0 : r ≠ 0 := by
    intro hzero
    exact a.ne_zero (by simpa only [hzero, zero_pow (by decide : 2 ≠ 0)] using hr2.symm)
  refine ⟨Units.mk0 r hr0, ?_⟩
  apply Units.ext
  simpa only [Units.val_mul, Units.val_mk0, pow_two] using hr2.symm

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- One actual unramified infinite extension place forces the local parameter to be square. -/
theorem quadratic_isSquare_at (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (v : NumberField.InfinitePlace K) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    ∀ (w : InfinitePlacesAbove (E := QuadraticAlgebra K (theta : K) 0) v),
      w.1.IsUnramified K →
        IsSquare (Units.map (algebraMap K v.Completion).toMonoidHom theta) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  intro w hw
  apply isSquare_of_local_degree_one
    (NumberField.InfinitePlace.Completion.finrank_eq_one_of_isUnramified v hw)
    _ (algebraMap (QuadraticAlgebra K (theta : K) 0) w.1.Completion ω)
  change (algebraMap _ _ ω) ^ 2 =
    algebraMap v.Completion w.1.Completion
      (algebraMap K v.Completion (theta : K))
  rw [← map_pow]
  have hmap := infinitePlaceAboveCompletionMap_global v w (theta : K)
  change algebraMap v.Completion w.1.Completion
      (algebraMap K v.Completion (theta : K)) =
    algebraMap (QuadraticAlgebra K (theta : K) 0) w.1.Completion
      (algebraMap K (QuadraticAlgebra K (theta : K) 0) (theta : K)) at hmap
  rw [hmap]
  congr 1
  ext <;> simp [pow_two]

/-- Unramifiedness above every infinite base place supplies every infinite square condition. -/
theorem quadratic_isSquare (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (hunram : letI := quadraticExtensionField theta htheta
      letI := quadraticExtensionNumberField theta htheta
      ∀ (v : NumberField.InfinitePlace K)
        (w : InfinitePlacesAbove (E := QuadraticAlgebra K (theta : K) 0) v),
          w.1.IsUnramified K) :
    ∀ v : NumberField.InfinitePlace K,
      IsSquare (Units.map (algebraMap K v.Completion).toMonoidHom theta) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  intro v
  obtain ⟨w, hw⟩ := NumberField.InfinitePlace.comap_surjective
    (K := QuadraticAlgebra K (theta : K) 0) v
  exact quadratic_isSquare_at theta htheta v ⟨w, hw⟩ (hunram v ⟨w, hw⟩)

end NormEuclidean.InfiniteUnramifiedSquareClasses
