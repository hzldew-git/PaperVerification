import NormEuclidean.ChapterX.InfiniteNormIndices

/-!
# Square indices at infinite completions

The real square subgroup consists of positive units and has index two;
the complex square subgroup is the whole unit group. Both computations
are transported to the actual infinite number-field completions.
-/

noncomputable section

namespace NormEuclidean.InfiniteSquareIndex

open scoped NumberField

/-- A field equivalence preserves the square-subgroup index. -/
theorem index_congr {F E : Type*} [Field F] [Field E] (e : F ≃+* E) :
    (Subgroup.square Fˣ).index = (Subgroup.square Eˣ).index := by
  let f := Units.mapEquiv e.toMulEquiv
  have he : (Subgroup.square Eˣ).comap f.toMonoidHom = Subgroup.square Fˣ := by
    ext a
    constructor
    · intro h
      have hh := (show IsSquare (f a) from h).map f.symm.toMonoidHom
      change IsSquare (f.symm (f a)) at hh
      change IsSquare a
      simpa only [MulEquiv.symm_apply_apply] using hh
    · intro h
      exact (show IsSquare a from h).map f.toMonoidHom
  have h : ((Subgroup.square Eˣ).comap f.toMonoidHom).index =
      (Subgroup.square Eˣ).index :=
    Subgroup.index_comap_of_surjective (Subgroup.square Eˣ) f.surjective
  rwa [he] at h

/-- Real nonzero squares have index two among real units. -/
theorem real_index : (Subgroup.square ℝˣ).index = 2 := by
  apply Subgroup.index_eq_two_iff_exists_notMem_and.mpr
  refine ⟨-1, ?_, ?_⟩
  · rintro ⟨r, hr⟩
    have h := congrArg Units.val hr
    change (-1 : ℝ) = r.val * r.val at h
    nlinarith [sq_nonneg r.val]
  · intro a
    by_cases ha : 0 ≤ a.val
    · exact Or.inr (InfiniteNormIndices.real_isSquare_of_nonneg a ha)
    · left
      apply InfiniteNormIndices.real_isSquare_of_nonneg
      change 0 ≤ a.val * (-1 : ℝ)
      nlinarith

/-- Every nonzero complex scalar is a square. -/
theorem complex_index : (Subgroup.square ℂˣ).index = 1 := by
  apply Subgroup.index_eq_one.mpr
  apply top_unique
  intro a _
  exact InfiniteNormIndices.complex_isSquare a

variable {K : Type*} [Field K] [NumberField K]

/-- The square index at an actual infinite completion. -/
theorem index (v : NumberField.InfinitePlace K) :
    (Subgroup.square v.Completionˣ).index = (by
      classical
      exact if v.IsReal then 2 else 1) := by
  classical
  by_cases hv : v.IsReal
  · rw [if_pos hv, index_congr (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv)]
    exact real_index
  · rw [if_neg hv, index_congr
      (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
        ((v.isReal_or_isComplex).resolve_left hv))]
    exact complex_index

/-- The archimedean square index times the product-formula weight of two equals four. -/
theorem index_mul_two (v : NumberField.InfinitePlace K) :
    ((Subgroup.square v.Completionˣ).index : ℝ) * v (2 : K) ^ v.mult = 4 := by
  classical
  have hv2 : v (2 : K) = (2 : ℝ) := by simpa using v.map_natCast 2
  rw [index, hv2]
  by_cases hv : v.IsReal <;> norm_num [NumberField.InfinitePlace.mult, hv]

end NormEuclidean.InfiniteSquareIndex
