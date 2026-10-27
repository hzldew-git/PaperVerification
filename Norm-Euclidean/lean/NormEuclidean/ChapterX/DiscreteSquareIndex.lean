import NormEuclidean.ChapterX.SquareIndex

/-!
# Splitting off valuation parity from square indices

A surjective integer-valued order contributes one factor of two to the
square index. The remaining factor is precisely the square index in its
unit kernel. No finite generation of the full local field group is used.
-/

noncomputable section

namespace NormEuclidean.DiscreteSquareIndex

open SquareIndex

/-- Valuation parity contributes one factor of two to the full square index. -/
theorem doubles_index (M : Type*) [AddCommGroup M] (f : M →+ ℤ)
    (hf : Function.Surjective f) :
    (doubles M).index = 2 * (doubles f.ker).index := by
  let S := doubles M
  let U := f.ker
  have hmap : S.map f = doubles ℤ := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨f x, (map_nsmul f 2 x).symm⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, hx⟩ := hf y
      refine ⟨2 • x, ⟨x, rfl⟩, ?_⟩
      change f (2 • x) = 2 • y
      rw [map_nsmul, hx]
  have hindex : (U ⊔ S).index = 2 := by
    have h := AddSubgroup.index_comap_of_surjective (H := doubles ℤ) hf
    rw [← hmap, AddSubgroup.comap_map_eq, sup_comm] at h
    rw [hmap] at h
    exact h.trans (by rw [doubles_index_free ℤ]; norm_num)
  have hker : S.comap U.subtype = doubles U := by
    ext y
    constructor
    · rintro ⟨x, hx⟩
      have h2 : (2 : ℕ) • f x = 0 := by
        rw [← map_nsmul]
        change f ((nsmulAddMonoidHom 2) x) = 0
        rw [hx]
        exact y.property
      have hfx : f x = 0 := by rw [two_nsmul] at h2; omega
      refine ⟨⟨x, hfx⟩, ?_⟩
      exact Subtype.ext hx
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, rfl⟩
  have hrel := AddSubgroup.index_comap S U.subtype
  rw [hker, AddSubgroup.range_subtype] at hrel
  have h := AddSubgroup.relIndex_mul_index (show S ≤ U ⊔ S from le_sup_right)
  rw [hindex, AddSubgroup.relIndex_sup_right, ← hrel] at h
  exact h.symm.trans (mul_comm _ _)

end NormEuclidean.DiscreteSquareIndex
