import NormEuclidean.ChapterX.FieldSquareIndex
import Mathlib.GroupTheory.Index

/-!
# The square-index balance for norm and difference

The two exact kernels identify the same finite-index subgroup in two ways.
Taking indices reduces the norm index to square indices of the base group
and of the difference image, retaining the torsion contribution.
-/

noncomputable section

namespace NormEuclidean.NormSquareBalance

/-- Exact norm and difference kernels give an equality of square indices. -/
theorem square_balance {A G : Type*} [CommGroup A] [CommGroup G]
    (f : A →* G) (N : G →* A) (T : G →* G)
    (hfixed : f.range = T.ker) (h90 : T.range = N.ker)
    (hbase : ∀ a, N (f a) = a ^ 2)
    (hdiff : ∀ x, T (T x) = T x ^ 2) :
    N.range.index * (powMonoidHom (α := T.range) 2).range.index =
      (powMonoidHom (α := A) 2).range.index := by
  let P := f.range ⊔ T.range
  have hTf (a : A) : T (f a) = 1 := hfixed.le ⟨a, rfl⟩
  have hNT (x : G) : N (T x) = 1 := h90.le ⟨x, rfl⟩
  have hmap : P.map T.rangeRestrict = (powMonoidHom (α := T.range) 2).range := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := Subgroup.mem_sup.mp hy
      refine ⟨T.rangeRestrict b, ?_⟩
      apply Subtype.ext
      change T b ^ 2 = T (f a * T b)
      rw [map_mul, hTf, one_mul, hdiff]
    · rintro ⟨x, rfl⟩
      obtain ⟨b, hb⟩ := x.property
      refine ⟨T b, Subgroup.mem_sup_right ⟨b, rfl⟩, ?_⟩
      apply Subtype.ext
      change T (T b) = x.val ^ 2
      rw [hdiff, hb]
  have hcomap : (powMonoidHom (α := A) 2).range.comap N = P := by
    ext x
    constructor
    · rintro ⟨a, ha⟩
      have hy : x / f a ∈ T.range := by
        rw [h90]
        change N (x / f a) = 1
        rw [map_div, hbase, ← ha]
        simp only [powMonoidHom_apply, div_self']
      exact Subgroup.mem_sup.mpr ⟨f a, ⟨a, rfl⟩, x / f a, hy,
        by simp [div_eq_mul_inv, mul_left_comm]⟩
    · intro hx
      obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := Subgroup.mem_sup.mp hx
      refine ⟨a, ?_⟩
      change a ^ 2 = N (f a * T b)
      rw [map_mul, hbase, hNT, mul_one]
  have hP : P.index = (powMonoidHom (α := T.range) 2).range.index := by
    rw [← hmap]
    exact (Subgroup.index_map_eq P T.rangeRestrict_surjective (by
      intro x hx
      have hh : x ∈ T.ker := congrArg Subtype.val hx
      exact Subgroup.mem_sup_left (hfixed.ge hh))).symm
  have hle : (powMonoidHom (α := A) 2).range ≤ N.range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨f a, hbase a⟩
  have hidx := Subgroup.index_comap (powMonoidHom (α := A) 2).range N
  rw [hcomap, hP] at hidx
  rw [hidx, mul_comm]
  exact Subgroup.relIndex_mul_index hle

end NormEuclidean.NormSquareBalance
