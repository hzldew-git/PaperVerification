import NormEuclidean.ChapterX.HerbrandIndex
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite

/-!
# Square indices with their torsion contribution

The free part contributes a power of two; the finite torsion part
contributes the cardinality of its two-torsion. These contributions must
both be kept in the numerical S-unit norm-index argument.
-/

noncomputable section

namespace NormEuclidean.SquareIndex

/-- The doubled lattice has quotient cardinality two to its rank. -/
theorem doubled_free_card (M : Type*) [AddCommGroup M]
    [Module.Free ℤ M] [Module.Finite ℤ M] :
    Nat.card (M ⧸ (LinearMap.lsmul ℤ M (2 : ℤ)).range) =
      2 ^ Module.finrank ℤ M := by
  let f := LinearMap.lsmul ℤ M (2 : ℤ)
  have hf : Function.Injective f := LinearMap.lsmul_injective (by norm_num : (2 : ℤ) ≠ 0)
  let e := LinearEquiv.ofInjective f hf
  have h := Submodule.natAbs_det_equiv f.range e
  change (LinearMap.det f).natAbs = Nat.card (M ⧸ f.range) at h
  have heq : f = (2 : ℤ) • (LinearMap.id : M →ₗ[ℤ] M) := by ext x; rfl
  rw [heq, LinearMap.det_smul, LinearMap.det_id, mul_one, Int.natAbs_pow] at h
  rw [← heq] at h
  simpa only [show Int.natAbs (2 : ℤ) = 2 from rfl] using h.symm

/-- The additive subgroup of doubles. -/
def doubles (M : Type*) [AddCommGroup M] : AddSubgroup M :=
  (nsmulAddMonoidHom (α := M) 2).range

/-- The additive two-torsion subgroup. -/
def twoTorsion (M : Type*) [AddCommGroup M] : AddSubgroup M :=
  (nsmulAddMonoidHom (α := M) 2).ker

/-- The free contribution to the square index. -/
theorem doubles_index_free (M : Type*) [AddCommGroup M]
    [Module.Free ℤ M] [Module.Finite ℤ M] :
    (doubles M).index = 2 ^ Module.finrank ℤ M := by
  have heq : (LinearMap.lsmul ℤ M (2 : ℤ)).range.toAddSubgroup = doubles M := by
    ext x
    change (∃ y, (2 : ℤ) • y = x) ↔ ∃ y, (2 : ℕ) • y = x
    simp only [two_zsmul, two_nsmul]
  change Nat.card (M ⧸ doubles M) = _
  rw [← heq]
  exact doubled_free_card M

/-- On a finite abelian group, an endomorphism's cokernel and kernel
have the same cardinality. -/
theorem finite_end_index (M : Type*) [AddCommGroup M] [Finite M] (f : M →+ M) :
    f.range.index = Nat.card f.ker := by
  have hker := f.ker.card_mul_index
  rw [AddSubgroup.index_ker] at hker
  have hrange := f.range.index_mul_card
  exact mul_right_cancel₀ (show Nat.card f.range ≠ 0 from Nat.card_pos.ne')
    (hrange.trans hker.symm)

/-- The finite torsion contribution to the square index. -/
theorem doubles_index_finite (M : Type*) [AddCommGroup M] [Finite M] :
    (doubles M).index = Nat.card (twoTorsion M) :=
  finite_end_index M _

/-- Doubles commute with a direct product. -/
theorem doubles_prod (M N : Type*) [AddCommGroup M] [AddCommGroup N] :
    doubles (M × N) = (doubles M).prod (doubles N) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨y.1, rfl⟩, ⟨y.2, rfl⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨(a, b), Prod.ext ha hb⟩

/-- Additive equivalence preserves the subgroup index of doubles. -/
theorem doubles_index_congr {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (e : M ≃+ N) : (doubles M).index = (doubles N).index := by
  have heq : (doubles M).map e.toAddMonoidHom = doubles N := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨e y, (map_nsmul e 2 y).symm⟩
    · rintro ⟨y, rfl⟩
      refine ⟨2 • e.symm y, ⟨e.symm y, rfl⟩, ?_⟩
      change e (2 • e.symm y) = 2 • y
      simp only [map_nsmul, e.apply_symm_apply]
  rw [← heq]
  exact ((doubles M).index_map_equiv e).symm

/-- Additive equivalence also preserves the two-torsion cardinality. -/
theorem twoTorsion_card_congr {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (e : M ≃+ N) : Nat.card (twoTorsion M) = Nat.card (twoTorsion N) := by
  let f : twoTorsion M ≃ twoTorsion N := {
    toFun x := ⟨e x.val, by
      change 2 • e x.val = 0
      rw [← map_nsmul, show 2 • x.val = 0 from x.property, map_zero]⟩
    invFun x := ⟨e.symm x.val, by
      change 2 • e.symm x.val = 0
      rw [← map_nsmul, show 2 • x.val = 0 from x.property, map_zero]⟩
    left_inv x := Subtype.ext (e.symm_apply_apply _)
    right_inv x := Subtype.ext (e.apply_symm_apply _) }
  exact Nat.card_congr f

end NormEuclidean.SquareIndex
