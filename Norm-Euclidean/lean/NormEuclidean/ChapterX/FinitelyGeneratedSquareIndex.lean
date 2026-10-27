import NormEuclidean.ChapterX.SquareIndex
import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# The square index of a finitely generated abelian group

The structure theorem separates a finite group from a free abelian group.
The square index is two to the free rank times the two-torsion cardinality.
-/

noncomputable section

namespace NormEuclidean.FinitelyGeneratedSquareIndex

open SquareIndex
open scoped DirectSum

/-- A finite additive group has integer rank zero. -/
theorem finite_finrank_zero (M : Type*) [AddCommGroup M] [Finite M] :
    Module.finrank ℤ M = 0 := by
  letI : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.mpr inferInstance
  apply Module.finrank_eq_zero_iff_isTorsion.mpr
  intro x
  refine ⟨⟨(Nat.card M : ℤ), mem_nonZeroDivisors_of_ne_zero
    (Int.natCast_ne_zero.mpr Nat.card_pos.ne')⟩, ?_⟩
  exact (natCast_zsmul _ _).trans (card_nsmul_eq_zero' (x := x))

/-- Two-torsion commutes with products, including its cardinality. -/
theorem twoTorsion_card_prod (M N : Type*) [AddCommGroup M] [AddCommGroup N] :
    Nat.card (twoTorsion (M × N)) = Nat.card (twoTorsion M) * Nat.card (twoTorsion N) := by
  have heq : twoTorsion (M × N) = (twoTorsion M).prod (twoTorsion N) := by
    ext x
    change (2 • x = 0) ↔ 2 • x.1 = 0 ∧ 2 • x.2 = 0
    exact Prod.ext_iff
  rw [heq]
  exact (Nat.card_congr ((twoTorsion M).prodEquiv (twoTorsion N)).toEquiv).trans
    (Nat.card_prod _ _)

/-- A free integer module has no nonzero two-torsion. -/
theorem twoTorsion_card_free (M : Type*) [AddCommGroup M] [Module.Free ℤ M] :
    Nat.card (twoTorsion M) = 1 := by
  have hz (x : twoTorsion M) : x.val = 0 := by
    have hi : Function.Injective (LinearMap.lsmul ℤ M (2 : ℤ)) :=
      LinearMap.lsmul_injective (by norm_num : (2 : ℤ) ≠ 0)
    apply hi
    change (2 : ℤ) • x.val = (2 : ℤ) • (0 : M)
    simpa only [two_zsmul, two_nsmul, smul_zero] using
      (show (2 : ℕ) • x.val = 0 from x.property)
  let e : twoTorsion M ≃ PUnit.{1} := {
    toFun := fun _ ↦ PUnit.unit
    invFun := fun _ ↦ 0
    left_inv := fun x ↦ Subtype.ext (hz x).symm
    right_inv := fun x ↦ Subsingleton.elim _ _ }
  exact (Nat.card_congr e).trans (by simp)

/-- The full square-index formula, including the two-torsion factor. -/
theorem doubles_index (M : Type*) [AddCommGroup M] [Module.Finite ℤ M] :
    (doubles M).index = 2 ^ Module.finrank ℤ M * Nat.card (twoTorsion M) := by
  classical
  letI : AddGroup.FG M := Module.Finite.iff_addGroup_fg.mp inferInstance
  obtain ⟨n, ι, hι, p, hp, k, ⟨e⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod M
  letI := hι
  letI (i : ι) : NeZero (p i ^ k i) := ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let L := Fin n →₀ ℤ
  let T := ⨁ i : ι, ZMod (p i ^ k i)
  letI : Finite T := Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  letI : Module.Finite ℤ T := Module.Finite.iff_addGroup_fg.mpr inferInstance
  have hr : Module.finrank ℤ M = Module.finrank ℤ L := by
    have h := e.toIntLinearEquiv.finrank_eq
    let f := LinearMap.fst ℤ L T
    let ek : f.ker ≃ T := {
      toFun := fun x ↦ x.val.2
      invFun := fun x ↦ ⟨(0, x), rfl⟩
      left_inv := fun x ↦ Subtype.ext (Prod.ext x.property.symm rfl)
      right_inv := fun _ ↦ rfl }
    letI : Finite f.ker := Finite.of_equiv T ek.symm
    have hh := f.ker.finrank_quotient_add_finrank
    rw [finite_finrank_zero f.ker, add_zero] at hh
    have hs : Function.Surjective f := fun x ↦ ⟨(x, 0), rfl⟩
    exact h.trans (hh.symm.trans (f.quotKerEquivOfSurjective hs).finrank_eq)
  have ht : Nat.card (twoTorsion M) = Nat.card (twoTorsion T) := by
    rw [twoTorsion_card_congr e, twoTorsion_card_prod,
      twoTorsion_card_free L, one_mul]
  rw [doubles_index_congr e, doubles_prod, AddSubgroup.index_prod,
    doubles_index_free L, doubles_index_finite T, hr, ht]

end NormEuclidean.FinitelyGeneratedSquareIndex
