import NormEuclidean.ChapterX.SquareIndex
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Bases of finite square-class groups with one prescribed class

The quotient by doubles is a vector space over the field with two
elements. A prescribed nonzero class extends to a basis. Lifting the
basis yields the independent finite family and its coordinate tests
used by the prime-selection argument.
-/

noncomputable section

namespace NormEuclidean.SquareClassBasis

open SquareIndex

/-- Coordinates on the square-class quotient, with a prescribed first class. -/
theorem exists_coordinates (M : Type*) [AddCommGroup M] (s : ℕ)
    (hcard : (doubles M).index = 2 ^ s) (x : M) (hx : x ∉ doubles M) :
    ∃ (e : Fin s → M) (i₀ : Fin s) (c : Fin s → M →+ ZMod 2),
      e i₀ = x ∧ (∀ i j, c i (e j) = if i = j then 1 else 0) ∧
      ∀ i y, c i (2 • y) = 0 := by
  classical
  let V := M ⧸ doubles M
  letI : Finite V := Nat.finite_of_card_ne_zero (by
    change (doubles M).index ≠ 0
    rw [hcard]
    positivity)
  letI : Fintype V := Fintype.ofFinite V
  letI : Module (ZMod 2) V := QuotientAddGroup.zmodModule
    (fun y ↦ show 2 • y ∈ doubles M from ⟨y, rfl⟩)
  let q : M →+ V := QuotientAddGroup.mk' (doubles M)
  have hxq : q x ≠ 0 := fun h ↦ hx ((QuotientAddGroup.eq_zero_iff x).mp h)
  have hi : LinearIndepOn (ZMod 2) id {q x} :=
    (linearIndepOn_singleton_iff (ZMod 2)).mpr hxq
  let b := Module.Basis.extend hi
  let I := hi.extend (Set.subset_univ {q x})
  letI : Finite I := Module.Finite.finite_basis b
  letI : Fintype I := Fintype.ofFinite I
  have hs : Module.finrank (ZMod 2) V = s := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := V)
    have hc : Fintype.card V = 2 ^ s := by
      rw [← Nat.card_eq_fintype_card]
      exact hcard
    rw [hc, ZMod.card] at h
    exact (Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))) h.symm
  have hI : Fintype.card I = s := (Module.finrank_eq_card_basis b).symm.trans hs
  let reindex := Fintype.equivFinOfCardEq hI
  let B : Module.Basis (Fin s) (ZMod 2) V := b.reindex reindex
  let iX : I := ⟨q x, hi.subset_extend (Set.subset_univ _) (by simp)⟩
  let i₀ := reindex iX
  have hbX : B i₀ = q x := by simp [B, i₀, b, iX]
  have hsur : Function.Surjective q := QuotientAddGroup.mk'_surjective _
  let e (i : Fin s) : M := if i = i₀ then x else Classical.choose (hsur (B i))
  have he (i : Fin s) : q (e i) = B i := by
    dsimp only [e]
    split_ifs with h
    · subst i
      exact hbX.symm
    · exact Classical.choose_spec (hsur (B i))
  let c (i : Fin s) : M →+ ZMod 2 := (B.coord i).toAddMonoidHom.comp q
  refine ⟨e, i₀, c, by simp [e], ?_, ?_⟩
  · intro i j
    change B.repr (q (e j)) i = _
    rw [he]
    simp [Finsupp.single_apply, eq_comm]
  · intro i y
    rw [map_nsmul]
    exact (show ∀ z : ZMod 2, (2 : ℕ) • z = 0 by decide) _

end NormEuclidean.SquareClassBasis
