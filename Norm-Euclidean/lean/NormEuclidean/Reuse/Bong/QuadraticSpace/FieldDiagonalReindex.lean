/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.QuadraticSpace.FieldDiagonalization

namespace Bong.QuadraticSpace

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Reindexing all coordinates of a finite diagonal quadratic space gives an
isometric finite diagonal space. -/
noncomputable def finiteDiagonalReindexIsometry
    {m n : Nat} (a : Fin m → K) (ha : ∀ i, a i ≠ 0)
    (e : Fin n ≃ Fin m) :
    Isometry (finiteDiagonal a ha)
      (finiteDiagonal (fun i ↦ a (e i)) (fun i ↦ ha (e i))) where
  toLinearEquiv :=
    (LinearEquiv.piCongrLeft K (fun _ : Fin m ↦ K) e).symm
  map_bilin := by
    intro x y
    rw [finiteDiagonal_bilin_apply, finiteDiagonal_bilin_apply]
    let E := LinearEquiv.piCongrLeft K (fun _ : Fin m ↦ K) e
    have hx (i : Fin n) : E.symm x i = x (e i) := by
      have hfun : E.symm x = fun j ↦ x (e j) := by
        apply E.injective
        change E (E.symm x) = E (fun j ↦ x (e j))
        rw [E.apply_symm_apply]
        funext j
        change x j =
          (Equiv.piCongrLeft (fun _ : Fin m ↦ K) e)
            (fun k ↦ x (e k)) j
        simpa using (Equiv.piCongrLeft_apply_apply
          (fun _ : Fin m ↦ K) e (fun k ↦ x (e k)) (e.symm j)).symm
      exact congrFun hfun i
    have hy (i : Fin n) : E.symm y i = y (e i) := by
      have hfun : E.symm y = fun j ↦ y (e j) := by
        apply E.injective
        change E (E.symm y) = E (fun j ↦ y (e j))
        rw [E.apply_symm_apply]
        funext j
        change y j =
          (Equiv.piCongrLeft (fun _ : Fin m ↦ K) e)
            (fun k ↦ y (e k)) j
        simpa using (Equiv.piCongrLeft_apply_apply
          (fun _ : Fin m ↦ K) e (fun k ↦ y (e k)) (e.symm j)).symm
      exact congrFun hfun i
    calc
      (∑ i, a (e i) * E.symm x i * E.symm y i) =
          ∑ i, a (e i) * x (e i) * y (e i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hx i, hy i]
      _ = ∑ i, a i * x i * y i :=
        Equiv.sum_comp e (fun i ↦ a i * x i * y i)

end Bong.QuadraticSpace
