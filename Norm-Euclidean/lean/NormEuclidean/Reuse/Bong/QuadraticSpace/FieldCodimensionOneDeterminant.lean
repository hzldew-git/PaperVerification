/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.QuadraticSpace.FieldDiagonalization
import NormEuclidean.Reuse.Bong.QuadraticSpace.FieldDiagonalReindex
import NormEuclidean.Reuse.Bong.QuadraticSpace.FieldRepresentationComplement

/-!
# Field diagonal units and one-dimensional models

This extraction retains the diagonal units and scaled-line isometry used
by the Hasse proof. The later codimension-one cancellation theorem and
its lattice dependencies are outside this extraction.
-/

namespace Bong.QuadraticSpace

universe u v w

variable {K : Type u} [Field K] [CharZero K]
  {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- Nonzero field-diagonal coefficients as units. -/
noncomputable def fieldDiagonalUnits (q : QuadraticSpace K V) :
    Fin (Module.finrank K V) → Kˣ :=
  fun i ↦ Units.mk0 (q.fieldDiagonalCoefficients i)
    (q.fieldDiagonalCoefficients_ne_zero i)

/-- The one-coordinate diagonal model is a scaled line. -/
noncomputable def fieldFiniteDiagonalLineIsometry (a : Kˣ) :
    Isometry
      (finiteDiagonal (fun _ : Fin 1 ↦ (a : K))
        (by intro; exact Units.ne_zero a))
      (scaledLine a) where
  toLinearEquiv := {
    toFun := fun z ↦ z 0
    invFun := fun z _ ↦ z
    left_inv := by intro z; funext i; fin_cases i; rfl
    right_inv := by intro z; rfl
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  map_bilin := by
    intro x y
    rw [scaledLine_bilin_apply, finiteDiagonal_bilin_apply]
    simp

/-- A nondegenerate one-dimensional space is a scaled line. -/
theorem exists_field_rankOne_scaledLine
    (q : QuadraticSpace K V) (hrank : Module.finrank K V = 1) :
    ∃ a : Kˣ, q.IsIsometric (scaledLine a) := by
  let e : Fin 1 ≃ Fin (Module.finrank K V) := finCongr hrank.symm
  let a : Kˣ := Units.mk0 (q.fieldDiagonalCoefficients (e 0))
    (q.fieldDiagonalCoefficients_ne_zero (e 0))
  have hcoeff : (fun i : Fin 1 ↦ q.fieldDiagonalCoefficients (e i)) =
      (fun _ ↦ (a : K)) := by
    funext i
    fin_cases i
    rfl
  let reindex := finiteDiagonalReindexIsometry
    q.fieldDiagonalCoefficients q.fieldDiagonalCoefficients_ne_zero e
  refine ⟨a, ⟨q.fieldDiagonalizationIsometry.trans (reindex.trans ?_)⟩⟩
  simpa only [hcoeff] using fieldFiniteDiagonalLineIsometry a

end Bong.QuadraticSpace
