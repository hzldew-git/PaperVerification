/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.QuadraticSpace.ScalarExtension
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Scalar extension through a field tower

This file proves that extending a finite-dimensional quadratic space first
from `F` to `E` and then from `E` to `L` agrees isometrically with extending
directly from `F` to `L`.
-/

namespace Bong

open scoped TensorProduct

namespace QuadraticSpace

universe u

/-- Successive scalar extension through a field tower is isometric to direct
scalar extension. -/
noncomputable def scalarExtensionTowerIsometry
    {F E L V : Type u} [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra E L] [Algebra F L]
    [IsScalarTower F E L]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (q : QuadraticSpace F V) :
    Isometry
      ((q.scalarExtension (E := E)).scalarExtension (E := L))
      (q.scalarExtension (E := L)) where
  toLinearEquiv :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange F E L L V
  map_bilin := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul b v =>
            induction y using TensorProduct.induction_on with
            | zero => simp
            | tmul c y =>
                induction y using TensorProduct.induction_on with
                | zero => simp
                | tmul d w =>
                    simp [scalarExtension_bilin_tmul, Algebra.smul_def]
                    rw [IsScalarTower.algebraMap_apply F E L]
                    ring
                | add y z hy hz =>
                    simp only [TensorProduct.tmul_add, map_add, hy, hz]
            | add y z hy hz => simp only [map_add, hy, hz]
        | add x z hx hz =>
            simp only [TensorProduct.tmul_add, map_add,
              LinearMap.add_apply, hx, hz]
    | add x z hx hz =>
        simp only [map_add, LinearMap.add_apply, hx, hz]

end QuadraticSpace

end Bong
