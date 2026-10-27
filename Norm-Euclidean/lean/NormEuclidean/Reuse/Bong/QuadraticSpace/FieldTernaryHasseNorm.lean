/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import NormEuclidean.Reuse.Bong.QuadraticSpace.FieldBinaryIsotropy
import Bong.Dyadic.HilbertSymbol
import Mathlib.Tactic

/-!
# Ternary isotropy and quadratic norm equations

This file gives the field-algebra bridge used in the ternary step of
O'Meara 66:1.  For a regular diagonal ternary form, isotropy is equivalent
to solvability of the associated quadratic norm equation.
-/

namespace Bong

open Dyadic

universe u

variable {F : Type u} [Field F] [CharZero F]

/-- The coefficient of the quadratic extension attached to a regular
diagonal ternary form. -/
def fieldTernaryNormTheta (a : Fin 3 → Fˣ) : Fˣ :=
  -(a 2) / a 1

/-- The scalar whose norm detects isotropy of a regular diagonal ternary
form. -/
def fieldTernaryNormAlpha (a : Fin 3 → Fˣ) : Fˣ :=
  -(a 0) / a 1

/-- A regular diagonal ternary form is isotropic exactly when its associated
quadratic norm equation is solvable. -/
theorem fieldTernary_isotropic_iff_isQuadraticNorm
    (a : Fin 3 → Fˣ) :
    DiagonalIsotropic (fun i ↦ (a i : F)) ↔
      IsQuadraticNorm F (fieldTernaryNormTheta a)
        (fieldTernaryNormAlpha a) := by
  constructor
  · rintro ⟨z, hz, hquadratic⟩
    have hvalue :
        (a 0 : F) * (z 0) ^ 2 +
            (a 1 : F) * (z 1) ^ 2 +
            (a 2 : F) * (z 2) ^ 2 = 0 := by
      simpa [diagonalQuadratic, Fin.sum_univ_three] using hquadratic
    by_cases htheta : IsSquare (fieldTernaryNormTheta a)
    · exact isQuadraticNorm_of_isSquare_left F htheta
    · have hzzero : z 0 ≠ 0 := by
        intro hzzero
        have htail :
            (a 1 : F) * (z 1) ^ 2 + (a 2 : F) * (z 2) ^ 2 = 0 := by
          simpa [hzzero] using hvalue
        have hztwo : z 2 ≠ 0 := by
          intro hztwo
          have hzone : z 1 = 0 := by
            have h : (a 1 : F) * (z 1) ^ 2 = 0 := by
              simpa [hztwo, hzzero] using hvalue
            exact (sq_eq_zero_iff).mp
              (mul_eq_zero.mp h |>.resolve_left (Units.ne_zero (a 1)))
          apply hz
          funext i
          fin_cases i
          · exact hzzero
          · exact hzone
          · exact hztwo
        apply htheta
        let s : Fˣ := Units.mk0 (z 1 / z 2) (div_ne_zero (by
          intro hzone
          have h : (a 2 : F) * (z 2) ^ 2 = 0 := by
            simpa [hzone, hzzero] using hvalue
          exact hztwo ((sq_eq_zero_iff).mp
            (mul_eq_zero.mp h |>.resolve_left (Units.ne_zero (a 2))))) hztwo)
        refine ⟨s, ?_⟩
        apply Units.ext
        simp only [fieldTernaryNormTheta, s, Units.val_neg,
          Units.val_div_eq_div_val, Units.val_mul, Units.val_mk0]
        field_simp [hztwo, Units.ne_zero (a 1)]
        linear_combination -htail
      refine ⟨z 1 / z 0, z 2 / z 0, ?_⟩
      simp only [fieldTernaryNormTheta, fieldTernaryNormAlpha,
        Units.val_div_eq_div_val, Units.val_neg]
      field_simp [hzzero, Units.ne_zero (a 1)]
      linear_combination hvalue
  · rintro ⟨x, y, hnorm⟩
    let z : Fin 3 → F := ![1, x, y]
    refine ⟨z, ?_, ?_⟩
    · intro hz
      have hone := congrFun hz (0 : Fin 3)
      simp [z] at hone
    · simp only [fieldTernaryNormTheta, fieldTernaryNormAlpha,
        Units.val_div_eq_div_val, Units.val_neg] at hnorm
      simp only [z, diagonalQuadratic, Fin.sum_univ_three]
      simp
      field_simp [Units.ne_zero (a 1)] at hnorm
      linear_combination hnorm

end Bong
