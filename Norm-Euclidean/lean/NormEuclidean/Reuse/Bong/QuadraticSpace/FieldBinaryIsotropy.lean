/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.DiagonalTernaryCore
import Mathlib.Tactic

/-!
# Binary isotropy over an arbitrary field

This file isolates the determinant-square criterion for a regular binary
diagonal quadratic space.  The result is field algebra and requires no
valuation, topology, or dyadic local-field structure.
-/

namespace Bong

universe u

variable {F : Type u} [Field F]

/-- A regular binary diagonal form is isotropic exactly when the negative
product of its two coefficients is a square. -/
theorem fieldBinary_isotropic_iff_isSquare_neg_product
    (a : Fin 2 → F) (ha : ∀ i, a i ≠ 0) :
    DiagonalIsotropic a ↔ IsSquare (-(a 0 * a 1)) := by
  constructor
  · rintro ⟨x, hxne, hquadratic⟩
    have hvalue :
        a 0 * (x 0) ^ 2 + a 1 * (x 1) ^ 2 = 0 := by
      simpa [diagonalQuadratic, Fin.sum_univ_two] using hquadratic
    have hxzero : x 0 ≠ 0 := by
      intro hxzero
      have hxone : x 1 = 0 := by
        have hb : a 1 * (x 1) ^ 2 = 0 := by
          simpa [hxzero] using hvalue
        exact (sq_eq_zero_iff).mp
          (mul_eq_zero.mp hb |>.resolve_left (ha 1))
      apply hxne
      funext i
      fin_cases i
      · exact hxzero
      · exact hxone
    have hxone : x 1 ≠ 0 := by
      intro hxone
      have hxzero' : x 0 = 0 := by
        have ha0 : a 0 * (x 0) ^ 2 = 0 := by
          simpa [hxone] using hvalue
        exact (sq_eq_zero_iff).mp
          (mul_eq_zero.mp ha0 |>.resolve_left (ha 0))
      exact hxzero hxzero'
    refine ⟨a 0 * x 0 / x 1, ?_⟩
    field_simp [hxone]
    linear_combination -a 0 * hvalue
  · rintro ⟨s, hs⟩
    let x : Fin 2 → F := ![s / a 0, 1]
    refine ⟨x, ?_, ?_⟩
    · intro hx
      have hone := congrFun hx (1 : Fin 2)
      simp [x] at hone
    · have hs' : -(a 0 * a 1) = s ^ 2 := by
        simpa [pow_two] using hs
      simp only [x, diagonalQuadratic, Fin.sum_univ_two]
      simp
      field_simp [ha 0]
      rw [← hs']
      ring

end Bong
