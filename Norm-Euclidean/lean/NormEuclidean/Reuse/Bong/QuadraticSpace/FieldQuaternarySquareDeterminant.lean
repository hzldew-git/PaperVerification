/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import NormEuclidean.Reuse.Bong.QuadraticSpace.FieldTernaryHasseNorm
import Mathlib.Tactic

/-!
# Quaternary isotropy with square determinant

This file proves the field-algebra step O'Meara 42:12 in diagonal
coordinates. A regular quaternary diagonal form whose determinant class is
square is isotropic exactly when its leading ternary subform is isotropic.
-/
namespace Bong

open Dyadic

universe u
variable {F : Type u} [Field F]

def fieldQuaternaryPrefix (a : Fin 4 → Fˣ) : Fin 3 → Fˣ :=
  ![a 0, a 1, a 2]

@[simp] theorem fieldQuaternaryPrefix_zero (a : Fin 4 → Fˣ) :
    fieldQuaternaryPrefix a 0 = a 0 := rfl

@[simp] theorem fieldQuaternaryPrefix_one (a : Fin 4 → Fˣ) :
    fieldQuaternaryPrefix a 1 = a 1 := rfl

@[simp] theorem fieldQuaternaryPrefix_two (a : Fin 4 → Fˣ) :
    fieldQuaternaryPrefix a 2 = a 2 := by
  rfl

private theorem exists_fieldQuaternary_norm_scale
    (a : Fin 4 → Fˣ) (hdet : IsSquare (∏ i, a i)) :
    ∃ s : Fˣ, a 3 / a 1 =
      fieldTernaryNormAlpha (fieldQuaternaryPrefix a) *
        fieldTernaryNormTheta (fieldQuaternaryPrefix a) * (s * s) := by
  rcases hdet with ⟨c, hc⟩
  let s : Fˣ := c / (a 0 * a 2)
  refine ⟨s, ?_⟩
  have hc' : a 0 * a 1 * a 2 * a 3 = c * c := by
    simpa only [Fin.prod_univ_four] using hc
  have hcval :
      (a 0 : F) * (a 1 : F) * (a 2 : F) * (a 3 : F) =
        (c : F) * (c : F) := by
    exact congrArg (fun u : Fˣ ↦ (u : F)) hc'
  apply Units.ext
  norm_num [fieldTernaryNormAlpha, fieldTernaryNormTheta,
    s, Units.val_div_eq_div_val, Units.val_neg,
    Units.val_mul]
  field_simp [Units.ne_zero]
  linear_combination hcval

private theorem isSquare_of_quadraticNorm_eq_zero
    (theta : Fˣ) {x y : F}
    (hzero : x ^ 2 - (theta : F) * y ^ 2 = 0)
    (hnonzero : x ≠ 0 ∨ y ≠ 0) : IsSquare theta := by
  have hy : y ≠ 0 := by
    intro hy
    have hx : x = 0 := by
      apply (sq_eq_zero_iff).mp
      simpa [hy] using hzero
    exact hnonzero.elim (· hx) (· hy)
  have hx : x ≠ 0 := by
    intro hx
    have hy' : y = 0 := by
      have h : (theta : F) * y ^ 2 = 0 := by
        simpa [hx] using hzero
      exact (sq_eq_zero_iff).mp
        (mul_eq_zero.mp h |>.resolve_left (Units.ne_zero theta))
    exact hy hy'
  let s : Fˣ := Units.mk0 (x / y) (div_ne_zero hx hy)
  refine ⟨s, ?_⟩
  apply Units.ext
  simp only [s, Units.val_mk0, Units.val_mul]
  field_simp [hy]
  exact (sub_eq_zero.mp hzero).symm

/-- O'Meara 42:12 in diagonal coordinates: a regular quaternary form whose
coefficient product is a square is isotropic exactly when its leading
ternary subform is isotropic. -/
theorem fieldQuaternary_isotropic_iff_prefix_of_square_det
    [CharZero F] (a : Fin 4 → Fˣ) (hdet : IsSquare (∏ i, a i)) :
    DiagonalIsotropic (fun i ↦ (a i : F)) ↔
      DiagonalIsotropic
        (fun i ↦ (fieldQuaternaryPrefix a i : F)) := by
  constructor
  · rintro ⟨z, hz, hquadratic⟩
    have hvalue :
        (a 0 : F) * (z 0) ^ 2 +
            (a 1 : F) * (z 1) ^ 2 +
            (a 2 : F) * (z 2) ^ 2 +
            (a 3 : F) * (z 3) ^ 2 = 0 := by
      simpa [diagonalQuadratic, Fin.sum_univ_four] using hquadratic
    rcases exists_fieldQuaternary_norm_scale a hdet with ⟨s, hscale⟩
    let theta := fieldTernaryNormTheta (fieldQuaternaryPrefix a)
    let alpha := fieldTernaryNormAlpha (fieldQuaternaryPrefix a)
    let beta : F := (z 0) ^ 2 - (theta : F) * ((s : F) * z 3) ^ 2
    have hscaleval := congrArg (fun u : Fˣ ↦ (u : F)) hscale
    have hnormRelation :
        (z 1) ^ 2 - (theta : F) * (z 2) ^ 2 =
          (alpha : F) * beta := by
      simp only [theta, alpha, beta, fieldTernaryNormTheta,
        fieldTernaryNormAlpha, Units.val_div_eq_div_val, Units.val_neg,
        Units.val_mul, fieldQuaternaryPrefix_zero,
        fieldQuaternaryPrefix_one, fieldQuaternaryPrefix_two] at hscaleval ⊢
      field_simp [Units.ne_zero (a 1)] at hscaleval ⊢
      linear_combination (a 1 : F) * hvalue - (z 3) ^ 2 * hscaleval
    apply (fieldTernary_isotropic_iff_isQuadraticNorm
      (fieldQuaternaryPrefix a)).2
    by_cases hbeta : beta = 0
    · have hpairs :
          ((z 0 ≠ 0 ∨ (s : F) * z 3 ≠ 0) ∨
            (z 1 ≠ 0 ∨ z 2 ≠ 0)) := by
        by_cases hz0 : z 0 = 0
        · by_cases hz3 : z 3 = 0
          · by_cases hz1 : z 1 = 0
            · right
              right
              intro hz2
              apply hz
              funext i
              fin_cases i
              · exact hz0
              · exact hz1
              · exact hz2
              · exact hz3
            · exact Or.inr (Or.inl hz1)
          · exact Or.inl (Or.inr (mul_ne_zero (Units.ne_zero s) hz3))
        · exact Or.inl (Or.inl hz0)
      have htheta : IsSquare theta := by
        rcases hpairs with hfirst | hsecond
        · exact isSquare_of_quadraticNorm_eq_zero theta
            (by simpa [beta] using hbeta) hfirst
        · exact isSquare_of_quadraticNorm_eq_zero theta
            (by rw [hnormRelation, hbeta]; simp) hsecond
      exact isQuadraticNorm_of_isSquare_left F htheta
    · let betaUnit : Fˣ := Units.mk0 beta hbeta
      have hbetaNorm : IsQuadraticNorm F theta betaUnit := by
        refine ⟨z 0, (s : F) * z 3, ?_⟩
        exact rfl
      have halphaBetaNorm :
          IsQuadraticNorm F theta (alpha * betaUnit) := by
        refine ⟨z 1, z 2, ?_⟩
        simpa [betaUnit] using hnormRelation
      have hquotient := IsQuadraticNorm.mul F halphaBetaNorm
        (IsQuadraticNorm.inv F hbetaNorm)
      simpa [mul_assoc] using hquotient
  · rintro ⟨x, hx, hquadratic⟩
    let z : Fin 4 → F := ![x 0, x 1, x 2, 0]
    refine ⟨z, ?_, ?_⟩
    · intro hz
      apply hx
      funext i
      fin_cases i
      · exact congrFun hz 0
      · exact congrFun hz 1
      · exact congrFun hz 2
    · have hvalue :
          (a 0 : F) * (x 0) ^ 2 +
              (a 1 : F) * (x 1) ^ 2 +
              (a 2 : F) * (x 2) ^ 2 = 0 := by
        simpa [diagonalQuadratic, Fin.sum_univ_three] using hquadratic
      simpa [z, diagonalQuadratic, Fin.sum_univ_four] using hvalue

end Bong
