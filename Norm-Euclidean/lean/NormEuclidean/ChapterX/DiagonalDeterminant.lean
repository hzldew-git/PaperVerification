/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalTernaryCore
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.StdBasis

/-! Elementary determinant comparison, extracted without the dyadic BONG layer. -/

namespace Bong.DiagonalRepresents

universe u
variable {K : Type u} [Field K]

@[simp]
theorem diagonalQuadratic_basisFun {n : Nat} (c : Fin n → K) (i : Fin n) :
    diagonalQuadratic c (Pi.basisFun K (Fin n) i) = c i := by
  classical
  simp [diagonalQuadratic, Pi.basisFun_apply, Pi.single_apply]

theorem diagonalQuadratic_basisFun_add {n : Nat}
    (c : Fin n → K) (i j : Fin n) (hij : i ≠ j) :
    diagonalQuadratic c
        (Pi.basisFun K (Fin n) i + Pi.basisFun K (Fin n) j) =
      c i + c j := by
  classical
  let ei := Pi.basisFun K (Fin n) i
  let ej := Pi.basisFun K (Fin n) j
  have hcross : ∑ k, c k * ei k * ej k = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k = i
    · subst k
      simp [ei, ej, Pi.basisFun_apply, hij]
    · simp [ei, Pi.basisFun_apply, hki]
  change diagonalQuadratic c (ei + ej) = c i + c j
  calc
    diagonalQuadratic c (ei + ej) =
        diagonalQuadratic c ei + diagonalQuadratic c ej +
          2 * ∑ k, c k * ei k * ej k := by
      unfold diagonalQuadratic
      simp_rw [Pi.add_apply]
      rw [show (∑ k, c k * (ei k + ej k) ^ 2) =
          (∑ k, c k * ei k ^ 2) + (∑ k, c k * ej k ^ 2) +
            2 * ∑ k, c k * ei k * ej k by
        simp_rw [add_sq, mul_add]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        have hmiddle : (∑ x, c x * (2 * ei x * ej x)) =
            2 * ∑ x, c x * ei x * ej x := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
        rw [hmiddle]
        ring]
    _ = c i + c j := by
      rw [hcross, mul_zero, add_zero]
      have hi : diagonalQuadratic c ei = c i := by
        simpa only [ei] using diagonalQuadratic_basisFun c i
      have hj : diagonalQuadratic c ej = c j := by
        simpa only [ej] using diagonalQuadratic_basisFun c j
      rw [hi, hj]


variable [CharZero K]

/-- Polarization of the elementary diagonal quadratic polynomial. -/
theorem diagonalQuadratic_add {n : Nat} (c : Fin n → K)
    (x y : Fin n → K) :
    diagonalQuadratic c (x + y) =
      diagonalQuadratic c x + diagonalQuadratic c y +
        2 * ∑ i, c i * x i * y i := by
  unfold diagonalQuadratic
  simp_rw [Pi.add_apply, add_sq, mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hmiddle : (∑ i, c i * (2 * x i * y i)) =
      2 * ∑ i, c i * x i * y i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hmiddle]
  ring

/-- Equal-rank diagonal representation preserves the determinant square
class.  The returned unit is the determinant of the representing map. -/
theorem exists_prod_eq_mul_square_of_sameRank
    {n : Nat} {source target : Fin n → K}
    (h : DiagonalRepresents source target) :
    ∃ p : Kˣ,
      (∏ i, source i) = (∏ i, target i) * (p : K) ^ 2 := by
  classical
  rcases h with ⟨f, hf, hquadratic⟩
  let F : Matrix (Fin n) (Fin n) K := LinearMap.toMatrix' f
  have hmatrix : Matrix.diagonal source =
      F.transpose * Matrix.diagonal target * F := by
    ext i j
    by_cases hij : i = j
    · subst j
      rw [Matrix.diagonal_apply_eq]
      have hq := hquadratic (Pi.basisFun K (Fin n) i)
      rw [diagonalQuadratic_basisFun] at hq
      simpa [F, diagonalQuadratic, Matrix.mul_apply,
        Matrix.diagonal_apply, Pi.basisFun_apply, pow_two,
        mul_assoc, mul_comm, mul_left_comm]
        using hq.symm
    · rw [Matrix.diagonal_apply_ne _ hij]
      let ei := Pi.basisFun K (Fin n) i
      let ej := Pi.basisFun K (Fin n) j
      have hadd := diagonalQuadratic_add target (f ei) (f ej)
      rw [← f.map_add, hquadratic (ei + ej), hquadratic ei,
        hquadratic ej,
        diagonalQuadratic_basisFun_add source i j hij,
        diagonalQuadratic_basisFun source i,
        diagonalQuadratic_basisFun source j] at hadd
      have hcross : ∑ k, target k * f ei k * f ej k = 0 := by
        calc
          ∑ k, target k * f ei k * f ej k =
              (2 : K)⁻¹ *
                (2 * ∑ k, target k * f ei k * f ej k) := by
            field_simp
          _ = 0 := by
            rw [show 2 * ∑ k, target k * f ei k * f ej k = 0 by
              calc
                2 * ∑ k, target k * f ei k * f ej k =
                    (source i + source j +
                      2 * ∑ k, target k * f ei k * f ej k) -
                        (source i + source j) := by ring
                _ = 0 := by rw [← hadd]; ring]
            simp
      simpa [F, ei, ej, Matrix.mul_apply, Matrix.diagonal_apply,
        Pi.basisFun_apply,
        mul_assoc, mul_comm, mul_left_comm] using hcross.symm
  have hdet : (∏ i, source i) =
      (∏ i, target i) * Matrix.det F ^ 2 := by
    have h := congrArg Matrix.det hmatrix
    simp only [Matrix.det_diagonal, Matrix.det_mul,
      Matrix.det_transpose] at h
    calc
      ∏ i, source i = Matrix.det F * (∏ i, target i) * Matrix.det F := h
      _ = (∏ i, target i) * Matrix.det F ^ 2 := by ring
  have hdetNe : Matrix.det F ≠ 0 := by
    intro hzero
    have hker : LinearMap.ker f ≠ ⊥ :=
      (LinearMap.det_eq_zero_iff_ker_ne_bot.mp (by
        rw [← LinearMap.det_toMatrix']
        exact hzero))
    exact hker (LinearMap.ker_eq_bot.mpr hf)
  let p : Kˣ := Units.mk0 (Matrix.det F) hdetNe
  exact ⟨p, by simpa only [p, Units.val_mk0] using hdet⟩


end Bong.DiagonalRepresents
