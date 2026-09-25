import TraceEuclidean.V15DegreeFourDiscriminant
import TraceEuclidean.V15CubicPowerBasis

/-!
# Quartic power-basis discriminant formula

This module proves the exact discriminant formula for a four-dimensional
power basis. It is the algebraic bridge from a primitive quartic generator
to the explicit coefficient discriminant used by the finite enumeration.
-/

namespace TraceEuclidean

noncomputable section

open NumberField Module Polynomial
open scoped Matrix

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- Expansion of a four-by-four determinant along its first row. -/
theorem v15_det_fin_four {R : Type*} [CommRing R]
    (A : Matrix (Fin 4) (Fin 4) R) :
    Matrix.det A =
      A 0 0 * (A 1 1 * A 2 2 * A 3 3 - A 1 1 * A 2 3 * A 3 2 -
        A 1 2 * A 2 1 * A 3 3 + A 1 2 * A 2 3 * A 3 1 +
        A 1 3 * A 2 1 * A 3 2 - A 1 3 * A 2 2 * A 3 1) -
      A 0 1 * (A 1 0 * A 2 2 * A 3 3 - A 1 0 * A 2 3 * A 3 2 -
        A 1 2 * A 2 0 * A 3 3 + A 1 2 * A 2 3 * A 3 0 +
        A 1 3 * A 2 0 * A 3 2 - A 1 3 * A 2 2 * A 3 0) +
      A 0 2 * (A 1 0 * A 2 1 * A 3 3 - A 1 0 * A 2 3 * A 3 1 -
        A 1 1 * A 2 0 * A 3 3 + A 1 1 * A 2 3 * A 3 0 +
        A 1 3 * A 2 0 * A 3 1 - A 1 3 * A 2 1 * A 3 0) -
      A 0 3 * (A 1 0 * A 2 1 * A 3 2 - A 1 0 * A 2 2 * A 3 1 -
        A 1 1 * A 2 0 * A 3 2 + A 1 1 * A 2 2 * A 3 0 +
        A 1 2 * A 2 0 * A 3 1 - A 1 2 * A 2 1 * A 3 0) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ]
  simp only [Matrix.det_fin_three]
  simp only [Matrix.submatrix_apply]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero, one_mul,
    Fin.succ_zero_eq_one, Fin.zero_succAbove, Fin.succ_one_eq_two,
    Fin.reduceSucc, Nat.one_mod, pow_one, neg_mul, ne_eq, one_ne_zero,
    not_false_eq_true, Fin.succAbove_ne_zero_zero,
    Fin.one_succAbove_one, Nat.reduceMod, even_two, Even.neg_pow,
    one_pow, Fin.reduceEq, Nat.mod_succ, Finset.univ_eq_empty,
    Fin.val_succ, Fin.val_eq_zero, zero_add, Fin.succ_ne_zero,
    Fin.succ_succAbove_one, Finset.sum_empty, add_zero]
  have h12 : (1 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
  have h21 : (2 : Fin 4).succAbove (1 : Fin 3) = 1 := by decide
  have h22 : (2 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
  have h31 : (3 : Fin 4).succAbove (1 : Fin 3) = 1 := by decide
  have h32 : (3 : Fin 4).succAbove (2 : Fin 3) = 2 := by decide
  rw [h12, h21, h22, h31, h32]
  norm_num
  ring

/-- In dimension four, multiplication by the generator of a power basis has
the usual companion matrix. -/
theorem v15_powerBasis_companionMatrix_dim_four
    (pb : PowerBasis F L) (hdim : pb.dim = 4) :
    let e : Fin pb.dim ≃ Fin 4 := finCongr hdim
    Matrix.reindexAlgEquiv F F e
        (Algebra.leftMulMatrix pb.basis pb.gen) =
      !![0, 0, 0, -pb.minpolyGen.coeff 0;
         1, 0, 0, -pb.minpolyGen.coeff 1;
         0, 1, 0, -pb.minpolyGen.coeff 2;
         0, 0, 1, -pb.minpolyGen.coeff 3] := by
  classical
  dsimp only
  rw [pb.leftMulMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, hdim]

set_option maxHeartbeats 1600000 in
-- Symbolically evaluating the derivative in a four-dimensional companion
-- matrix requires substantially more normalization than the cubic case.
/-- The matrix of multiplication by the derivative of the minimal
polynomial, written in a quartic power basis. -/
theorem v15_powerBasis_derivativeMatrix_dim_four
    (pb : PowerBasis F L) (hdim : pb.dim = 4) :
    let e : Fin pb.dim ≃ Fin 4 := finCongr hdim
    Matrix.reindexAlgEquiv F F e
        (Algebra.leftMulMatrix pb.basis
          (Polynomial.aeval pb.gen (minpoly F pb.gen).derivative)) =
      !![pb.minpolyGen.coeff 1,
          -4 * pb.minpolyGen.coeff 0,
          pb.minpolyGen.coeff 0 * pb.minpolyGen.coeff 3,
          2 * pb.minpolyGen.coeff 0 * pb.minpolyGen.coeff 2 -
            pb.minpolyGen.coeff 0 * pb.minpolyGen.coeff 3 ^ 2;
         2 * pb.minpolyGen.coeff 2,
          -3 * pb.minpolyGen.coeff 1,
          -4 * pb.minpolyGen.coeff 0 +
            pb.minpolyGen.coeff 1 * pb.minpolyGen.coeff 3,
          pb.minpolyGen.coeff 0 * pb.minpolyGen.coeff 3 +
            2 * pb.minpolyGen.coeff 1 * pb.minpolyGen.coeff 2 -
            pb.minpolyGen.coeff 1 * pb.minpolyGen.coeff 3 ^ 2;
         3 * pb.minpolyGen.coeff 3,
          -2 * pb.minpolyGen.coeff 2,
          -3 * pb.minpolyGen.coeff 1 +
            pb.minpolyGen.coeff 2 * pb.minpolyGen.coeff 3,
          -4 * pb.minpolyGen.coeff 0 +
            pb.minpolyGen.coeff 1 * pb.minpolyGen.coeff 3 +
            2 * pb.minpolyGen.coeff 2 ^ 2 -
            pb.minpolyGen.coeff 2 * pb.minpolyGen.coeff 3 ^ 2;
         4, -pb.minpolyGen.coeff 3,
          -2 * pb.minpolyGen.coeff 2 + pb.minpolyGen.coeff 3 ^ 2,
          -3 * pb.minpolyGen.coeff 1 +
            3 * pb.minpolyGen.coeff 2 * pb.minpolyGen.coeff 3 -
            pb.minpolyGen.coeff 3 ^ 3] := by
  classical
  dsimp only
  let e : Fin pb.dim ≃ Fin 4 := finCongr hdim
  let M := Matrix.reindexAlgEquiv F F e
    (Algebra.leftMulMatrix pb.basis pb.gen)
  have hM : M =
      !![0, 0, 0, -pb.minpolyGen.coeff 0;
         1, 0, 0, -pb.minpolyGen.coeff 1;
         0, 1, 0, -pb.minpolyGen.coeff 2;
         0, 0, 1, -pb.minpolyGen.coeff 3] := by
    exact v15_powerBasis_companionMatrix_dim_four pb hdim
  rw [← pb.minpolyGen_eq]
  rw [← Polynomial.aeval_algHom_apply
    (Algebra.leftMulMatrix pb.basis) pb.gen pb.minpolyGen.derivative]
  rw [← Polynomial.aeval_algHom_apply
    (Matrix.reindexAlgEquiv F F e)
    (Algebra.leftMulMatrix pb.basis pb.gen) pb.minpolyGen.derivative]
  change Polynomial.aeval M pb.minpolyGen.derivative = _
  have hderiv : pb.minpolyGen.derivative.natDegree < 4 := by
    have h := Polynomial.natDegree_derivative_lt
      (p := pb.minpolyGen) (by
        rw [pb.natDegree_minpolyGen, hdim]
        norm_num)
    rwa [pb.natDegree_minpolyGen, hdim] at h
  rw [Polynomial.aeval_eq_sum_range' hderiv]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Finset.sum_range_zero, zero_add,
    Polynomial.coeff_derivative, Nat.cast_zero, Nat.cast_one,
    one_add_one_eq_two, Nat.cast_ofNat, pow_zero, pow_one,
    Matrix.smul_one_eq_diagonal]
  have hlead : pb.minpolyGen.coeff 4 = 1 := by
    have h := pb.minpolyGen_monic.coeff_natDegree
    rw [pb.natDegree_minpolyGen, hdim] at h
    exact h
  rw [hlead, hM]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ]
  all_goals ring_nf
  all_goals simp

set_option maxHeartbeats 2000000 in
-- The final determinant is a universal polynomial identity in the four
-- nonleading coefficients of the minimal polynomial.
/-- Exact discriminant formula for a quartic power basis. -/
theorem v15_powerBasis_discr_dim_four
    (pb : PowerBasis F L) (hdim : pb.dim = 4)
    [FiniteDimensional F L] [Algebra.IsSeparable F L] :
    Algebra.discr F pb.basis =
      256 * pb.minpolyGen.coeff 0 ^ 3 -
        192 * pb.minpolyGen.coeff 0 ^ 2 *
          pb.minpolyGen.coeff 1 * pb.minpolyGen.coeff 3 -
        128 * pb.minpolyGen.coeff 0 ^ 2 *
          pb.minpolyGen.coeff 2 ^ 2 +
        144 * pb.minpolyGen.coeff 0 ^ 2 *
          pb.minpolyGen.coeff 2 * pb.minpolyGen.coeff 3 ^ 2 -
        27 * pb.minpolyGen.coeff 0 ^ 2 * pb.minpolyGen.coeff 3 ^ 4 +
        144 * pb.minpolyGen.coeff 0 *
          pb.minpolyGen.coeff 1 ^ 2 * pb.minpolyGen.coeff 2 -
        6 * pb.minpolyGen.coeff 0 *
          pb.minpolyGen.coeff 1 ^ 2 * pb.minpolyGen.coeff 3 ^ 2 -
        80 * pb.minpolyGen.coeff 0 * pb.minpolyGen.coeff 1 *
          pb.minpolyGen.coeff 2 ^ 2 * pb.minpolyGen.coeff 3 +
        18 * pb.minpolyGen.coeff 0 * pb.minpolyGen.coeff 1 *
          pb.minpolyGen.coeff 2 * pb.minpolyGen.coeff 3 ^ 3 +
        16 * pb.minpolyGen.coeff 0 * pb.minpolyGen.coeff 2 ^ 4 -
        4 * pb.minpolyGen.coeff 0 *
          pb.minpolyGen.coeff 2 ^ 3 * pb.minpolyGen.coeff 3 ^ 2 -
        27 * pb.minpolyGen.coeff 1 ^ 4 +
        18 * pb.minpolyGen.coeff 1 ^ 3 *
          pb.minpolyGen.coeff 2 * pb.minpolyGen.coeff 3 -
        4 * pb.minpolyGen.coeff 1 ^ 3 * pb.minpolyGen.coeff 3 ^ 3 -
        4 * pb.minpolyGen.coeff 1 ^ 2 * pb.minpolyGen.coeff 2 ^ 3 +
        pb.minpolyGen.coeff 1 ^ 2 *
          pb.minpolyGen.coeff 2 ^ 2 * pb.minpolyGen.coeff 3 ^ 2 := by
  classical
  rw [Algebra.discr_powerBasis_eq_norm F pb]
  rw [Algebra.norm_eq_matrix_det pb.basis]
  rw [pb.finrank]
  simp only [hdim]
  norm_num
  let e : Fin pb.dim ≃ Fin 4 := finCongr hdim
  rw [← Matrix.det_reindexAlgEquiv F F e]
  rw [v15_powerBasis_derivativeMatrix_dim_four pb hdim]
  rw [v15_det_fin_four]
  simp
  ring

/-- Newton's second trace identity for a quartic power-basis generator. -/
theorem v15_powerBasis_trace_gen_sq_dim_four
    (pb : PowerBasis F L) (hdim : pb.dim = 4) :
    Algebra.trace F L (pb.gen ^ 2) =
      pb.minpolyGen.coeff 3 ^ 2 - 2 * pb.minpolyGen.coeff 2 := by
  classical
  rw [Algebra.trace_eq_matrix_trace pb.basis]
  let e : Fin pb.dim ≃ Fin 4 := finCongr hdim
  let M := Algebra.leftMulMatrix pb.basis pb.gen
  have hM : Matrix.reindexAlgEquiv F F e M =
      !![0, 0, 0, -pb.minpolyGen.coeff 0;
         1, 0, 0, -pb.minpolyGen.coeff 1;
         0, 1, 0, -pb.minpolyGen.coeff 2;
         0, 0, 1, -pb.minpolyGen.coeff 3] := by
    exact v15_powerBasis_companionMatrix_dim_four pb hdim
  calc
    Matrix.trace (Algebra.leftMulMatrix pb.basis (pb.gen ^ 2)) =
        Matrix.trace (Matrix.reindexAlgEquiv F F e
          (Algebra.leftMulMatrix pb.basis (pb.gen ^ 2))) :=
      (v15_matrix_trace_reindex e _).symm
    _ = Matrix.trace ((Matrix.reindexAlgEquiv F F e M) ^ 2) := by
      simp only [M, map_pow]
    _ = pb.minpolyGen.coeff 3 ^ 2 -
        2 * pb.minpolyGen.coeff 2 := by
      rw [hM]
      simp [Matrix.trace, Matrix.diag_apply, pow_two,
        Fin.sum_univ_succ]
      ring

set_option maxHeartbeats 2000000 in
-- Cubing the four-dimensional companion matrix gives Newton's third
-- identity without appealing to a separate symmetric-polynomial library.
/-- Newton's third trace identity for a quartic power-basis generator. -/
theorem v15_powerBasis_trace_gen_cube_dim_four
    (pb : PowerBasis F L) (hdim : pb.dim = 4) :
    Algebra.trace F L (pb.gen ^ 3) =
      -pb.minpolyGen.coeff 3 ^ 3 +
        3 * pb.minpolyGen.coeff 3 * pb.minpolyGen.coeff 2 -
        3 * pb.minpolyGen.coeff 1 := by
  classical
  rw [Algebra.trace_eq_matrix_trace pb.basis]
  let e : Fin pb.dim ≃ Fin 4 := finCongr hdim
  let M := Algebra.leftMulMatrix pb.basis pb.gen
  have hM : Matrix.reindexAlgEquiv F F e M =
      !![0, 0, 0, -pb.minpolyGen.coeff 0;
         1, 0, 0, -pb.minpolyGen.coeff 1;
         0, 1, 0, -pb.minpolyGen.coeff 2;
         0, 0, 1, -pb.minpolyGen.coeff 3] := by
    exact v15_powerBasis_companionMatrix_dim_four pb hdim
  calc
    Matrix.trace (Algebra.leftMulMatrix pb.basis (pb.gen ^ 3)) =
        Matrix.trace (Matrix.reindexAlgEquiv F F e
          (Algebra.leftMulMatrix pb.basis (pb.gen ^ 3))) :=
      (v15_matrix_trace_reindex e _).symm
    _ = Matrix.trace ((Matrix.reindexAlgEquiv F F e M) ^ 3) := by
      simp only [M, map_pow]
    _ = _ := by
      rw [hM]
      simp [Matrix.trace, Matrix.diag_apply, pow_succ,
        Fin.sum_univ_succ]
      ring

set_option maxHeartbeats 3000000 in
-- The fourth power is the last trace needed for the three-by-three Hermite
-- Gram determinant.
/-- Newton's fourth trace identity for a quartic power-basis generator. -/
theorem v15_powerBasis_trace_gen_fourth_dim_four
    (pb : PowerBasis F L) (hdim : pb.dim = 4) :
    Algebra.trace F L (pb.gen ^ 4) =
      pb.minpolyGen.coeff 3 ^ 4 -
        4 * pb.minpolyGen.coeff 3 ^ 2 * pb.minpolyGen.coeff 2 +
        2 * pb.minpolyGen.coeff 2 ^ 2 +
        4 * pb.minpolyGen.coeff 3 * pb.minpolyGen.coeff 1 -
        4 * pb.minpolyGen.coeff 0 := by
  classical
  rw [Algebra.trace_eq_matrix_trace pb.basis]
  let e : Fin pb.dim ≃ Fin 4 := finCongr hdim
  let M := Algebra.leftMulMatrix pb.basis pb.gen
  have hM : Matrix.reindexAlgEquiv F F e M =
      !![0, 0, 0, -pb.minpolyGen.coeff 0;
         1, 0, 0, -pb.minpolyGen.coeff 1;
         0, 1, 0, -pb.minpolyGen.coeff 2;
         0, 0, 1, -pb.minpolyGen.coeff 3] := by
    exact v15_powerBasis_companionMatrix_dim_four pb hdim
  calc
    Matrix.trace (Algebra.leftMulMatrix pb.basis (pb.gen ^ 4)) =
        Matrix.trace (Matrix.reindexAlgEquiv F F e
          (Algebra.leftMulMatrix pb.basis (pb.gen ^ 4))) :=
      (v15_matrix_trace_reindex e _).symm
    _ = Matrix.trace ((Matrix.reindexAlgEquiv F F e M) ^ 4) := by
      simp only [M, map_pow]
    _ = _ := by
      rw [hM]
      simp [Matrix.trace, Matrix.diag_apply, pow_succ,
        Fin.sum_univ_succ]
      ring

/-- Newton's first trace identity for a quartic power-basis generator. -/
theorem v15_powerBasis_trace_gen_dim_four
    (pb : PowerBasis F L) (hdim : pb.dim = 4) :
    Algebra.trace F L pb.gen = -pb.minpolyGen.coeff 3 := by
  rw [PowerBasis.trace_gen_eq_nextCoeff_minpoly]
  congr 1
  simp [Polynomial.nextCoeff, hdim]

end

end TraceEuclidean
