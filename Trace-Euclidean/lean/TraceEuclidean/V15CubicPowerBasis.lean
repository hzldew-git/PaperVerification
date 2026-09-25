import TraceEuclidean.V15DegreeThreeDiscriminant

/-!
# Cubic power-basis discriminant formula

This module proves the exact discriminant formula for a three-dimensional
power basis.  It supplies the algebraic bridge from the minimal polynomial
of a primitive cubic generator to the discriminant of its power basis.
-/

namespace TraceEuclidean

noncomputable section

open NumberField Module Polynomial
open scoped Matrix

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- In dimension three, multiplication by the generator of a power basis has
the usual companion matrix. -/
theorem v15_powerBasis_companionMatrix_dim_three
    (pb : PowerBasis F L) (hdim : pb.dim = 3) :
    let e : Fin pb.dim ≃ Fin 3 := finCongr hdim
    Matrix.reindexAlgEquiv F F e
        (Algebra.leftMulMatrix pb.basis pb.gen) =
      !![0, 0, -pb.minpolyGen.coeff 0;
         1, 0, -pb.minpolyGen.coeff 1;
         0, 1, -pb.minpolyGen.coeff 2] := by
  classical
  dsimp only
  rw [pb.leftMulMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, hdim]

set_option maxHeartbeats 800000 in
-- Expanding the derivative polynomial into a symbolic three-by-three matrix
-- requires more normalization steps than the project-wide default permits.
/-- The matrix of multiplication by the derivative of the minimal
polynomial, written in a cubic power basis. -/
theorem v15_powerBasis_derivativeMatrix_dim_three
    (pb : PowerBasis F L) (hdim : pb.dim = 3) :
    let e : Fin pb.dim ≃ Fin 3 := finCongr hdim
    Matrix.reindexAlgEquiv F F e
        (Algebra.leftMulMatrix pb.basis
          (Polynomial.aeval pb.gen (minpoly F pb.gen).derivative)) =
      !![pb.minpolyGen.coeff 1,
          -3 * pb.minpolyGen.coeff 0,
          pb.minpolyGen.coeff 0 * pb.minpolyGen.coeff 2;
         2 * pb.minpolyGen.coeff 2,
          -2 * pb.minpolyGen.coeff 1,
          pb.minpolyGen.coeff 1 * pb.minpolyGen.coeff 2 -
            3 * pb.minpolyGen.coeff 0;
         3, -pb.minpolyGen.coeff 2,
          pb.minpolyGen.coeff 2 ^ 2 -
            2 * pb.minpolyGen.coeff 1] := by
  classical
  dsimp only
  let e : Fin pb.dim ≃ Fin 3 := finCongr hdim
  let M := Matrix.reindexAlgEquiv F F e
    (Algebra.leftMulMatrix pb.basis pb.gen)
  have hM : M =
      !![0, 0, -pb.minpolyGen.coeff 0;
         1, 0, -pb.minpolyGen.coeff 1;
         0, 1, -pb.minpolyGen.coeff 2] := by
    exact v15_powerBasis_companionMatrix_dim_three pb hdim
  rw [← pb.minpolyGen_eq]
  rw [← Polynomial.aeval_algHom_apply
    (Algebra.leftMulMatrix pb.basis) pb.gen pb.minpolyGen.derivative]
  rw [← Polynomial.aeval_algHom_apply
    (Matrix.reindexAlgEquiv F F e)
    (Algebra.leftMulMatrix pb.basis pb.gen) pb.minpolyGen.derivative]
  change Polynomial.aeval M pb.minpolyGen.derivative = _
  have hderiv : pb.minpolyGen.derivative.natDegree < 3 := by
    have h := Polynomial.natDegree_derivative_lt
      (p := pb.minpolyGen) (by
        rw [pb.natDegree_minpolyGen, hdim]
        norm_num)
    rwa [pb.natDegree_minpolyGen, hdim] at h
  rw [Polynomial.aeval_eq_sum_range' hderiv]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ]
  simp only [Finset.sum_range_zero, zero_add,
    Polynomial.coeff_derivative, Nat.cast_zero, Nat.cast_one,
    one_add_one_eq_two, Nat.cast_ofNat, pow_zero, pow_one,
    Matrix.smul_one_eq_diagonal]
  have hlead : pb.minpolyGen.coeff 3 = 1 := by
    have h := pb.minpolyGen_monic.coeff_natDegree
    rw [pb.natDegree_minpolyGen, hdim] at h
    exact h
  rw [hlead, hM]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_two]
  all_goals ring_nf
  all_goals simp

/-- Exact discriminant formula for a cubic power basis. -/
theorem v15_powerBasis_discr_dim_three
    (pb : PowerBasis F L) (hdim : pb.dim = 3)
    [FiniteDimensional F L] [Algebra.IsSeparable F L] :
    Algebra.discr F pb.basis =
      pb.minpolyGen.coeff 2 ^ 2 * pb.minpolyGen.coeff 1 ^ 2 -
        4 * pb.minpolyGen.coeff 1 ^ 3 -
        4 * pb.minpolyGen.coeff 2 ^ 3 * pb.minpolyGen.coeff 0 -
        27 * pb.minpolyGen.coeff 0 ^ 2 +
        18 * pb.minpolyGen.coeff 2 * pb.minpolyGen.coeff 1 *
          pb.minpolyGen.coeff 0 := by
  classical
  rw [Algebra.discr_powerBasis_eq_norm F pb]
  rw [Algebra.norm_eq_matrix_det pb.basis]
  rw [pb.finrank]
  simp only [hdim]
  norm_num
  let e : Fin pb.dim ≃ Fin 3 := finCongr hdim
  rw [← Matrix.det_reindexAlgEquiv F F e]
  rw [v15_powerBasis_derivativeMatrix_dim_three pb hdim]
  simp [Matrix.det_fin_three]
  ring

/-- Simultaneously reindexing the rows and columns preserves the matrix
trace. -/
theorem v15_matrix_trace_reindex
    {R : Type*} [CommRing R]
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) (A : Matrix m m R) :
    Matrix.trace (Matrix.reindexAlgEquiv R R e A) = Matrix.trace A := by
  rw [Matrix.trace, Matrix.trace, ← e.sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Matrix.diag_apply, Matrix.coe_reindexAlgEquiv,
    Matrix.reindex_apply]

/-- Newton's second trace identity for a cubic power-basis generator. -/
theorem v15_powerBasis_trace_gen_sq_dim_three
    (pb : PowerBasis F L) (hdim : pb.dim = 3) :
    Algebra.trace F L (pb.gen ^ 2) =
      pb.minpolyGen.coeff 2 ^ 2 - 2 * pb.minpolyGen.coeff 1 := by
  classical
  rw [Algebra.trace_eq_matrix_trace pb.basis]
  let e : Fin pb.dim ≃ Fin 3 := finCongr hdim
  let M := Algebra.leftMulMatrix pb.basis pb.gen
  have hM : Matrix.reindexAlgEquiv F F e M =
      !![0, 0, -pb.minpolyGen.coeff 0;
         1, 0, -pb.minpolyGen.coeff 1;
         0, 1, -pb.minpolyGen.coeff 2] := by
    exact v15_powerBasis_companionMatrix_dim_three pb hdim
  calc
    Matrix.trace (Algebra.leftMulMatrix pb.basis (pb.gen ^ 2)) =
        Matrix.trace (Matrix.reindexAlgEquiv F F e
          (Algebra.leftMulMatrix pb.basis (pb.gen ^ 2))) :=
      (v15_matrix_trace_reindex e _).symm
    _ = Matrix.trace ((Matrix.reindexAlgEquiv F F e M) ^ 2) := by
      simp only [M, map_pow]
    _ = pb.minpolyGen.coeff 2 ^ 2 -
        2 * pb.minpolyGen.coeff 1 := by
      rw [hM]
      simp [Matrix.trace, Matrix.diag_apply, pow_two,
        Fin.sum_univ_succ]
      ring

/-- Newton's first trace identity for a cubic power-basis generator. -/
theorem v15_powerBasis_trace_gen_dim_three
    (pb : PowerBasis F L) (hdim : pb.dim = 3) :
    Algebra.trace F L pb.gen = -pb.minpolyGen.coeff 2 := by
  rw [PowerBasis.trace_gen_eq_nextCoeff_minpoly]
  congr 1
  simp [Polynomial.nextCoeff, hdim]

end

end TraceEuclidean
