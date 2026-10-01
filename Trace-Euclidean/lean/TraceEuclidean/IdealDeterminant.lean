import TraceEuclidean.TraceParityBridge
import Mathlib.RingTheory.Discriminant

/-!
The determinant of the trace Gram matrix of a quadratic ideal is the field
discriminant times the norm of its value ideal. This file first proves the
basis-independent linear-algebra statement and then the ideal norm factor.
-/

namespace TraceEuclidean

open Matrix Module
open scoped NumberField nonZeroDivisors

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

def twistedTraceMatrix (B : Basis (Fin 2) ℚ F) (α : F) :
    Matrix (Fin 2) (Fin 2) ℚ :=
  fun i j ↦ Algebra.trace ℚ F (α * B i * B j)

/-- Twisting the trace pairing by `α` multiplies its determinant by the
field norm of `α`, for every rational basis. -/
theorem twisted_trace_det (B : Basis (Fin 2) ℚ F) (α : F) :
    (twistedTraceMatrix B α).det =
      Algebra.discr ℚ B * Algebra.norm ℚ α := by
  have hmatrix : twistedTraceMatrix B α =
      Algebra.traceMatrix ℚ B * Algebra.leftMulMatrix B α := by
    ext i j
    have h := congrFun (Algebra.traceMatrix_of_basis_mulVec B (α * B j)) i
    -- The column of the multiplication matrix is the coordinate vector of `α * B j`.
    simpa only [twistedTraceMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Algebra.leftMulMatrix_eq_repr_mul, Basis.equivFun_apply,
      mul_assoc, mul_left_comm, mul_comm] using h.symm
  rw [hmatrix, Matrix.det_mul]
  rw [← Algebra.discr_def]
  exact congrArg (Algebra.discr ℚ B * ·) (Algebra.norm_eq_matrix_det B α).symm

/-- Reindex the selected integral basis of a quadratic number field by `Fin 2`. -/
def integerIndexEquiv (hdegree : Module.finrank ℚ F = 2) :
    Fin 2 ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 F) := by
  classical
  apply Fintype.equivOfCardEq
  rw [Fintype.card_fin, ← Module.finrank_eq_card_chooseBasisIndex]
  calc
    2 = Module.finrank ℚ F := hdegree.symm
    _ = Module.finrank ℤ (𝓞 F) := (NumberField.RingOfIntegers.rank F).symm

def integralFieldBasis (hdegree : Module.finrank ℚ F = 2) :
    Basis (Fin 2) ℚ F :=
  (NumberField.integralBasis F).reindex (integerIndexEquiv hdegree).symm

/-- The absolute change-of-basis determinant from the field integral basis
to the chosen basis of any fractional ideal equals its absolute norm. -/
theorem abs_det_integral_to_ideal
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (hdegree : Module.finrank ℚ F = 2) :
    |(integralFieldBasis hdegree).det
      (idealFieldBasis I hI hdegree)| = FractionalIdeal.absNorm I := by
  classical
  let e := integerIndexEquiv (F := F) hdegree
  let bZ : Basis (Fin 2) ℤ (𝓞 F) :=
    (NumberField.RingOfIntegers.basis F).reindex e.symm
  let bI := idealZBasis I hI hdegree
  have hbZ : bZ.localizationLocalization ℚ ℤ⁰ F =
      integralFieldBasis hdegree := by
    ext i
    simp [bZ, e, integralFieldBasis, NumberField.integralBasis_apply]
  have hbI : ((↑) ∘ bI : Fin 2 → F) =
      idealFieldBasis I hI hdegree := by
    funext i
    exact (ideal_field_basis_apply I hI hdegree i).symm
  simpa only [hbZ, hbI] using
    (FractionalIdeal.abs_det_basis_change bZ I bI)

/-- The ideal basis discriminant differs from the field discriminant by
the square of the ideal norm. -/
theorem ideal_basis_discriminant
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (hdegree : Module.finrank ℚ F = 2) :
    Algebra.discr ℚ (idealFieldBasis I hI hdegree) =
      (NumberField.discr F : ℚ) * (FractionalIdeal.absNorm I) ^ 2 := by
  classical
  let B := idealFieldBasis I hI hdegree
  let B₀ := integralFieldBasis hdegree
  have hchange : Algebra.discr ℚ B =
      (B₀.toMatrix B).det ^ 2 * Algebra.discr ℚ B₀ := by
    calc
      Algebra.discr ℚ B =
          Algebra.discr ℚ
            (B₀ ᵥ* (B₀.toMatrix B).map (algebraMap ℚ F)) := by
              rw [B₀.toMatrix_map_vecMul B]
      _ = (B₀.toMatrix B).det ^ 2 * Algebra.discr ℚ B₀ :=
        Algebra.discr_of_matrix_vecMul B₀ (B₀.toMatrix B)
  have hfield : Algebra.discr ℚ B₀ = (NumberField.discr F : ℚ) := by
    unfold B₀ integralFieldBasis
    rw [Basis.coe_reindex, Algebra.discr_reindex,
      ← NumberField.coe_discr]
  have habs := abs_det_integral_to_ideal I hI hdegree
  change |B₀.det B| = FractionalIdeal.absNorm I at habs
  have hsq : (B₀.toMatrix B).det ^ 2 = (FractionalIdeal.absNorm I) ^ 2 := by
    rw [Basis.det_apply] at habs
    rw [← sq_abs (B₀.toMatrix B).det, habs]
  rw [hchange, hsq, hfield]
  ring

/-- The exact determinant identity for the three entries of the trace Gram
matrix of an arbitrary quadratic fractional ideal. -/
theorem actual_ideal_trace_gram_determinant
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (hdegree : Module.finrank ℚ F = 2) (α : F)
    {a b c : ℕ}
    (hGram : idealTraceGram I hI hdegree α =
      ((a : ℚ), (b : ℚ), (c : ℚ))) :
    (a : ℚ) * c - (b : ℚ) ^ 2 =
      (NumberField.discr F : ℚ) * Algebra.norm ℚ α *
        (FractionalIdeal.absNorm I) ^ 2 := by
  let B := idealFieldBasis I hI hdegree
  have hA : Algebra.trace ℚ F (α * B 0 * B 0) = (a : ℚ) := by
    have h := congrArg Prod.fst hGram
    dsimp [idealTraceGram] at h
    simpa only [B, pow_two, mul_assoc] using h
  have hB : Algebra.trace ℚ F (α * B 0 * B 1) = (b : ℚ) := by
    have h := congrArg (fun z : ℚ × ℚ × ℚ ↦ z.2.1) hGram
    simpa only [idealTraceGram, B] using h
  have hC : Algebra.trace ℚ F (α * B 1 * B 1) = (c : ℚ) := by
    have h := congrArg (fun z : ℚ × ℚ × ℚ ↦ z.2.2) hGram
    dsimp [idealTraceGram] at h
    simpa only [B, pow_two, mul_assoc] using h
  have hB' : Algebra.trace ℚ F (α * B 1 * B 0) = (b : ℚ) := by
    convert hB using 1 <;> ring
  calc
    (a : ℚ) * c - (b : ℚ) ^ 2 =
        (twistedTraceMatrix B α).det := by
          rw [Matrix.det_fin_two]
          dsimp only [twistedTraceMatrix]
          rw [hA, hB, hB', hC]
          ring
    _ = Algebra.discr ℚ B * Algebra.norm ℚ α :=
      twisted_trace_det B α
    _ = (NumberField.discr F : ℚ) * Algebra.norm ℚ α *
          (FractionalIdeal.absNorm I) ^ 2 := by
      rw [ideal_basis_discriminant I hI hdegree]
      ring

/-- Any selected integral basis computes the number-field discriminant after
localization to the rational field. -/
theorem discr_of_integral_basis
    (bZ : Basis (Fin 2) ℤ (𝓞 F)) :
    (NumberField.discr F : ℚ) =
      Algebra.discr ℚ (bZ.localizationLocalization ℚ ℤ⁰ F) := by
  rw [← NumberField.discr_eq_discr F bZ]
  exact (Algebra.discr_localizationLocalization ℤ ℤ⁰ F bZ).symm

end

end TraceEuclidean
