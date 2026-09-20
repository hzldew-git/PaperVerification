import TraceEuclidean.V15VariableBasis
import TraceEuclidean.V15IdealDeterminant

/-!
The ideal norm and trace Gram determinant identities for every selected
integer basis, including the basis produced by Gauss reduction.
-/

namespace TraceEuclidean

open Module Matrix
open scoped NumberField nonZeroDivisors

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

theorem v15_abs_det_integral_to_ideal_of
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (hdegree : Module.finrank ℚ F = 2)
    (B : Basis (Fin 2) ℤ I.coeToSubmodule) :
    |(v15IntegralFieldBasis hdegree).det (v15IdealFieldBasisOf I hI B)| =
      FractionalIdeal.absNorm I := by
  classical
  let e := v15IntegerIndexEquiv (F := F) hdegree
  let bZ : Basis (Fin 2) ℤ (𝓞 F) :=
    (NumberField.RingOfIntegers.basis F).reindex e.symm
  have hbZ : bZ.localizationLocalization ℚ ℤ⁰ F =
      v15IntegralFieldBasis hdegree := by
    ext i
    simp [bZ, e, v15IntegralFieldBasis, NumberField.integralBasis_apply]
  have hbI : ((↑) ∘ B : Fin 2 → F) = v15IdealFieldBasisOf I hI B := by
    funext i
    exact (v15_ideal_field_basis_of_apply I hI B i).symm
  simpa only [hbZ, hbI] using
    (FractionalIdeal.abs_det_basis_change bZ I B)

theorem v15_ideal_basis_discriminant_of
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (hdegree : Module.finrank ℚ F = 2)
    (B : Basis (Fin 2) ℤ I.coeToSubmodule) :
    Algebra.discr ℚ (v15IdealFieldBasisOf I hI B) =
      (NumberField.discr F : ℚ) * (FractionalIdeal.absNorm I) ^ 2 := by
  classical
  let Bf := v15IdealFieldBasisOf I hI B
  let B₀ := v15IntegralFieldBasis hdegree
  have hchange : Algebra.discr ℚ Bf =
      (B₀.toMatrix Bf).det ^ 2 * Algebra.discr ℚ B₀ := by
    calc
      Algebra.discr ℚ Bf =
          Algebra.discr ℚ
            (B₀ ᵥ* (B₀.toMatrix Bf).map (algebraMap ℚ F)) := by
              rw [B₀.toMatrix_map_vecMul Bf]
      _ = (B₀.toMatrix Bf).det ^ 2 * Algebra.discr ℚ B₀ :=
        Algebra.discr_of_matrix_vecMul B₀ (B₀.toMatrix Bf)
  have hfield : Algebra.discr ℚ B₀ = (NumberField.discr F : ℚ) := by
    unfold B₀ v15IntegralFieldBasis
    rw [Basis.coe_reindex, Algebra.discr_reindex,
      ← NumberField.coe_discr]
  have habs := v15_abs_det_integral_to_ideal_of I hI hdegree B
  change |B₀.det Bf| = FractionalIdeal.absNorm I at habs
  have hsq : (B₀.toMatrix Bf).det ^ 2 = (FractionalIdeal.absNorm I) ^ 2 := by
    rw [Basis.det_apply] at habs
    rw [← sq_abs (B₀.toMatrix Bf).det, habs]
  rw [hchange, hsq, hfield]
  ring

theorem v15_actual_ideal_trace_gram_determinant_of
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (hdegree : Module.finrank ℚ F = 2)
    (B : Basis (Fin 2) ℤ I.coeToSubmodule) (α : F)
    {a b c : ℕ}
    (hGram : v15IdealTraceGramOf I hI B α =
      ((a : ℚ), (b : ℚ), (c : ℚ))) :
    (a : ℚ) * c - (b : ℚ) ^ 2 =
      (NumberField.discr F : ℚ) * Algebra.norm ℚ α *
        (FractionalIdeal.absNorm I) ^ 2 := by
  let Bf := v15IdealFieldBasisOf I hI B
  have hA : Algebra.trace ℚ F (α * Bf 0 * Bf 0) = (a : ℚ) := by
    have h := congrArg Prod.fst hGram
    dsimp [v15IdealTraceGramOf] at h
    simpa only [Bf, pow_two, mul_assoc] using h
  have hB : Algebra.trace ℚ F (α * Bf 0 * Bf 1) = (b : ℚ) := by
    have h := congrArg (fun z : ℚ × ℚ × ℚ ↦ z.2.1) hGram
    simpa only [v15IdealTraceGramOf, Bf] using h
  have hC : Algebra.trace ℚ F (α * Bf 1 * Bf 1) = (c : ℚ) := by
    have h := congrArg (fun z : ℚ × ℚ × ℚ ↦ z.2.2) hGram
    dsimp [v15IdealTraceGramOf] at h
    simpa only [Bf, pow_two, mul_assoc] using h
  have hB' : Algebra.trace ℚ F (α * Bf 1 * Bf 0) = (b : ℚ) := by
    convert hB using 1 <;> ring
  calc
    (a : ℚ) * c - (b : ℚ) ^ 2 =
        (v15TwistedTraceMatrix Bf α).det := by
          rw [Matrix.det_fin_two]
          dsimp only [v15TwistedTraceMatrix]
          rw [hA, hB, hB', hC]
          ring
    _ = Algebra.discr ℚ Bf * Algebra.norm ℚ α :=
      v15_twisted_trace_det Bf α
    _ = (NumberField.discr F : ℚ) * Algebra.norm ℚ α *
          (FractionalIdeal.absNorm I) ^ 2 := by
      rw [v15_ideal_basis_discriminant_of I hI hdegree B]
      ring

end

end TraceEuclidean
