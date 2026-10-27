import NormEuclidean.CompletedHyperbolicSpinorMap
import NormEuclidean.BinarySpinorNorm

/-!
# Spinor-kernel transformations with a prescribed isotropic-ray multiplier

A binary norm is realized by a binary proper isometry. Its block extension
cancels the spinor norm of the explicit hyperbolic diagonal transformation,
while fixing the primitive hyperbolic vector.
-/

noncomputable section

namespace NormEuclidean.NormRayTransformations

open ProperSpinor SpinorBaseChange OrthogonalTransport CompletedIntegralLattice

variable {F V : Type*} [Field F] [CharZero F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate)

/-- The explicit two-reflection correction scales the first hyperbolic ray. -/
theorem correction_e (a : Fˣ) :
    (hyperbolicCorrection Q hQ a).1.1 (Hyperbolic.e : Hyperbolic F V) =
      (a : F) • Hyperbolic.e := by
  change IntegralReflection.linearEquiv (Hyperbolic.form Q) (0, (a : F), 1)
    (by simp [Hyperbolic.q])
    (IntegralReflection.linearEquiv (Hyperbolic.form Q) (0, 1, 1)
      (by simp [Hyperbolic.q]) Hyperbolic.e) = _
  simp only [IntegralReflection.linearEquiv_apply, QuadraticMap.polar,
    Hyperbolic.form_apply, Hyperbolic.q, Hyperbolic.e, Prod.fst_add, Prod.snd_add,
    Prod.fst_sub, Prod.snd_sub, zero_add, add_zero, map_zero, one_mul, mul_one]
  ext <;> simp

/-- Every binary norm is a multiplier of the isotropic ray inside the actual Wall kernel. -/
theorem exists_kernel_ray {theta : Fˣ} (f : BinaryNormForm.Frame Q theta) (a : Fˣ)
    (ha : Bong.Dyadic.IsQuadraticNorm F theta a) :
    ∃ s : properGroup (Hyperbolic.form Q),
      properAmbientSpinorNormHom (Hyperbolic.form Q)
          (Hyperbolic.form_polarBilin_nondegenerate Q hQ) s = 1 ∧
        s.1.1 (Hyperbolic.e : Hyperbolic F V) = (a : F) • Hyperbolic.e := by
  letI : Invertible (2 : F) := invertibleOfNonzero (by norm_num)
  obtain ⟨g, hg⟩ := BinarySpinorNorm.exists_proper_of_isNorm f hQ a ha
  let b := HyperbolicSpinorMap.properMap Q g
  let s := hyperbolicCorrection Q hQ a * b⁻¹
  refine ⟨s, ?_, ?_⟩
  · change properAmbientSpinorNormHom _ _ (hyperbolicCorrection Q hQ a * b⁻¹) = 1
    rw [map_mul, map_inv, hyperbolicCorrection_spinorNorm]
    have hb : properAmbientSpinorNormHom (Hyperbolic.form Q)
        (Hyperbolic.form_polarBilin_nondegenerate Q hQ) b = Bong.Dyadic.squareClass F a :=
      (HyperbolicSpinorMap.proper_spinorNorm_map Q hQ g).trans hg
    rw [hb, mul_inv_cancel]
  · have hb : b⁻¹ |>.1.1 (Hyperbolic.e : Hyperbolic F V) = Hyperbolic.e := by
      change (g.1.1.symm 0, (1 : F), (0 : F)) = (0, 1, 0)
      simp
    change (hyperbolicCorrection Q hQ a).1.1 (b⁻¹ |>.1.1 Hyperbolic.e) = _
    rw [hb, correction_e]

end NormEuclidean.NormRayTransformations

namespace NormEuclidean.NormRayTransformations

open ProperSpinor SpinorBaseChange OrthogonalTransport CompletedIntegralLattice IsDedekindDomain

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)

/-- The ray multiplier construction in the actual completed hyperbolic tensor space. -/
theorem exists_completed_kernel_ray {theta : Kˣ} (f : BinaryNormForm.Frame Q theta)
    (p : HeightOneSpectrum (integerSubring K)) (a : (LocalField (integerSubring K) p)ˣ)
    (ha : Bong.Dyadic.IsQuadraticNorm (LocalField (integerSubring K) p)
      (Units.map (algebraMap K (LocalField (integerSubring K) p)).toMonoidHom theta) a) :
    ∃ s : properGroup (form (integerSubring K) p (Hyperbolic.form Q)),
      properAmbientSpinorNormHom (form (integerSubring K) p (Hyperbolic.form Q))
          (form_polarBilin_nondegenerate _ p _
            (Hyperbolic.form_polarBilin_nondegenerate Q hQ)) s = 1 ∧
        s.1.1 (inclusion _ p (Hyperbolic.e : Hyperbolic K V)) =
          (a : LocalField (integerSubring K) p) • inclusion _ p Hyperbolic.e := by
  letI : CharZero (LocalField (integerSubring K) p) := Algebra.charZero_of_charZero K _
  let P := form (integerSubring K) p Q
  let H := form (integerSubring K) p (Hyperbolic.form Q)
  let e := hyperbolicEquiv (V := V) (integerSubring K) p
  have he : ∀ z, Hyperbolic.form P (e z) = H z := hyperbolicEquiv_form _ p Q
  have hP := form_polarBilin_nondegenerate (integerSubring K) p Q hQ
  have hH := form_polarBilin_nondegenerate (integerSubring K) p (Hyperbolic.form Q)
    (Hyperbolic.form_polarBilin_nondegenerate Q hQ)
  obtain ⟨g, hg, hge⟩ := exists_kernel_ray P hP (f.baseChange _) a ha
  let s := properMap (Hyperbolic.form P) H e.symm (inverse_value H _ e he) g
  refine ⟨s, ?_, ?_⟩
  · exact (proper_spinorNorm_map (Hyperbolic.form P) H e.symm (inverse_value H _ e he)
      (Hyperbolic.form_polarBilin_nondegenerate P hP) hH g).trans hg
  · apply e.injective
    change e (e.symm (g.1.1 (e _))) = e ((a : LocalField (integerSubring K) p) • _)
    rw [e.apply_symm_apply, e.map_smul]
    have hee : e (inclusion _ p (Hyperbolic.e : Hyperbolic K V)) = Hyperbolic.e := by
      simp [e, hyperbolicEquiv_inclusion, Hyperbolic.e]
    rw [hee]
    exact hge

end NormEuclidean.NormRayTransformations
