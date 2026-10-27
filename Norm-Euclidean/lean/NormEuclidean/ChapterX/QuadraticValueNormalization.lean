import NormEuclidean.LocalRescaling
import NormEuclidean.ChapterX.LocalPrimitivePairing
import NormEuclidean.ChapterX.GenusVolumeFiniteness
import NormEuclidean.ChapterX.ScalarIntegralApproximation

/-!
# Normalizing a nonzero quadratic value

Scalar rescaling commutes with the entire actual tensor-space form.
Local half-polar self-duality is unchanged by a local unit scalar.
These comparisons supply the normalization in O'Meara 104:3 step 1.
-/

noncomputable section

namespace NormEuclidean.QuadraticValueNormalization

open IsDedekindDomain CompletedIntegralLattice ScalarIntegralApproximation LocalPrimitivePairing
open scoped TensorProduct

section Field

variable {F E : Type*} [Field F] [AddCommGroup E] [Module F E]

/-- A nonzero scalar with integral inverse preserves the integral-membership test. -/
theorem mul_mem_iff (S : Subring F) (a : F) (ha : a ≠ 0)
    (hint : a ∈ S) (hinv : a⁻¹ ∈ S) (b : F) : a * b ∈ S ↔ b ∈ S := by
  constructor
  · intro h
    have h' := S.mul_mem hinv h
    simpa only [← mul_assoc, inv_mul_cancel₀ ha, one_mul] using h'
  · exact S.mul_mem hint

/-- Self-duality of a lattice is unchanged by multiplying the bilinear form by a unit. -/
theorem selfDual_smul (S : Subring F) (B : LinearMap.BilinForm F E) (L : Submodule S E)
    (hL : SelfDual S B L) (a : F) (ha : a ≠ 0) (hint : a ∈ S) (hinv : a⁻¹ ∈ S) :
    SelfDual S (a • B) L := by
  intro x
  rw [hL x]
  apply forall_congr'
  intro y
  apply imp_congr_right
  intro _
  exact (mul_mem_iff S a ha hint hinv (B x y)).symm

/-- The half-polar convention respects scalar rescaling over any field. -/
theorem halfPolar_smul (a : F) (Q : QuadraticForm F E) :
    halfPolar (a • Q) = a • halfPolar Q := by
  ext x y
  simp only [halfPolar_apply, QuadraticMap.polar, QuadraticMap.smul_apply,
    LinearMap.smul_apply, smul_eq_mul]
  ring

end Field

variable {K F V : Type*} [Field K] [Field F] [Algebra K F] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V]

/-- Scalar rescaling commutes with base change on every tensor-space vector. -/
theorem baseChange_smul (a : K) (Q : QuadraticForm K V) :
    (a • Q).baseChange F = algebraMap K F a • Q.baseChange F := by
  apply _root_.baseChange_ext
  intro x
  simp only [QuadraticForm.baseChange_tmul, QuadraticMap.smul_apply, smul_eq_mul,
    Algebra.smul_def, map_mul]
  ring

/-- Rescaling by a nonzero scalar preserves anisotropy of the whole form. -/
theorem anisotropic_smul_iff (a : K) (ha : a ≠ 0) (Q : QuadraticForm K V) :
    (a • Q).Anisotropic ↔ Q.Anisotropic := by
  simp only [QuadraticMap.Anisotropic, QuadraticMap.smul_apply, smul_eq_mul,
    mul_eq_zero, ha, false_or]

variable [NumberField K]

/-- A unit-valued global scalar and its inverse belong to the actual local integer ring. -/
theorem local_unit_membership (a : K) (p : HeightOneSpectrum (integerSubring K))
    (hu : p.valuation K a = 1) :
    algebraMap K (LocalField (integerSubring K) p) a ∈ LocalRing (integerSubring K) p ∧
      algebraMap K (LocalField (integerSubring K) p) a⁻¹ ∈ LocalRing (integerSubring K) p := by
  constructor
  · change Valued.v (algebraMap K (LocalField (integerSubring K) p) a) ≤ 1
    rw [valuation_algebraMap, hu]
  · change Valued.v (algebraMap K (LocalField (integerSubring K) p) a⁻¹) ≤ 1
    rw [map_inv₀, map_inv₀, valuation_algebraMap, hu, inv_one]

set_option backward.isDefEq.respectTransparency false in
/-- Normalizing the target value preserves every off-target self-dual carrier. -/
theorem selfDual_normalize (Q : QuadraticForm K V) (a : K) (ha : a ≠ 0)
    (p : HeightOneSpectrum (integerSubring K)) (hu : p.valuation K a = 1)
    (L : Submodule (LocalRing (integerSubring K) p) (Space (V := V) (integerSubring K) p))
    (hL : SelfDual (LocalRing (integerSubring K) p)
      (halfPolar (form (integerSubring K) p Q)) L) :
    SelfDual (LocalRing (integerSubring K) p)
      (halfPolar (form (integerSubring K) p (a⁻¹ • Q))) L := by
  rw [form_rescale, halfPolar_smul]
  have hmem := local_unit_membership a p hu
  apply selfDual_smul _ _ L hL _ ((map_ne_zero _).mpr (inv_ne_zero ha)) hmem.2
  simpa only [map_inv₀, inv_inv] using hmem.1

end NormEuclidean.QuadraticValueNormalization
