import NormEuclidean.ChapterX.CompletedSubspaceIntersection
import NormEuclidean.ChapterX.NegativeLineBaseChange
import NormEuclidean.ChapterX.IsotropicOrthogonalComplement

/-!
# The actual scalar extension of an orthogonal complement

The extended inclusion has precisely the local polar kernel as its range.
This compares actual tensor spaces; it is not an assumed identification of
the global complement with a newly chosen local subspace.
-/

noncomputable section

namespace NormEuclidean.OrthogonalBaseChange

open ProjectedComplement
open scoped TensorProduct

variable {K F V : Type*} [Field K] [CharZero K] [Field F] [Algebra K F]
  [AddCommGroup V] [Module K V] [Invertible (2 : K)] [Invertible (2 : F)]

/-- The literal half-polar complement is the polar linear kernel. -/
theorem complement_eq_polar_kernel (Q : QuadraticForm K V) (v : V) :
    complement Q v = (Q.polarBilin v).ker := by
  rw [complement, LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker]
  ext x
  change (2 : K)⁻¹ * Q.polarBilin v x = 0 ↔ Q.polarBilin v x = 0
  exact mul_eq_zero.trans (or_iff_right (inv_ne_zero (by norm_num)))

/-- The local polar functional is the scalar extension of the original one,
followed by the canonical scalar-tensor comparison. -/
theorem polar_baseChange_functional (Q : QuadraticForm K V) (v : V)
    (z : F ⊗[K] V) :
    (Q.baseChange F).polarBilin ((1 : F) ⊗ₜ[K] v) z =
      TensorProduct.AlgebraTensorModule.rid K F F ((Q.polarBilin v).baseChange F z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp only [QuadraticForm.polarBilin_baseChange, LinearMap.BilinForm.baseChange_tmul,
      LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.rid_tmul,
      Algebra.smul_def, one_mul]
  | add z t hz ht => simp only [map_add, hz, ht]

/-- The extended inclusion of the global complement has exactly the local
orthogonal kernel as its range. Flatness supplies the reverse inclusion. -/
theorem range_subtype_baseChange (Q : QuadraticForm K V) (v : V) :
    LinearMap.range ((complement Q v).subtype.baseChange F) =
      ((Q.baseChange F).polarBilin ((1 : F) ⊗ₜ[K] v)).ker := by
  have hker : ((Q.polarBilin v).baseChange F).ker =
      LinearMap.range ((Q.polarBilin v).ker.subtype.baseChange F) :=
    Module.Flat.ker_lTensor_eq F F (Q.polarBilin v)
  rw [complement_eq_polar_kernel, ← hker]
  ext z
  change (Q.polarBilin v).baseChange F z = 0 ↔
    (Q.baseChange F).polarBilin ((1 : F) ⊗ₜ[K] v) z = 0
  rw [polar_baseChange_functional]
  exact (map_eq_zero_iff (TensorProduct.AlgebraTensorModule.rid K F F)
    (TensorProduct.AlgebraTensorModule.rid K F F).injective).symm

/-- The quadratic form on the extended global complement is the restriction
of the extended ambient form along its actual inclusion. -/
theorem form_comp_subtype (Q : QuadraticForm K V) (v : V) :
    (Q.baseChange F).comp ((complement Q v).subtype.baseChange F) =
      QuadraticForm.baseChange F (Q.comp (complement Q v).subtype) := by
  apply _root_.baseChange_ext
  intro x
  simp only [QuadraticMap.comp_apply, LinearMap.baseChange_tmul,
    QuadraticForm.baseChange_tmul]

/-- Every vector in the actual local orthogonal complement lifts to the
scalar extension of the global complement, with its value preserved. -/
theorem exists_lift (Q : QuadraticForm K V) (v : V) (z : F ⊗[K] V)
    (hz : (Q.baseChange F).polarBilin ((1 : F) ⊗ₜ[K] v) z = 0) :
    ∃ u : F ⊗[K] (complement Q v),
      (complement Q v).subtype.baseChange F u = z ∧
      QuadraticForm.baseChange F (Q.comp (complement Q v).subtype) u = Q.baseChange F z := by
  obtain ⟨u, hu⟩ := (show z ∈ LinearMap.range ((complement Q v).subtype.baseChange F) by
    rw [range_subtype_baseChange]
    exact hz)
  refine ⟨u, hu, ?_⟩
  rw [← form_comp_subtype, QuadraticMap.comp_apply, hu]

variable [CharZero F] [FiniteDimensional K V]

/-- At an actual isotropic completion, the extended global complement
represents the negative normalized target. The normalization and the tensor
comparison are proved, rather than supplied as a local representation input. -/
theorem represents_negative_normalized_value (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (v : V) (hv : Q v ≠ 0) (a c : K)
    (hc : c ≠ 0) (hvalue : Q v = c ^ 2 * a) (hiso : ¬ (Q.baseChange F).Anisotropic) :
    ∃ u : F ⊗[K] (complement Q v),
      QuadraticForm.baseChange F (Q.comp (complement Q v).subtype) u =
        -algebraMap K F a := by
  have hvF : Q.baseChange F ((1 : F) ⊗ₜ[K] v) = algebraMap K F (Q v) := by
    simp only [QuadraticForm.baseChange_tmul, Algebra.smul_def, mul_one, one_mul]
  have hv0 : Q.baseChange F ((1 : F) ⊗ₜ[K] v) ≠ 0 := by
    rw [hvF]
    exact (map_ne_zero _).mpr hv
  obtain ⟨z, hzorth, hzQ⟩ := IsotropicOrthogonalComplement.represents_negative_value
    (Q.baseChange F) (quadraticForm_baseChange_polarBilin_nondegenerate Q hQ)
    hiso ((1 : F) ⊗ₜ[K] v) hv0
  obtain ⟨u, _, huQ⟩ := exists_lift Q v z hzorth
  have hcF : algebraMap K F c ≠ 0 := (map_ne_zero _).mpr hc
  refine ⟨(algebraMap K F c)⁻¹ • u, ?_⟩
  rw [QuadraticMap.map_smul, huQ, hzQ, hvF, hvalue, map_mul, map_pow, smul_eq_mul]
  field_simp
  <;> ring

end NormEuclidean.OrthogonalBaseChange
