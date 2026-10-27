import NormEuclidean.ChapterX.QuadraticValueRepresentation
import NormEuclidean.QuadraticBaseChangeNondegenerate

/-!
# The opposite value in the complement of a vector in an isotropic space

This is the algebraic input at the excluded isotropic place in 104:3.
It holds over any characteristic-zero field, with no arithmetic transfer
theorem and no prescribed-value hypothesis on the complement.
-/

noncomputable section

namespace NormEuclidean.IsotropicOrthogonalComplement

variable {F E : Type*} [Field F] [CharZero F] [AddCommGroup E] [Module F E]

/-- Restricting a regular form to the polar kernel of a nonzero-value
vector preserves regularity, over the local field as well as globally. -/
theorem polar_kernel_regular (Q : QuadraticForm F E) (hQ : Q.polarBilin.Nondegenerate)
    (v : E) (hv : Q v ≠ 0) :
    (Q.comp (Q.polarBilin v).ker.subtype).polarBilin.Nondegenerate := by
  have hs : Q.polarBilin.IsRefl :=
    (show Q.polarBilin.IsSymm from
      ⟨fun x y ↦ QuadraticMap.polar_comm (Q : E → F) x y⟩).isRefl
  have hvv : Q.polarBilin v v ≠ 0 := by
    simp only [QuadraticMap.polarBilin_apply_apply, Q.polar_self, nsmul_eq_mul]
    exact mul_ne_zero (by norm_num) hv
  have h := LinearMap.BilinForm.restrict_nondegenerate_orthogonal_spanSingleton
    Q.polarBilin hQ hs hvv
  rw [LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker] at h
  exact h

/-- In an isotropic regular space, the orthogonal complement of v represents
minus Q(v). Both the orthogonal isotropic and nonorthogonal cases are proved. -/
theorem represents_negative_value (Q : QuadraticForm F E) (hQ : Q.polarBilin.Nondegenerate)
    (hiso : ¬ Q.Anisotropic) (v : E) (hv : Q v ≠ 0) :
    ∃ z : E, Q.polarBilin v z = 0 ∧ Q z = -Q v := by
  obtain ⟨e, he, heQ⟩ := Q.not_anisotropic_iff_exists.mp hiso
  by_cases hp : Q.polarBilin v e = 0
  · let eU : (Q.polarBilin v).ker := ⟨e, hp⟩
    have heU : eU ≠ 0 := fun h ↦ he (congrArg Subtype.val h)
    obtain ⟨z, hz⟩ := QuadraticValueRepresentation.represents_of_isotropic
      (Q.comp (Q.polarBilin v).ker.subtype) (polar_kernel_regular Q hQ v hv)
      eU heU heQ (-Q v)
    exact ⟨z, z.property, hz⟩
  · let t := 2 * Q v / Q.polarBilin v e
    refine ⟨t • e - v, ?_, ?_⟩
    · rw [LinearMap.map_sub, map_smul, smul_eq_mul]
      change 2 * Q v / Q.polarBilin v e * Q.polarBilin v e - Q.polarBilin v v = 0
      rw [div_mul_cancel₀ _ hp, QuadraticMap.polarBilin_apply_apply, Q.polar_self,
        nsmul_eq_mul]
      norm_num
    · rw [sub_eq_add_neg, QuadraticMap.map_add (Q : E → F), Q.map_smul,
        Q.map_neg, heQ, Q.polar_neg_right, Q.polar_smul_left,
        QuadraticMap.polar_comm (Q : E → F) e v]
      simp only [smul_eq_mul, mul_zero, zero_add]
      change Q v + -((2 * Q v / Q.polarBilin v e) * Q.polarBilin v e) = -Q v
      rw [div_mul_cancel₀ _ hp]
      ring

end NormEuclidean.IsotropicOrthogonalComplement
