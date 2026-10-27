import NormEuclidean.ChapterX.ReflectionApproximation
import Bong.QuadraticSpace.OrthogonalExtension

/-!
# Two-reflection transitivity on nonzero quadratic values

This supplies the local proper-isometry input in O'Meara 104:3, step 2.
An anisotropic vector in its orthogonal complement adjusts the determinant
when one reflection suffices to identify the two given vectors.
-/

noncomputable section

namespace NormEuclidean.FixedValueTransitivity

open QuadraticMap ProperSpinor SpinorBaseChange

variable {F E : Type*} [Field F] [CharZero F] [AddCommGroup E] [Module F E]
  [FiniteDimensional F E]
variable (Q : QuadraticForm F E)

/-- A regular space of dimension at least two has an anisotropic vector
orthogonal to any vector of nonzero quadratic value. -/
theorem exists_anisotropic_orthogonal (hQ : Q.polarBilin.Nondegenerate)
    (hdim : 2 ≤ Module.finrank F E) (x : E) (hx : Q x ≠ 0) :
    ∃ u : E, Q u ≠ 0 ∧ polar Q x u = 0 := by
  let q := SpinorBridge.quadraticSpace Q hQ
  have hxq : q.IsAnisotropic x := by simpa [q, Bong.QuadraticSpace.IsAnisotropic] using hx
  have hpos : 0 < Module.finrank F (q.vectorOrthogonal x) := by
    have h := q.finrank_vectorOrthogonal hxq
    omega
  obtain ⟨u, hu⟩ := (q.orthogonalSpace x hxq).exists_isAnisotropic_of_finrank_pos hpos
  refine ⟨u, ?_, ?_⟩
  · simpa only [Bong.QuadraticSpace.IsAnisotropic,
      Bong.QuadraticSpace.orthogonalSpace_quadratic, q,
      SpinorBridge.quadraticSpace_quadratic] using hu
  · have h := (q.mem_vectorOrthogonal_iff x u).mp u.2
    change (2 : F)⁻¹ * polar Q x u = 0 at h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (by norm_num))

omit [CharZero F] [FiniteDimensional F E] in
/-- The reflection in the difference identifies equal-value vectors
whenever the difference has nonzero quadratic value. -/
theorem reflection_sub_apply (x y : E) (hxy : Q x = Q y) (hd : Q (x - y) ≠ 0) :
    IntegralReflection.linearEquiv Q (x - y) hd x = y := by
  have hvalue : Q (x - y) = Q x + Q y - polar Q x y := by
    rw [sub_eq_add_neg, QuadraticMap.map_add (Q : E → F), Q.map_neg, Q.polar_neg_right]
    ring
  have hpolar : polar Q (x - y) x = Q (x - y) := by
    rw [Q.polar_sub_left, polar_self, hvalue, polar_comm Q y x, hxy]
    simp only [two_smul]
  rw [IntegralReflection.linearEquiv_apply, hpolar, inv_mul_cancel₀ hd, one_smul]
  abel

/-- Any two vectors with equal nonzero quadratic value are identified by
two actual reflections. The orthogonal anisotropic vector is an explicit
padding witness, not an assumed proper-isometry existence principle. -/
theorem exists_doubleReflection_map (hQ : Q.polarBilin.Nondegenerate)
    (x y u : E) (hx : Q x ≠ 0) (hxy : Q x = Q y) (hu : Q u ≠ 0)
    (hxu : polar Q u x = 0) :
    ∃ (v : E) (hv : Q v ≠ 0) (w : E) (hw : Q w ≠ 0),
      (doubleReflection Q hQ v hv w hw).1.1 x = y := by
  by_cases hd : Q (x - y) ≠ 0
  · refine ⟨x - y, hd, u, hu, ?_⟩
    change IntegralReflection.linearEquiv Q (x - y) hd
      (IntegralReflection.linearEquiv Q u hu x) = y
    rw [IntegralReflection.linearEquiv_eq_self Q u hu x hxu]
    exact reflection_sub_apply Q x y hxy hd
  · have hd0 : Q (x - y) = 0 := not_ne_iff.mp hd
    have hsum : Q (x + y) = 4 * Q x := by
      have hsub : Q (x - y) = Q x + Q y - polar Q x y := by
        rw [sub_eq_add_neg, QuadraticMap.map_add (Q : E → F), Q.map_neg, Q.polar_neg_right]
        ring
      rw [QuadraticMap.map_add (Q : E → F)]
      rw [hxy] at hsub ⊢
      rw [hd0] at hsub
      linear_combination hsub
    have hs : Q (x + y) ≠ 0 := by rw [hsum]; exact mul_ne_zero (by norm_num) hx
    have hy : Q y ≠ 0 := hxy.symm.trans_ne hx
    refine ⟨y, hy, x + y, hs, ?_⟩
    have hr : IntegralReflection.linearEquiv Q (x + y) hs x = -y := by
      have heq : Q x = Q (-y) := by simpa only [Q.map_neg] using hxy
      have hdneg : Q (x - -y) ≠ 0 := by simpa only [sub_neg_eq_add] using hs
      simpa only [sub_neg_eq_add] using reflection_sub_apply Q x (-y) heq hdneg
    change IntegralReflection.linearEquiv Q y hy
      (IntegralReflection.linearEquiv Q (x + y) hs x) = y
    rw [hr, map_neg, IntegralReflection.linearEquiv_self, neg_neg]

end NormEuclidean.FixedValueTransitivity
