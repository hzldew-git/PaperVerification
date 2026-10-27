import NormEuclidean.SpinorBaseChange

/-!
# Explicit hyperbolic unipotents in the actual proper spinor kernel

For an anisotropic complementary form, every hyperbolic transvection is
an actual proper transformation. A pair of equal-value reflections computes
its genuine Wall spinor norm as one. These identities also apply to a regular
line, providing the elementary transformations needed in the ternary case.
-/

noncomputable section

namespace NormEuclidean.HyperbolicUnipotent

open QuadraticMap ProperSpinor SpinorBaseChange

variable {F E : Type*} [Field F] [CharZero F] [AddCommGroup E] [Module F E]
  [FiniteDimensional F E] (Q : QuadraticForm F E) (hQ : Q.polarBilin.Nondegenerate)

omit [CharZero F] [FiniteDimensional F E] in
/-- The unhalved polar form in the full hyperbolic coordinates. -/
theorem polar_apply (x y : Hyperbolic F E) :
    polar (Hyperbolic.form Q) x y =
      polar Q x.1 y.1 + x.2.1 * y.2.2 + x.2.2 * y.2.1 := by
  simp only [QuadraticMap.polar, Hyperbolic.form_apply, Hyperbolic.q,
    Prod.fst_add, Prod.snd_add]
  ring

omit [CharZero F] [FiniteDimensional F E] in
/-- A reflecting vector with zero first hyperbolic coordinate has this explicit action. -/
theorem reflection_apply (u : E) (hu : Q u ≠ 0) (s : F) (z : Hyperbolic F E) :
    IntegralReflection.linearEquiv (Hyperbolic.form Q) (u, 0, s)
      (by simpa [Hyperbolic.q] using hu) z =
      (z.1 - ((Q u)⁻¹ * (polar Q u z.1 + s * z.2.1)) • u,
        z.2.1, z.2.2 - (Q u)⁻¹ * (polar Q u z.1 + s * z.2.1) * s) := by
  rw [IntegralReflection.linearEquiv_apply, polar_apply]
  ext <;> simp [Hyperbolic.q]

set_option maxHeartbeats 800000 in
/-- The existing transvection is exactly a pair of equal-value anisotropic reflections. -/
theorem pair_apply (u : E) (hu : Q u ≠ 0) (z : Hyperbolic F E) :
    (doubleReflection (Hyperbolic.form Q) (Hyperbolic.form_polarBilin_nondegenerate Q hQ)
      (u, 0, 0) (by simpa [Hyperbolic.q] using hu)
      (u, 0, -Q u) (by simpa [Hyperbolic.q] using hu)).1.1 z =
      Hyperbolic.transvection Q u z := by
  change IntegralReflection.linearEquiv (Hyperbolic.form Q) (u, 0, 0)
    (by simpa [Hyperbolic.q] using hu)
    (IntegralReflection.linearEquiv (Hyperbolic.form Q) (u, 0, -Q u)
      (by simpa [Hyperbolic.q] using hu) z) = _
  rw [reflection_apply Q u hu (-Q u) z, reflection_apply Q u hu 0]
  apply Prod.ext
  · change (z.1 - ((Q u)⁻¹ * (polar Q u z.1 + -Q u * z.2.1)) • u) -
      ((Q u)⁻¹ * (polar Q u
        (z.1 - ((Q u)⁻¹ * (polar Q u z.1 + -Q u * z.2.1)) • u) + 0 * z.2.1)) • u =
        z.1 - z.2.1 • u
    rw [Q.polar_sub_right, Q.polar_smul_right, Q.polar_self]
    rw [sub_sub, ← add_smul]
    congr 1
    congr 1
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    field_simp [hu]
    linear_combination -(2 * polar Q u z.1 - 2 * Q u * z.2.1) * (mul_inv_cancel₀ hu)
  · apply Prod.ext
    · rfl
    · change (z.2.2 - (Q u)⁻¹ * (polar Q u z.1 + -Q u * z.2.1) * -Q u) -
        (Q u)⁻¹ * _ * 0 = z.2.2 + polar Q z.1 u - z.2.1 * Q u
      rw [polar_comm Q z.1 u]
      field_simp [hu]
      ring

/-- The actual proper unipotent, including the zero parameter. -/
def element (_hA : Q.Anisotropic) (u : E) : properGroup (Hyperbolic.form Q) := by
  classical
  exact if hu : Q u = 0 then 1 else
    doubleReflection (Hyperbolic.form Q) (Hyperbolic.form_polarBilin_nondegenerate Q hQ)
      (u, 0, 0) (by simpa [Hyperbolic.q] using hu)
      (u, 0, -Q u) (by simpa [Hyperbolic.q] using hu)

/-- The bundled proper element has precisely the original transvection's coordinate formula. -/
theorem element_apply (hA : Q.Anisotropic) (u : E) (z : Hyperbolic F E) :
    (element Q hQ hA u).1.1 z = Hyperbolic.transvection Q u z := by
  classical
  by_cases hu : Q u = 0
  · have hu0 := hA u hu
    simp [element, hu0]
  · simpa only [element, dif_neg hu] using pair_apply Q hQ u hu z

/-- Each actual proper unipotent has trivial genuine Wall spinor norm. -/
theorem element_spinorNorm (hA : Q.Anisotropic) (u : E) :
    properAmbientSpinorNormHom (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ) (element Q hQ hA u) = 1 := by
  classical
  by_cases hu : Q u = 0
  · simp only [element, dif_pos hu, map_one]
  · rw [element, dif_neg hu, doubleReflection_spinorNorm]
    simp only [Hyperbolic.form_apply, Hyperbolic.q, zero_mul, add_zero]
    let a : Fˣ := Units.mk0 (Q u) hu
    change Bong.Dyadic.squareClass F (a * a) = 1
    rw [show a * a = (1 : Fˣ) * a ^ 2 by simp [pow_two], Bong.Dyadic.squareClass_mul_square]
    rfl

/-- Parameters add under the actual orthogonal-group multiplication. -/
theorem element_add (hA : Q.Anisotropic) (u w : E) :
    element Q hQ hA (u + w) = element Q hQ hA u * element Q hQ hA w := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  change (element Q hQ hA (u + w)).1.1 z =
    (element Q hQ hA u).1.1 ((element Q hQ hA w).1.1 z)
  simp only [element_apply, Hyperbolic.transvection_transvection]

/-- An integral parameter preserves the entire hyperbolic lattice in both directions. -/
theorem element_integral (hA : Q.Anisotropic) (R : Subring F) (L : Submodule R E)
    (hInt : ∀ x ∈ L, Q x ∈ R) (u : E) (hu : u ∈ L) :
    ∀ z : Hyperbolic F E, (element Q hQ hA u).1.1 z ∈ Hyperbolic.submodule L ↔
      z ∈ Hyperbolic.submodule L := by
  intro z
  rw [element_apply]
  change Hyperbolic.Mem L (Hyperbolic.transvection Q u z) ↔ Hyperbolic.Mem L z
  constructor
  · intro hz
    have h := Hyperbolic.mem_transvection (Q := Q) L hInt (L.neg_mem hu) hz
    rwa [Hyperbolic.transvection_neg_left] at h
  · exact Hyperbolic.mem_transvection (Q := Q) L hInt hu

end NormEuclidean.HyperbolicUnipotent
