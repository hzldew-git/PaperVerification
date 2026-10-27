import NormEuclidean.HyperbolicUnipotentGroup
import NormEuclidean.ChapterX.HyperbolicAbelianization

/-!
# Square dilations as words in the two opposite unipotent families
-/

noncomputable section

namespace NormEuclidean.TernaryUnipotentDilation

open ProperSpinor SpinorBaseChange HyperbolicUnipotentGroup QuadraticMap

variable {F E : Type*} [Field F] [CharZero F] [AddCommGroup E] [Module F E]
  [FiniteDimensional F E] (Q : QuadraticForm F E) (hQ : Q.polarBilin.Nondegenerate)
  (hA : Q.Anisotropic)

/-- A Weyl element expressed using three actual unipotents. -/
def weyl (u : E) : properGroup (Hyperbolic.form Q) :=
  upper Q hQ hA u * lower Q hQ hA ((Q u)⁻¹ • u) * upper Q hQ hA u

theorem weyl_mem (u : E) : weyl Q hQ hA u ∈ generated Q hQ hA :=
  (generated Q hQ hA).mul_mem
    ((generated Q hQ hA).mul_mem (upper_mem Q hQ hA u) (lower_mem Q hQ hA _))
    (upper_mem Q hQ hA u)

/-- The Weyl word interchanges the two isotropic axes with the exact scale factors. -/
theorem weyl_apply (hdim : Module.finrank F E = 1) (u : E) (hu : Q u ≠ 0)
    (z : Hyperbolic F E) :
    (weyl Q hQ hA u).1.1 z = (-z.1, -(Q u)⁻¹ * z.2.2, -Q u * z.2.1) := by
  have hu0 : u ≠ 0 := fun h ↦ hu (by simp [h])
  rcases z with ⟨v, a, b⟩
  obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one hdim hu0 v
  change (upper Q hQ hA u).1.1
    ((lower Q hQ hA ((Q u)⁻¹ • u)).1.1
      ((upper Q hQ hA u).1.1 (c • u, a, b))) = _
  simp only [upper, lower, HyperbolicUnipotent.element_apply,
    OppositeHyperbolicUnipotent.element_apply, Hyperbolic.transvection,
    polar_sub_left, polar_smul_left, polar_smul_right, polar_self,
    Q.map_smul, smul_eq_mul, smul_smul, ← sub_smul]
  apply Prod.ext
  · change _ • u = -(c • u)
    rw [← neg_smul]
    congr 1
    field_simp [hu]
    ring
  · apply Prod.ext <;> dsimp only
    · field_simp [hu]
      ring
    · field_simp [hu]
      ring

/-- Every square hyperbolic dilation is a finite word in the opposite families. -/
theorem square_correction_mem (hdim : Module.finrank F E = 1) (u : E) (hu : Q u ≠ 0)
    (s : Fˣ) : hyperbolicCorrection Q hQ (s ^ 2) ∈ generated Q hQ hA := by
  have hsu : Q ((s : F) • u) ≠ 0 := by
    rw [Q.map_smul, smul_eq_mul]
    exact mul_ne_zero (mul_ne_zero s.ne_zero s.ne_zero) hu
  have hw : hyperbolicCorrection Q hQ (s ^ 2) =
      weyl Q hQ hA u * weyl Q hQ hA ((s : F) • u) := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    change (hyperbolicCorrection Q hQ (s ^ 2)).1.1 z =
      (weyl Q hQ hA u).1.1 ((weyl Q hQ hA ((s : F) • u)).1.1 z)
    rw [HyperbolicAbelianization.correction_apply, weyl_apply Q hQ hA hdim _ hu,
      weyl_apply Q hQ hA hdim _ hsu]
    simp only [Q.map_smul, smul_eq_mul, Units.val_pow_eq_pow_val, neg_neg]
    ext
    · rfl
    · field_simp [hu, s.ne_zero]
    · field_simp [hu, s.ne_zero]
  rw [hw]
  exact (generated Q hQ hA).mul_mem (weyl_mem Q hQ hA u) (weyl_mem Q hQ hA _)

end NormEuclidean.TernaryUnipotentDilation
