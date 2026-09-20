import TraceEuclidean.V15IdealDeterminant
import Mathlib.LinearAlgebra.Basis.Fin

/-!
The explicit field discriminants of the concrete quadratic models, using
their already-proved complete integral-coordinate descriptions.
-/

namespace TraceEuclidean

open Module
open scoped NumberField nonZeroDivisors

noncomputable section

theorem v15_caseI_field_discriminant
    {m : ℕ} (hm : 1 < m) (hsq : IsSquarefreeNat m)
    (hmod : m % 4 = 2 ∨ m % 4 = 3) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare hm hsq⟩
    (NumberField.discr (RealQuadraticAlgebra m) : ℚ) = 4 * m := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  let bZ : Basis (Fin 2) ℤ (𝓞 (RealQuadraticAlgebra m)) :=
    (Basis.finTwoProd ℤ).map
      (caseIIntegerPointRingEquiv hsq hmod).toIntLinearEquiv
  let bQ := bZ.localizationLocalization ℚ ℤ⁰ (RealQuadraticAlgebra m)
  have hb0 : bQ 0 = 1 := by
    apply QuadraticAlgebra.ext <;>
      simp [bQ, bZ, caseIIntegerPointRingEquiv, caseIIntegerPointRingHom,
        caseIIntegerPointToRing, caseIIntegerPointValue,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have hb1 : bQ 1 = (QuadraticAlgebra.omega : RealQuadraticAlgebra m) := by
    apply QuadraticAlgebra.ext <;>
      simp [bQ, bZ, caseIIntegerPointRingEquiv, caseIIntegerPointRingHom,
        caseIIntegerPointToRing, caseIIntegerPointValue]
  rw [v15_discr_of_integral_basis bZ]
  change Algebra.discr ℚ bQ = 4 * m
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  rw [hb0, hb1]
  simp [realQuadratic_trace, QuadraticAlgebra.re_one,
    QuadraticAlgebra.im_one, pow_two]
  ring

theorem v15_caseII_field_discriminant
    {m : ℕ} (hm : 1 < m) (hsq : IsSquarefreeNat m)
    (hmod : m % 4 = 1) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare hm hsq⟩
    (NumberField.discr (RealQuadraticAlgebra m) : ℚ) = m := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  let bZ : Basis (Fin 2) ℤ (𝓞 (RealQuadraticAlgebra m)) :=
    (Basis.finTwoProd ℤ).map
      (caseIIIntegerPointRingEquiv hsq hmod).toIntLinearEquiv
  let bQ := bZ.localizationLocalization ℚ ℤ⁰ (RealQuadraticAlgebra m)
  have hb0 : bQ 0 = 1 := by
    apply QuadraticAlgebra.ext <;>
      simp [bQ, bZ, caseIIIntegerPointRingEquiv, caseIIIntegerPointRingHom,
        caseIIIntegerPointToRing, caseIIIntegerPointValue,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have hb1 : bQ 1 = quadraticEta (m := m) := by
    apply QuadraticAlgebra.ext <;>
      simp [bQ, bZ, caseIIIntegerPointRingEquiv, caseIIIntegerPointRingHom,
        caseIIIntegerPointToRing, caseIIIntegerPointValue, quadraticEta]
  rw [v15_discr_of_integral_basis bZ]
  change Algebra.discr ℚ bQ = m
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  rw [hb0, hb1]
  simp [realQuadratic_trace, quadraticEta, QuadraticAlgebra.re_one,
    QuadraticAlgebra.im_one, pow_two]
  ring

/-- The manuscript's positive quadratic discriminant agrees with the
number-field discriminant of the concrete model. -/
theorem v15_real_quadratic_field_discriminant
    {m : ℕ} (hm : 1 < m) (hsq : IsSquarefreeNat m) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare hm hsq⟩
    (NumberField.discr (RealQuadraticAlgebra m) : ℚ) =
      (v15QuadraticDiscriminant m : ℚ) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  rcases squarefree_mod_four_cases hsq with hmod | hmod
  · rw [v15_caseII_field_discriminant hm hsq hmod]
    simp [v15QuadraticDiscriminant, hmod]
  · rw [v15_caseI_field_discriminant hm hsq hmod]
    have hnot : m % 4 ≠ 1 := by omega
    simp [v15QuadraticDiscriminant, hnot]

end

end TraceEuclidean
