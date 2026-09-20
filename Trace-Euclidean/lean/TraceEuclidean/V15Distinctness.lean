import TraceEuclidean.V15PositivityBridge
import Mathlib.NumberTheory.NumberField.Units.Basic

/-!
The two representatives over `ℚ(√5)` are distinct. Representatives over
different radicands lie over different square-free real quadratic fields.
-/

namespace TraceEuclidean

open Module
open scoped NumberField nonZeroDivisors

noncomputable section

def V15FreeFormsIsometric
    {F : Type*} [Field F] [NumberField F] (α δ : F) : Prop :=
  ∃ e : (𝓞 F) ≃ₗ[𝓞 F] (𝓞 F),
    ∀ x : 𝓞 F,
      α * (((e x : 𝓞 F) : F) ^ 2) = δ * (x : F) ^ 2

theorem v15_mfive_one_two_not_isometric :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (5 : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare (by norm_num) v15_small_squarefree_five⟩
    ¬ V15FreeFormsIsometric
        (1 : RealQuadraticAlgebra 5) (2 : RealQuadraticAlgebra 5) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (5 : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare (by norm_num) v15_small_squarefree_five⟩
  intro h
  obtain ⟨e, he⟩ := h
  let y : 𝓞 (RealQuadraticAlgebra 5) := e 1
  have hySq : ((y : RealQuadraticAlgebra 5) ^ 2) = 2 := by
    simpa [y] using he 1
  have hmap (x : 𝓞 (RealQuadraticAlgebra 5)) : e x = x * y := by
    calc
      e x = e (x • (1 : 𝓞 (RealQuadraticAlgebra 5))) := by
        simp [smul_eq_mul]
      _ = x • e 1 := map_smul e x 1
      _ = x * y := by simp [y, smul_eq_mul]
  let z : 𝓞 (RealQuadraticAlgebra 5) := e.symm 1
  have hzy : z * y = 1 := by
    have hez : e z = 1 := e.apply_symm_apply 1
    rw [hmap] at hez
    exact hez
  have hyunit : IsUnit y :=
    isUnit_iff_exists_inv.mpr ⟨z, by simpa only [mul_comm] using hzy⟩
  have hnormAbs : |Algebra.norm ℚ (y : RealQuadraticAlgebra 5)| = 1 := by
    simpa only [RingOfIntegers.coe_norm] using
      (NumberField.isUnit_iff_norm.mp hyunit)
  have hnormSq : (Algebra.norm ℚ (y : RealQuadraticAlgebra 5)) ^ 2 =
      (4 : ℚ) := by
    have h := congrArg (Algebra.norm ℚ) hySq
    rw [map_pow] at h
    have htwo : Algebra.norm ℚ (2 : RealQuadraticAlgebra 5) =
        (4 : ℚ) := by
          norm_num [realQuadratic_norm, QuadraticAlgebra.re_ofNat,
            QuadraticAlgebra.im_ofNat]
    rw [htwo] at h
    exact h
  have hnormSqOne : (Algebra.norm ℚ (y : RealQuadraticAlgebra 5)) ^ 2 =
      (1 : ℚ) := by
    calc
      (Algebra.norm ℚ (y : RealQuadraticAlgebra 5)) ^ 2 =
          |Algebra.norm ℚ (y : RealQuadraticAlgebra 5)| ^ 2 :=
            (sq_abs _).symm
      _ = 1 := by rw [hnormAbs]; norm_num
  norm_num [hnormSqOne] at hnormSq

/-- Different field discriminants exclude a rational field isomorphism.
This applies to the five square-free radicands in the six-class list. -/
theorem v15_distinct_discriminants_no_field_isomorphism
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n)
    (hsm : IsSquarefreeNat m) (hsn : IsSquarefreeNat n)
    (hdisc : v15QuadraticDiscriminant m ≠
      v15QuadraticDiscriminant n) :
    ¬ Nonempty (RealQuadraticAlgebra m ≃ₐ[ℚ] RealQuadraticAlgebra n) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsm⟩
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (n : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hn hsn⟩
  intro ⟨e⟩
  have heq := NumberField.discr_eq_discr_of_algEquiv
    (RealQuadraticAlgebra m) e
  have heqQ : (NumberField.discr (RealQuadraticAlgebra m) : ℚ) =
      (NumberField.discr (RealQuadraticAlgebra n) : ℚ) :=
    congrArg (fun z : ℤ ↦ (z : ℚ)) heq
  rw [v15_real_quadratic_field_discriminant hm hsm,
    v15_real_quadratic_field_discriminant hn hsn] at heqQ
  exact hdisc (by exact_mod_cast heqQ)

theorem v15_five_field_discriminants_nodup :
    ([(v15QuadraticDiscriminant 2), (v15QuadraticDiscriminant 3),
      (v15QuadraticDiscriminant 5), (v15QuadraticDiscriminant 13),
      (v15QuadraticDiscriminant 21)] : List ℕ).Nodup := by
  decide

end

end TraceEuclidean
