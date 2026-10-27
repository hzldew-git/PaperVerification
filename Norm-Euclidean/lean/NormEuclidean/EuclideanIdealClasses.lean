import NormEuclidean.EuclideanIdealDescent
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# A norm-Euclidean ideal class generates the ordinary class group

Induction on the norm of an actual nonzero integral ideal closes Lenstra's
generator conclusion. If the generator has square one, the field class number
divides two and is two precisely when that ideal is nonprincipal.
-/

noncomputable section

namespace NormEuclidean.EuclideanIdealDescent

open scoped NumberField nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

local instance : Module.Free ℤ (integerSubring K) := inferInstanceAs (Module.Free ℤ (𝓞 K))
local instance : Module.Finite ℤ (integerSubring K) := inferInstanceAs (Module.Finite ℤ (𝓞 K))
local instance : Fintype (ClassGroup (integerSubring K)) :=
  inferInstanceAs (Fintype (ClassGroup (𝓞 K)))

/-- Every ordinary ideal class is an integral power of the actual norm-Euclidean ideal class. -/
theorem class_mem_zpowers (I : FractionalIdeal (integerSubring K)⁰ K)
    (hI : I ≠ 0) (hE : IsNormEuclidean I) :
    ∀ C : ClassGroup (integerSubring K), C ∈ Subgroup.zpowers (idealClass I hI) := by
  have haux : ∀ n : ℕ, ∀ (J : Ideal (integerSubring K)) (hJ : J ≠ ⊥),
      Ideal.absNorm J = n →
        idealClass (J : FractionalIdeal (integerSubring K)⁰ K)
          (FractionalIdeal.coeIdeal_ne_zero.mpr hJ) ∈ Subgroup.zpowers (idealClass I hI) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro J hJ hnorm
      by_cases hJ1 : J = ⊤
      · have hc : idealClass (J : FractionalIdeal (integerSubring K)⁰ K)
            (FractionalIdeal.coeIdeal_ne_zero.mpr hJ) = 1 := by
          apply ClassGroup.mk_eq_one_iff.mpr
          exact (FractionalIdeal.isPrincipal_iff _).mpr ⟨1, by simp [hJ1]⟩
        rw [hc]
        exact Subgroup.one_mem _
      · obtain ⟨B, hB, hsmall, hclass⟩ := exists_smaller_integral_ideal I hI hE J hJ hJ1
        have hBmem := ih (Ideal.absNorm B) (by omega) B hB rfl
        have hprod : idealClass (J : FractionalIdeal (integerSubring K)⁰ K)
            (FractionalIdeal.coeIdeal_ne_zero.mpr hJ) =
            idealClass (B : FractionalIdeal (integerSubring K)⁰ K)
              (FractionalIdeal.coeIdeal_ne_zero.mpr hB) * idealClass I hI := by
          rw [hclass, mul_assoc, inv_mul_cancel, mul_one]
        rw [hprod]
        exact Subgroup.mul_mem _ hBmem (Subgroup.mem_zpowers _)
  intro C
  obtain ⟨J, rfl⟩ := ClassGroup.mk0_surjective C
  simpa only [idealClass_integral] using haux (Ideal.absNorm (J : Ideal (integerSubring K)))
    J (nonZeroDivisors.coe_ne_zero J) rfl

/-- The field class number is exactly the order of the norm-Euclidean ideal class. -/
theorem classNumber_eq_orderOf (I : FractionalIdeal (integerSubring K)⁰ K)
    (hI : I ≠ 0) (hE : IsNormEuclidean I) :
    NumberField.classNumber K = orderOf (idealClass I hI) := by
  have h := orderOf_eq_card_of_forall_mem_zpowers (class_mem_zpowers I hI hE)
  calc
    NumberField.classNumber K = Fintype.card (ClassGroup (integerSubring K)) :=
      Fintype.card_congr (Equiv.refl _)
    _ = orderOf (idealClass I hI) := by
      simpa only [Nat.card_eq_fintype_card] using h.symm

/-- The generator's square relation gives divisibility of the actual field class number by two. -/
theorem classNumber_dvd_two_of_sq (I : FractionalIdeal (integerSubring K)⁰ K)
    (hI : I ≠ 0) (hE : IsNormEuclidean I) (hsq : idealClass I hI ^ 2 = 1) :
    NumberField.classNumber K ∣ 2 := by
  rw [classNumber_eq_orderOf I hI hE]
  exact orderOf_dvd_of_pow_eq_one hsq

/-- The class number is one precisely when the Euclidean ideal is principal. -/
theorem classNumber_eq_one_iff_isPrincipal (I : FractionalIdeal (integerSubring K)⁰ K)
    (hI : I ≠ 0) (hE : IsNormEuclidean I) :
    NumberField.classNumber K = 1 ↔ (I : Submodule (integerSubring K) K).IsPrincipal := by
  rw [classNumber_eq_orderOf I hI hE, orderOf_eq_one_iff]
  exact ClassGroup.mk_eq_one_iff

/-- The exceptional field class number is exactly the nonprincipal unary ideal case. -/
theorem classNumber_eq_two_iff_not_isPrincipal (I : FractionalIdeal (integerSubring K)⁰ K)
    (hI : I ≠ 0) (hE : IsNormEuclidean I) (hsq : idealClass I hI ^ 2 = 1) :
    NumberField.classNumber K = 2 ↔ ¬(I : Submodule (integerSubring K) K).IsPrincipal := by
  have hbound := Nat.le_of_dvd (by decide : 0 < 2) (classNumber_dvd_two_of_sq I hI hE hsq)
  have hpos := NumberField.classNumber_pos K
  have hone := classNumber_eq_one_iff_isPrincipal I hI hE
  constructor
  · intro htwo hprincipal
    have h := hone.mpr hprincipal
    omega
  · intro hnonprincipal
    have hne : NumberField.classNumber K ≠ 1 := fun h ↦ hnonprincipal (hone.mp h)
    omega

end NormEuclidean.EuclideanIdealDescent
