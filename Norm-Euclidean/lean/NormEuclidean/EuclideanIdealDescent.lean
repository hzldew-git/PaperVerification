import NormEuclidean.FractionalIdealLattice
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.FractionalIdeal.Norm

/-!
# Norm descent for Euclidean fractional ideals

Strict approximation by an actual fractional ideal gives integral ideals of
smaller norm in the adjacent ideal class. Induction proves that this one ideal
class generates the full ordinary class group.
-/

noncomputable section

namespace NormEuclidean.EuclideanIdealDescent

open scoped nonZeroDivisors NumberField

variable {K : Type*} [Field K] [NumberField K]

local instance : Module.Free ℤ (integerSubring K) := inferInstanceAs (Module.Free ℤ (𝓞 K))
local instance : Module.Finite ℤ (integerSubring K) := inferInstanceAs (Module.Finite ℤ (𝓞 K))

/-- The actual ordinary class of a nonzero fractional ideal. -/
def idealClass (I : FractionalIdeal (integerSubring K)⁰ K) (hI : I ≠ 0) :
    ClassGroup (integerSubring K) := ClassGroup.mk K (Units.mk0 I hI)

/-- Strict approximation normalized by the fractional ideal norm. -/
def IsNormEuclidean (I : FractionalIdeal (integerSubring K)⁰ K) : Prop :=
  ∀ x : K, ∃ y ∈ I, fieldAbsNorm K (x - y) < FractionalIdeal.absNorm I

theorem norm_pos (I : FractionalIdeal (integerSubring K)⁰ K) (hI : I ≠ 0) :
    0 < FractionalIdeal.absNorm I :=
  lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg I)
    (Ne.symm (FractionalIdeal.absNorm_eq_zero_iff.not.mpr hI))

theorem norm_principal (a : K) :
    FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (integerSubring K)⁰ a) =
      fieldAbsNorm K a := by
  simpa only [fieldAbsNorm] using FractionalIdeal.absNorm_span_singleton (integerSubring K) a

theorem idealClass_mul (I J : FractionalIdeal (integerSubring K)⁰ K)
    (hI : I ≠ 0) (hJ : J ≠ 0) :
    idealClass (I * J) (mul_ne_zero hI hJ) = idealClass I hI * idealClass J hJ := by
  unfold idealClass
  rw [← map_mul]
  congr 1
  exact Units.ext rfl

theorem idealClass_inv (I : FractionalIdeal (integerSubring K)⁰ K) (hI : I ≠ 0) :
    idealClass I⁻¹ (inv_ne_zero hI) = (idealClass I hI)⁻¹ := by
  unfold idealClass
  rw [← map_inv]
  congr 1
  exact Units.ext rfl

theorem idealClass_principal (a : K) (ha : a ≠ 0) :
    idealClass (FractionalIdeal.spanSingleton (integerSubring K)⁰ a)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha) = 1 := by
  apply ClassGroup.mk_eq_one_iff.mpr
  exact (FractionalIdeal.isPrincipal_iff _).mpr ⟨a, rfl⟩

theorem idealClass_congr {I J : FractionalIdeal (integerSubring K)⁰ K}
    (hI : I ≠ 0) (hJ : J ≠ 0) (h : I = J) : idealClass I hI = idealClass J hJ := by
  subst J
  rfl

theorem idealClass_integral (J : (Ideal (integerSubring K))⁰) :
    idealClass (J : Ideal (integerSubring K))
      (FractionalIdeal.coeIdeal_ne_zero.mpr (nonZeroDivisors.coe_ne_zero J)) =
      ClassGroup.mk0 J := by
  have h := ClassGroup.mk_mk0 (K := K) J
  exact h

/-- A proper integral ideal makes the inverse multiple of any nonzero ideal strictly larger. -/
theorem exists_inverse_multiple_not_mem
    (I : FractionalIdeal (integerSubring K)⁰ K) (hI : I ≠ 0)
    (J : Ideal (integerSubring K)) (hJ : J ≠ ⊥) (hJ1 : J ≠ ⊤) :
    ∃ x ∈ (J : FractionalIdeal (integerSubring K)⁰ K)⁻¹ * I, x ∉ I := by
  have hJ0 : (J : FractionalIdeal (integerSubring K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hJ
  have hle : I ≤ (J : FractionalIdeal (integerSubring K)⁰ K)⁻¹ * I := by
    have h := FractionalIdeal.inv_anti_mono hJ0 one_ne_zero
      (FractionalIdeal.coeIdeal_le_one (I := J))
    simpa only [inv_one, mul_one, mul_comm] using mul_le_mul_right h I
  have hne : I ≠ (J : FractionalIdeal (integerSubring K)⁰ K)⁻¹ * I := by
    intro h
    have hi : (1 : FractionalIdeal (integerSubring K)⁰ K) =
        (J : FractionalIdeal (integerSubring K)⁰ K)⁻¹ := by
      simpa only [mul_assoc, mul_inv_cancel₀ hI, mul_one] using
        congrArg (fun A ↦ A * I⁻¹) h
    have hj : (J : FractionalIdeal (integerSubring K)⁰ K) = 1 := by
      simpa only [inv_one, inv_inv] using congrArg Inv.inv hi.symm
    apply hJ1
    apply (FractionalIdeal.coeIdeal_inj' (S := (integerSubring K)⁰) (P := K) le_rfl).mp
    simpa only [FractionalIdeal.coeIdeal_top] using hj
  obtain ⟨x, hx, hxn⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  exact ⟨x, hx, hxn⟩

/-- The Euclidean step decreases the actual integral ideal norm and shifts the class by I. -/
theorem exists_smaller_integral_ideal
    (I : FractionalIdeal (integerSubring K)⁰ K) (hI : I ≠ 0) (hE : IsNormEuclidean I)
    (J : Ideal (integerSubring K)) (hJ : J ≠ ⊥) (hJ1 : J ≠ ⊤) :
    ∃ (B : Ideal (integerSubring K)) (hB : B ≠ ⊥), Ideal.absNorm B < Ideal.absNorm J ∧
      idealClass (B : FractionalIdeal (integerSubring K)⁰ K)
        (FractionalIdeal.coeIdeal_ne_zero.mpr hB) =
      idealClass (J : FractionalIdeal (integerSubring K)⁰ K)
        (FractionalIdeal.coeIdeal_ne_zero.mpr hJ) * (idealClass I hI)⁻¹ := by
  obtain ⟨x, hx, hxn⟩ := exists_inverse_multiple_not_mem I hI J hJ hJ1
  obtain ⟨y, hy, hsmall⟩ := hE x
  let z := x - y
  have hz0 : z ≠ 0 := by
    intro h
    exact hxn ((sub_eq_zero.mp h).symm ▸ hy)
  have hJ0 : (J : FractionalIdeal (integerSubring K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hJ
  have hle : I ≤ (J : FractionalIdeal (integerSubring K)⁰ K)⁻¹ * I := by
    have h := FractionalIdeal.inv_anti_mono hJ0 one_ne_zero
      (FractionalIdeal.coeIdeal_le_one (I := J))
    simpa only [inv_one, mul_one, mul_comm] using mul_le_mul_right h I
  have hz : z ∈ (J : FractionalIdeal (integerSubring K)⁰ K)⁻¹ * I :=
    ((J : FractionalIdeal (integerSubring K)⁰ K)⁻¹ * I).coeToSubmodule.sub_mem hx (hle hy)
  let A := FractionalIdeal.spanSingleton (integerSubring K)⁰ z *
    (J : FractionalIdeal (integerSubring K)⁰ K) * I⁻¹
  have hA0 : A ≠ 0 := mul_ne_zero
    (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hz0) hJ0) (inv_ne_zero hI)
  have hA : A ≤ 1 := by
    have h := mul_le_mul_right
      (mul_le_mul_right (FractionalIdeal.spanSingleton_le_iff_mem.mpr hz)
        (J : FractionalIdeal (integerSubring K)⁰ K)) I⁻¹
    have heq : I⁻¹ * ((J : FractionalIdeal (integerSubring K)⁰ K) *
        ((J : FractionalIdeal (integerSubring K)⁰ K)⁻¹ * I)) = 1 := by
      calc
        _ = ((J : FractionalIdeal (integerSubring K)⁰ K) *
            (J : FractionalIdeal (integerSubring K)⁰ K)⁻¹) * (I⁻¹ * I) := by ac_rfl
        _ = 1 := by rw [mul_inv_cancel₀ hJ0, inv_mul_cancel₀ hI, mul_one]
    calc
      A = I⁻¹ * ((J : FractionalIdeal (integerSubring K)⁰ K) *
          FractionalIdeal.spanSingleton (integerSubring K)⁰ z) := by dsimp [A]; ac_rfl
      _ ≤ I⁻¹ * ((J : FractionalIdeal (integerSubring K)⁰ K) *
          ((J : FractionalIdeal (integerSubring K)⁰ K)⁻¹ * I)) := h
      _ = 1 := heq
  obtain ⟨B, hB⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hA
  have hB0 : B ≠ ⊥ := FractionalIdeal.coeIdeal_ne_zero.mp (hB.symm ▸ hA0)
  refine ⟨B, hB0, ?_, ?_⟩
  · have hn : (Ideal.absNorm B : ℚ) =
        fieldAbsNorm K z * (Ideal.absNorm J : ℚ) / FractionalIdeal.absNorm I := by
      rw [← FractionalIdeal.coeIdeal_absNorm (K := K) B, hB]
      simp only [A, map_mul, map_inv₀, norm_principal, FractionalIdeal.coeIdeal_absNorm,
        div_eq_mul_inv]
    have hnJ : 0 < (Ideal.absNorm J : ℚ) := by
      exact_mod_cast (Ideal.absNorm_pos_of_nonZeroDivisors
        (⟨J, mem_nonZeroDivisors_of_ne_zero hJ⟩ : (Ideal (integerSubring K))⁰))
    have hlt : (Ideal.absNorm B : ℚ) < (Ideal.absNorm J : ℚ) := by
      rw [hn, div_lt_iff₀ (norm_pos I hI)]
      nlinarith
    exact_mod_cast hlt
  · calc
      idealClass (B : FractionalIdeal (integerSubring K)⁰ K) _ = idealClass A hA0 :=
        idealClass_congr _ _ hB
      _ = _ := by
        change idealClass (FractionalIdeal.spanSingleton (integerSubring K)⁰ z *
          (J : FractionalIdeal (integerSubring K)⁰ K) * I⁻¹) hA0 = _
        rw [idealClass_mul _ _
            (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hz0) hJ0)
            (inv_ne_zero hI),
          idealClass_mul _ _ (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hz0) hJ0,
          idealClass_inv I hI, idealClass_principal z hz0, one_mul]

end NormEuclidean.EuclideanIdealDescent
