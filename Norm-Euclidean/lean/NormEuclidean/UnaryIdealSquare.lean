import NormEuclidean.UnaryIdealNorm
import NormEuclidean.UnconditionalClassNumber

/-!
# The square of the unary ideal class is trivial

Every prime dividing the actual integral product (c) I^2 has a nonzero
isotropic vector in the original ideal lattice modulo that prime. The proved
Euclidean content descent makes each such prime principal. Factorization then
makes the product principal and proves [I]^2=1.
-/

noncomputable section

namespace NormEuclidean.UnaryIdealSquare

open scoped NumberField nonZeroDivisors
open EuclideanIdealDescent UnaryIdealNorm

variable {K : Type*} [Field K] [NumberField K]

/-- Invertibility gives a nonzero residue vector in every ideal module, without a basis. -/
theorem exists_not_prime_multiple (I : FractionalIdeal (integerSubring K)⁰ K)
    (hI : I ≠ 0) (p : Ideal (integerSubring K)) (hp : p ≠ ⊤) :
    ∃ x ∈ I, x ∉ (p : FractionalIdeal (integerSubring K)⁰ K) * I := by
  have hle : (p : FractionalIdeal (integerSubring K)⁰ K) * I ≤ I := by
    simpa only [mul_one, mul_comm] using
      mul_le_mul_right (FractionalIdeal.coeIdeal_le_one (I := p)) I
  have hne : (p : FractionalIdeal (integerSubring K)⁰ K) * I ≠ I := by
    intro h
    have heq : (p : FractionalIdeal (integerSubring K)⁰ K) = 1 := by
      simpa only [mul_assoc, mul_inv_cancel₀ hI, mul_one] using
        congrArg (fun A ↦ A * I⁻¹) h
    apply hp
    apply (FractionalIdeal.coeIdeal_inj' (S := (integerSubring K)⁰) (P := K) le_rfl).mp
    simpa only [FractionalIdeal.coeIdeal_top] using heq
  exact SetLike.exists_of_lt (lt_of_le_of_ne hle hne)

/-- Every prime divisor of the unary product ideal is principal under the original hypothesis. -/
theorem prime_isPrincipal (M : UnaryIdealModel.Model K)
    (hE : HasNumberFieldApproximation (unaryForm K M.coefficient) M.lattice.carrier)
    (p : Ideal (integerSubring K)) (hp : p.IsMaximal) (hp0 : p ≠ ⊥)
    (hle : productIdeal M ≤ (p : FractionalIdeal (integerSubring K)⁰ K)) :
    p.IsPrincipal := by
  obtain ⟨x, hx, hxp⟩ := exists_not_prime_multiple M.ideal M.ideal_ne_zero p hp.ne_top
  have hnmem : x ∉ ((p : FractionalIdeal (integerSubring K)⁰ K) :
      Submodule (integerSubring K) K) • M.lattice.carrier := by
    change x ∉ (p : FractionalIdeal (integerSubring K)⁰ K).coeToSubmodule *
      M.ideal.coeToSubmodule
    rw [← FractionalIdeal.coe_mul]
    exact hxp
  have hvalue : unaryForm K M.coefficient x ∈ productIdeal M := by
    rw [unaryForm_apply]
    apply FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _)
    simpa only [pow_two] using FractionalIdeal.mul_mem_mul hx hx
  exact prime_isPrincipal_of_isotropic_residue M.lattice M.anisotropic hE p hp hp0
    x hx hnmem (hle hvalue)

/-- The actual integral ideal (c) I^2 is principal, including all ramified and dyadic factors. -/
theorem productIdeal_isPrincipal (M : UnaryIdealModel.Model K)
    (hE : HasNumberFieldApproximation (unaryForm K M.coefficient) M.lattice.carrier) :
    (productIdeal M : Submodule (integerSubring K) K).IsPrincipal := by
  obtain ⟨B, hB⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp (productIdeal_le_one M)
  have hprincipal : B.IsPrincipal := ideal_isPrincipal_of_prime_divisors B (by
    intro p hp hpB
    apply prime_isPrincipal M hE p ((Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero) hp.ne_zero
    rw [← hB]
    exact (FractionalIdeal.coeIdeal_le_coeIdeal K).mpr (Ideal.dvd_iff_le.mp hpB))
  obtain ⟨a, ha⟩ := hprincipal.principal
  apply (FractionalIdeal.isPrincipal_iff _).mpr
  refine ⟨(a : K), ?_⟩
  rw [← hB, ha, FractionalIdeal.coeIdeal_span_singleton]
  rfl

/-- The retained ideal class has exponent dividing two, proved from the original unary property. -/
theorem idealClass_sq (M : UnaryIdealModel.Model K)
    (hE : HasNumberFieldApproximation (unaryForm K M.coefficient) M.lattice.carrier) :
    idealClass M.ideal M.ideal_ne_zero ^ 2 = 1 := by
  have hpow : idealClass (M.ideal ^ 2) (pow_ne_zero _ M.ideal_ne_zero) =
      idealClass M.ideal M.ideal_ne_zero ^ 2 := by
    unfold idealClass
    rw [← map_pow]
    congr 1
    exact Units.ext rfl
  have hproduct : idealClass (productIdeal M) (productIdeal_ne_zero M) = 1 :=
    ClassGroup.mk_eq_one_iff.mpr (productIdeal_isPrincipal M hE)
  have h := idealClass_mul
    (FractionalIdeal.spanSingleton (integerSubring K)⁰ M.coefficient) (M.ideal ^ 2)
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr M.coefficient_ne_zero)
    (pow_ne_zero _ M.ideal_ne_zero)
  rw [idealClass_principal _ M.coefficient_ne_zero, one_mul, hpow] at h
  exact h.symm.trans hproduct

end NormEuclidean.UnaryIdealSquare
