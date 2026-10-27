import NormEuclidean.UnaryIdealModel
import NormEuclidean.EuclideanIdealDescent

/-!
# The norm-Euclidean ideal extracted from an integral unary lattice

Integrality of c*x^2 implies integrality of every c*x*y: its square is the
product of two integral values, and the number ring is integrally closed.
Consequently (c) I^2 is an actual nonzero integral ideal. Its norm is at least
one, which turns the original quadratic approximation into ideal approximation.
-/

noncomputable section

namespace NormEuclidean.UnaryIdealNorm

open scoped NumberField nonZeroDivisors
open EuclideanIdealDescent

variable {K : Type*} [Field K] [NumberField K]

local instance : Module.Free ℤ (integerSubring K) := inferInstanceAs (Module.Free ℤ (𝓞 K))
local instance : Module.Finite ℤ (integerSubring K) := inferInstanceAs (Module.Finite ℤ (𝓞 K))

/-- An element of the fraction field whose square is integral is itself integral. -/
theorem mem_integerSubring_of_sq_mem (x : K) (hx : x ^ 2 ∈ integerSubring K) :
    x ∈ integerSubring K := by
  have hi : IsIntegral (integerSubring K) (x ^ 2) :=
    IsIntegrallyClosed.isIntegral_iff.mpr ⟨⟨x ^ 2, hx⟩, rfl⟩
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hi.of_pow (by decide))
  exact hr ▸ r.property

/-- The coefficient times any product of two ideal elements is integral, also above two. -/
theorem mixed_value_integral (M : UnaryIdealModel.Model K) (x y : K)
    (hx : x ∈ M.ideal) (hy : y ∈ M.ideal) :
    M.coefficient * x * y ∈ integerSubring K := by
  apply mem_integerSubring_of_sq_mem
  have h := (integerSubring K).mul_mem (M.integral x hx) (M.integral y hy)
  convert h using 1
  ring

/-- The fractional ideal (c) I^2, constructed without an integral basis. -/
def productIdeal (M : UnaryIdealModel.Model K) : FractionalIdeal (integerSubring K)⁰ K :=
  FractionalIdeal.spanSingleton (integerSubring K)⁰ M.coefficient * M.ideal ^ 2

theorem productIdeal_ne_zero (M : UnaryIdealModel.Model K) : productIdeal M ≠ 0 :=
  mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr M.coefficient_ne_zero)
    (pow_ne_zero _ M.ideal_ne_zero)

/-- The actual ideal product (c) I^2 is integral; dyadic primes are included. -/
theorem productIdeal_le_one (M : UnaryIdealModel.Model K) : productIdeal M ≤ 1 := by
  rw [productIdeal, pow_two, ← mul_assoc]
  apply FractionalIdeal.mul_le.mpr
  intro a ha y hy
  obtain ⟨x, hx, rfl⟩ := FractionalIdeal.mem_singleton_mul.mp ha
  exact (FractionalIdealLattice.mem_one_iff _).mpr (mixed_value_integral M x y hx hy)

/-- The coefficient norm times the square ideal norm is bounded below by one. -/
theorem one_le_coefficient_norm_mul_ideal_norm_sq (M : UnaryIdealModel.Model K) :
    1 ≤ fieldAbsNorm K M.coefficient * (FractionalIdeal.absNorm M.ideal) ^ 2 := by
  obtain ⟨B, hB⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp (productIdeal_le_one M)
  have hB0 : B ≠ ⊥ := FractionalIdeal.coeIdeal_ne_zero.mp
    (hB.symm ▸ productIdeal_ne_zero M)
  have hpos := Ideal.absNorm_pos_of_nonZeroDivisors
    (⟨B, mem_nonZeroDivisors_of_ne_zero hB0⟩ : (Ideal (integerSubring K))⁰)
  have hnorm : (Ideal.absNorm B : ℚ) =
      fieldAbsNorm K M.coefficient * (FractionalIdeal.absNorm M.ideal) ^ 2 := by
    rw [← FractionalIdeal.coeIdeal_absNorm (K := K) B, hB]
    simp only [productIdeal, map_mul, map_pow, norm_principal]
  rw [← hnorm]
  exact_mod_cast hpos

/-- The original norm-Euclidean unary hypothesis gives Lenstra's strict ideal-norm condition. -/
theorem normEuclidean_ideal (M : UnaryIdealModel.Model K)
    (hE : HasNumberFieldApproximation (unaryForm K M.coefficient) M.lattice.carrier) :
    EuclideanIdealDescent.IsNormEuclidean M.ideal := by
  intro x
  obtain ⟨y, hy, hsmall⟩ := hE x
  refine ⟨y, hy, ?_⟩
  have hge := one_le_coefficient_norm_mul_ideal_norm_sq M
  have hN := norm_pos M.ideal M.ideal_ne_zero
  change fieldAbsNorm K (unaryForm K M.coefficient (x - y)) < 1 at hsmall
  rw [unaryForm_apply, fieldAbsNorm_mul, fieldAbsNorm_sq] at hsmall
  by_contra h
  have hle := le_of_not_gt h
  have hsq : (FractionalIdeal.absNorm M.ideal) ^ 2 ≤ (fieldAbsNorm K (x - y)) ^ 2 :=
    (sq_le_sq₀ hN.le (fieldAbsNorm_nonneg K _)).mpr hle
  have hmul := mul_le_mul_of_nonneg_left hsq (fieldAbsNorm_nonneg K M.coefficient)
  exact (not_lt_of_ge (hge.trans hmul)) hsmall

end NormEuclidean.UnaryIdealNorm
