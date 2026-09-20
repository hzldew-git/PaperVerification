import TraceEuclidean.V15IndexOne
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.RingTheory.FractionalIdeal.Inverse

/-!
The integral quotient ideal `β𝓞_F / I` for a basis vector `β ∈ I`. Its norm is
the positive integer used in the trace/norm sieve, and norm one forces `I`
to be principal. This proof applies to every nonzero fractional ideal.
-/

namespace TraceEuclidean

open scoped NumberField nonZeroDivisors

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

theorem v15_ideal_quotient_norm
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (hI : I ≠ 0) {β : F} (hβ : β ∈ I) (hβ0 : β ≠ 0) :
    ∃ J : Ideal (𝓞 F),
      0 < Ideal.absNorm J ∧
      (FractionalIdeal.absNorm I) * (Ideal.absNorm J : ℚ) =
        |Algebra.norm ℚ β| ∧
      (Ideal.absNorm J = 1 →
        I = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) β) := by
  have hspan : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) β ≤ I := by
    intro x hx
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_spanSingleton _).mp hx
    rw [← hr]
    exact I.coeToSubmodule.smul_mem r hβ
  have hquot :
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) β / I ≤ 1 := by
    rw [← div_self hI]
    apply (FractionalIdeal.le_div_iff_mul_le hI).2
    simpa [div_mul_cancel₀ _ hI] using hspan
  obtain ⟨J, hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hquot
  have hmul : (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * I =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) β := by
    rw [hJ]
    exact div_mul_cancel₀ _ hI
  have hJ0 : J ≠ ⊥ := by
    intro hzero
    rw [hzero] at hmul
    simp only [FractionalIdeal.coeIdeal_bot, zero_mul] at hmul
    have := (FractionalIdeal.spanSingleton_eq_zero_iff).mp hmul.symm
    exact hβ0 this
  have hk : 0 < Ideal.absNorm J := by
    exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ0)
  have hspanNorm :
      FractionalIdeal.absNorm
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) β) =
          |Algebra.norm ℚ β| :=
    FractionalIdeal.absNorm_span_singleton (K := F) (𝓞 F) β
  have hJnorm :
      FractionalIdeal.absNorm
        (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
          (Ideal.absNorm J : ℚ) :=
    FractionalIdeal.coeIdeal_absNorm (K := F) J
  have hnorm : FractionalIdeal.absNorm I * (Ideal.absNorm J : ℚ) =
      |Algebra.norm ℚ β| := by
    rw [← hJnorm, mul_comm, ← map_mul, hmul, hspanNorm]
  refine ⟨J, hk, hnorm, ?_⟩
  intro hOne
  have htop : J = ⊤ := Ideal.absNorm_eq_one_iff.mp hOne
  rw [htop] at hmul
  simpa using hmul

def v15ValueFractionalIdeal
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (α : F) :
    FractionalIdeal (nonZeroDivisors (𝓞 F)) F :=
  FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) α * I ^ 2

/-- Every product value `αxy` is an algebraic integer when `αI²` is an
integral ideal. This applies to the two chosen ideal basis vectors as well. -/
theorem v15_value_integral_of_ideal_integral
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (α : F)
    (hintegral : v15ValueFractionalIdeal I α ≤ 1)
    {x y : F} (hx : x ∈ I) (hy : y ∈ I) :
    IsIntegral ℤ (α * x * y) := by
  have hxy : x * y ∈ I ^ 2 := by
    rw [pow_two]
    exact FractionalIdeal.mul_mem_mul hx hy
  have hvalue : α * (x * y) ∈ v15ValueFractionalIdeal I α := by
    unfold v15ValueFractionalIdeal
    exact FractionalIdeal.mul_mem_mul
      (FractionalIdeal.mem_spanSingleton_self _ α) hxy
  have hone : α * (x * y) ∈
      (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
    hintegral hvalue
  obtain ⟨z, hz⟩ := (FractionalIdeal.mem_one_iff _).mp hone
  have hzint : IsIntegral ℤ (α * (x * y)) := hz ▸ z.isIntegral_coe
  simpa only [mul_assoc] using hzint

/-- Integrality of `αI²` makes its absolute norm a positive integer and
gives the exact multiplicative norm identity used by the nine-row sieve. -/
theorem v15_value_ideal_positive_norm
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (hI : I ≠ 0) (α : F) (hα : α ≠ 0)
    (hintegral : v15ValueFractionalIdeal I α ≤ 1) :
    ∃ n : ℕ, 0 < n ∧
      (n : ℚ) = |Algebra.norm ℚ α| * (FractionalIdeal.absNorm I) ^ 2 := by
  obtain ⟨J, hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hintegral
  have hnorm : FractionalIdeal.absNorm (v15ValueFractionalIdeal I α) =
      |Algebra.norm ℚ α| * (FractionalIdeal.absNorm I) ^ 2 := by
    unfold v15ValueFractionalIdeal
    rw [map_mul, map_pow,
      FractionalIdeal.absNorm_span_singleton (K := F) (𝓞 F) α]
  have hInorm : FractionalIdeal.absNorm I ≠ 0 :=
    (FractionalIdeal.absNorm_eq_zero_iff).not.mpr hI
  have hαnorm : Algebra.norm ℚ α ≠ 0 := by
    exact (Algebra.norm_ne_zero_iff).mpr hα
  have hJnorm : FractionalIdeal.absNorm
      (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        (Ideal.absNorm J : ℚ) :=
    FractionalIdeal.coeIdeal_absNorm (K := F) J
  have hJ0 : J ≠ ⊥ := by
    intro hzero
    have hnorm0 : FractionalIdeal.absNorm (v15ValueFractionalIdeal I α) = 0 := by
      rw [← hJ, hzero]
      simp
    rw [hnorm] at hnorm0
    exact (mul_ne_zero (abs_ne_zero.mpr hαnorm) (pow_ne_zero 2 hInorm)) hnorm0
  refine ⟨Ideal.absNorm J,
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ0), ?_⟩
  rw [← hJnorm, hJ]
  exact hnorm

/-- The norm-index identity for each nonzero ideal vector. The integer `k`
is the norm of the integral quotient ideal `β𝓞_F / I`; its value one forces
the original ideal to be generated by `β`. -/
theorem v15_ideal_vector_norm_index
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (hI : I ≠ 0) (α : F) (hαnorm : 0 < Algebra.norm ℚ α)
    (n : ℕ)
    (hn : (n : ℚ) = |Algebra.norm ℚ α| * (FractionalIdeal.absNorm I) ^ 2)
    {β : F} (hβ : β ∈ I) (hβ0 : β ≠ 0) :
    ∃ k : ℕ, 0 < k ∧
      Algebra.norm ℚ (α * β ^ 2) = (n : ℚ) * (k : ℚ) ^ 2 ∧
      (k = 1 →
        I = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) β) := by
  obtain ⟨J, hk, hβnorm, hprincipal⟩ :=
    v15_ideal_quotient_norm I hI hβ hβ0
  refine ⟨Ideal.absNorm J, hk, ?_, hprincipal⟩
  calc
    Algebra.norm ℚ (α * β ^ 2) =
        Algebra.norm ℚ α * (Algebra.norm ℚ β) ^ 2 := by
          rw [map_mul, map_pow]
    _ = |Algebra.norm ℚ α| * |Algebra.norm ℚ β| ^ 2 := by
          rw [abs_of_pos hαnorm, sq_abs]
    _ = |Algebra.norm ℚ α| *
        (FractionalIdeal.absNorm I * (Ideal.absNorm J : ℚ)) ^ 2 := by
          rw [hβnorm]
    _ = (n : ℚ) * (Ideal.absNorm J : ℚ) ^ 2 := by
          rw [hn]
          ring

end

end TraceEuclidean
