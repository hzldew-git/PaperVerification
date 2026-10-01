import TraceEuclidean.OdlyzkoKernel
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients

/-!
# Finite Odlyzko prime-ideal corrections

The source's correction is

`2 * sum_P sum_m log(N P) * F(log((N P)^m)) / (N P)^(m/2)`.

This file realizes its individual summands and canonical finite partial sums
over prime ideals of bounded norm and positive exponents.  It proves their
nonnegativity from the kernel theorem in `OdlyzkoKernel`.  Identification
of the analytic infinite sum with these finite partial sums is a later layer.
-/

namespace TraceEuclidean

noncomputable section

open IsDedekindDomain
open scoped NumberField

variable {K : Type*} [Field K] [NumberField K]

private theorem odlyzkoPrime_absNorm_one_lt
    (P : HeightOneSpectrum (𝓞 K)) : 1 < Ideal.absNorm P.asIdeal := by
  by_contra! h
  apply Ideal.IsPrime.ne_top P.isPrime
  rw [← Ideal.absNorm_eq_one_iff]
  have hpos : 0 < Ideal.absNorm P.asIdeal := by
    exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot)
  omega

/-- The summand attached to a nonzero prime ideal `P` and exponent `m` in
Odlyzko's unconditional prime-ideal correction. -/
def odlyzkoPrimeTerm (P : HeightOneSpectrum (𝓞 K)) (m : ℕ) : ℝ :=
  let q : ℝ := Ideal.absNorm P.asIdeal
  2 * Real.log q * odlyzkoF4 (Real.log (q ^ m)) /
    q ^ ((m : ℝ) / 2)

/-- Every prime-ideal summand is nonnegative.  The statement is also valid at
`m = 0`; the source sum below uses only the positive exponents `m + 1`. -/
theorem odlyzkoPrimeTerm_nonneg (P : HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    0 ≤ odlyzkoPrimeTerm P m := by
  have hqNat : 1 < Ideal.absNorm P.asIdeal := odlyzkoPrime_absNorm_one_lt P
  have hq : (0 : ℝ) < Ideal.absNorm P.asIdeal := by
    exact_mod_cast (Nat.zero_lt_one.trans hqNat)
  have hqOne : (1 : ℝ) ≤ Ideal.absNorm P.asIdeal := by exact_mod_cast hqNat.le
  unfold odlyzkoPrimeTerm
  dsimp only
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) (Real.log_nonneg hqOne))
      (odlyzkoF4_nonneg _))
    (Real.rpow_nonneg hq.le _)

/-- A kernel-supported prime term vanishes once its logarithmic argument is
strictly larger than the support radius eight. -/
theorem odlyzkoPrimeTerm_eq_zero_of_eight_lt_log
    (P : HeightOneSpectrum (𝓞 K)) (m : ℕ)
    (hlog : 8 < Real.log ((Ideal.absNorm P.asIdeal : ℝ) ^ m)) :
    odlyzkoPrimeTerm P m = 0 := by
  have habs : 8 < |Real.log ((Ideal.absNorm P.asIdeal : ℝ) ^ m)| :=
    hlog.trans_le (le_abs_self _)
  unfold odlyzkoPrimeTerm
  dsimp only
  rw [odlyzkoF4_eq_zero_of_eight_lt_abs habs, mul_zero, zero_div]

private theorem odlyzko_exp_eight_lt_4096 : Real.exp 8 < 4096 := by
  have hpow := pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_nonneg 1)
    (by norm_num : (8 : ℕ) ≠ 0)
  rw [← Real.exp_nat_mul] at hpow
  norm_num at hpow ⊢
  exact hpow.trans (by norm_num)

/-- Since every prime-ideal norm is at least two, the support radius eight
forces every summand with exponent at least twelve to vanish. -/
theorem odlyzkoPrimeTerm_eq_zero_of_twelve_le
    (P : HeightOneSpectrum (𝓞 K)) (m : ℕ) (hm : 12 ≤ m) :
    odlyzkoPrimeTerm P m = 0 := by
  have hqNat : 1 < Ideal.absNorm P.asIdeal := odlyzkoPrime_absNorm_one_lt P
  have hqTwoNat : 2 ≤ Ideal.absNorm P.asIdeal := by omega
  have hqTwo : (2 : ℝ) ≤ Ideal.absNorm P.asIdeal := by exact_mod_cast hqTwoNat
  have hpowBase : (2 : ℝ) ^ m ≤ (Ideal.absNorm P.asIdeal : ℝ) ^ m :=
    pow_le_pow_left₀ (by norm_num) hqTwo m
  have hpowExponent : (2 : ℝ) ^ 12 ≤ (2 : ℝ) ^ m :=
    pow_le_pow_right₀ (by norm_num) hm
  have h4096 : (4096 : ℝ) ≤ (Ideal.absNorm P.asIdeal : ℝ) ^ m := by
    calc
      (4096 : ℝ) = (2 : ℝ) ^ 12 := by norm_num
      _ ≤ (2 : ℝ) ^ m := hpowExponent
      _ ≤ (Ideal.absNorm P.asIdeal : ℝ) ^ m := hpowBase
  apply odlyzkoPrimeTerm_eq_zero_of_eight_lt_log
  apply (Real.lt_log_iff_exp_lt (by positivity)).2
  exact odlyzko_exp_eight_lt_4096.trans_le h4096

/-- A positive-exponent summand also vanishes once the prime-ideal norm is
at least 4096. -/
theorem odlyzkoPrimeTerm_eq_zero_of_absNorm_ge_4096
    (P : HeightOneSpectrum (𝓞 K)) (m : ℕ) (hm : 1 ≤ m)
    (hqNat : 4096 ≤ Ideal.absNorm P.asIdeal) :
    odlyzkoPrimeTerm P m = 0 := by
  have hqOne : (1 : ℝ) ≤ Ideal.absNorm P.asIdeal := by
    exact_mod_cast hqNat.trans' (by norm_num)
  have hq4096 : (4096 : ℝ) ≤ Ideal.absNorm P.asIdeal := by
    exact_mod_cast hqNat
  have hpow : (Ideal.absNorm P.asIdeal : ℝ) ≤
      (Ideal.absNorm P.asIdeal : ℝ) ^ m := by
    simpa only [pow_one] using pow_le_pow_right₀ hqOne hm
  apply odlyzkoPrimeTerm_eq_zero_of_eight_lt_log
  apply (Real.lt_log_iff_exp_lt (by positivity)).2
  exact odlyzko_exp_eight_lt_4096.trans_le (hq4096.trans hpow)

/-- The finite set of nonzero prime ideals whose absolute norm is at most
`N`.  Finiteness is supplied by the number-field ideal theory in mathlib. -/
def odlyzkoPrimePlacesUpTo (K : Type*) [Field K] [NumberField K] (N : ℕ) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le
    (R := 𝓞 K) N).toFinset

@[simp] theorem odlyzkoPrimePlacesUpTo_mem
    (P : HeightOneSpectrum (𝓞 K)) (N : ℕ) :
    P ∈ odlyzkoPrimePlacesUpTo K N ↔ Ideal.absNorm P.asIdeal ≤ N := by
  simp [odlyzkoPrimePlacesUpTo]

/-- The exact finite partial correction over prime ideals of norm at most
`N` and exponents `1, ..., M`. -/
def odlyzkoPrimeCorrectionPartial
    (K : Type*) [Field K] [NumberField K] (N M : ℕ) : ℝ :=
  ∑ P ∈ odlyzkoPrimePlacesUpTo K N,
    ∑ j ∈ Finset.range M, odlyzkoPrimeTerm P (j + 1)

/-- Every finite Odlyzko prime-ideal correction is nonnegative. -/
theorem odlyzkoPrimeCorrectionPartial_nonneg
    (K : Type*) [Field K] [NumberField K] (N M : ℕ) :
    0 ≤ odlyzkoPrimeCorrectionPartial K N M := by
  unfold odlyzkoPrimeCorrectionPartial
  exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
    odlyzkoPrimeTerm_nonneg _ _

/-- Enlarging the exponent cutoff can only increase the finite correction. -/
theorem odlyzkoPrimeCorrectionPartial_mono_exponent
    (K : Type*) [Field K] [NumberField K] (N : ℕ) :
    Monotone (odlyzkoPrimeCorrectionPartial K N) := by
  intro M₁ M₂ hM
  unfold odlyzkoPrimeCorrectionPartial
  apply Finset.sum_le_sum
  intro P hP
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hM)
  intro m _ _
  exact odlyzkoPrimeTerm_nonneg P (m + 1)

/-- Once the cutoff reaches eleven, enlarging it adds only terms with
exponent at least twelve, and hence does not change the correction. -/
theorem odlyzkoPrimeCorrectionPartial_eq_eleven_of_le
    (K : Type*) [Field K] [NumberField K] (N M : ℕ) (hM : 11 ≤ M) :
    odlyzkoPrimeCorrectionPartial K N M =
      odlyzkoPrimeCorrectionPartial K N 11 := by
  unfold odlyzkoPrimeCorrectionPartial
  apply Finset.sum_congr rfl
  intro P _
  exact (Finset.sum_subset (Finset.range_mono hM) (by
    intro j _ hjNot
    have hj : 11 ≤ j := by
      simpa [Finset.mem_range, not_lt] using hjNot
    exact odlyzkoPrimeTerm_eq_zero_of_twelve_le P (j + 1) (by omega))).symm

/-- Once the norm cutoff reaches 4095, enlarging it adds only prime ideals
whose positive-exponent summands vanish. -/
theorem odlyzkoPrimeCorrectionPartial_eq_4095_of_le
    (K : Type*) [Field K] [NumberField K] (N M : ℕ) (hN : 4095 ≤ N) :
    odlyzkoPrimeCorrectionPartial K N M =
      odlyzkoPrimeCorrectionPartial K 4095 M := by
  unfold odlyzkoPrimeCorrectionPartial
  exact (Finset.sum_subset (by
    intro P hP
    rw [odlyzkoPrimePlacesUpTo_mem] at hP ⊢
    omega) (by
    intro P _ hPNot
    have hq : 4096 ≤ Ideal.absNorm P.asIdeal := by
      rw [odlyzkoPrimePlacesUpTo_mem] at hPNot
      omega
    apply Finset.sum_eq_zero
    intro j _
    exact odlyzkoPrimeTerm_eq_zero_of_absNorm_ge_4096
      P (j + 1) (by omega) hq)).symm

/-- The source's complete prime-ideal correction, indexed over all nonzero
prime ideals and all positive exponents. -/
def odlyzkoPrimeCorrection (K : Type*) [Field K] [NumberField K] : ℝ :=
  ∑' p : HeightOneSpectrum (𝓞 K) × ℕ,
    odlyzkoPrimeTerm p.1 (p.2 + 1)

/-- Compact support makes the apparently infinite prime-ideal correction an
exact finite sum: norms at most 4095 and exponents at most eleven suffice. -/
theorem odlyzkoPrimeCorrection_eq_finite
    (K : Type*) [Field K] [NumberField K] :
    odlyzkoPrimeCorrection K =
      odlyzkoPrimeCorrectionPartial K 4095 11 := by
  unfold odlyzkoPrimeCorrection
  rw [tsum_eq_sum (s :=
    odlyzkoPrimePlacesUpTo K 4095 ×ˢ Finset.range 11) (by
      intro p hp
      by_cases hP : p.1 ∈ odlyzkoPrimePlacesUpTo K 4095
      · have hjNot : p.2 ∉ Finset.range 11 := by
          intro hj
          exact hp (Finset.mem_product.mpr ⟨hP, hj⟩)
        apply odlyzkoPrimeTerm_eq_zero_of_twelve_le
        simp only [Finset.mem_range, not_lt] at hjNot
        omega
      · have hq : 4096 ≤ Ideal.absNorm p.1.asIdeal := by
          rw [odlyzkoPrimePlacesUpTo_mem] at hP
          omega
        exact odlyzkoPrimeTerm_eq_zero_of_absNorm_ge_4096
          p.1 (p.2 + 1) (by omega) hq)]
  rw [Finset.sum_product]
  rfl

/-- The full prime-ideal correction is nonnegative. -/
theorem odlyzkoPrimeCorrection_nonneg
    (K : Type*) [Field K] [NumberField K] :
    0 ≤ odlyzkoPrimeCorrection K := by
  rw [odlyzkoPrimeCorrection_eq_finite]
  exact odlyzkoPrimeCorrectionPartial_nonneg K 4095 11

end

end TraceEuclidean
