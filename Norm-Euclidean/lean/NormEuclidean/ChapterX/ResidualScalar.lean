import NormEuclidean.ChapterX.ScalarIntegralApproximation
import NormEuclidean.ChapterX.ResidualCorrection

/-!
# Actual congruence and integrality of the residual scalar in 104:3

The 104:1 multiplier can be chosen away from both the target primes and the
prime divisors of the preliminary scalar. A Bezout inverse and integral
approximation then construct a scalar with divisible residual, arbitrary
integral finite-place targets, and integrality at every finite place.
This does not prove the residual's representation in an anisotropic complement
or the archimedean sign conditions in 104:3.
-/

noncomputable section

namespace NormEuclidean.ResidualScalar

open IsDedekindDomain CompletedIntegralLattice ScalarIntegralApproximation Filter Topology

variable {K : Type*} [Field K]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]

omit [IsDedekindDomain R] [IsFractionRing R K] in
/-- Avoiding every prime divisor of a nonzero scalar gives an actual Bezout
identity with that scalar. No principal ideal ring premise is used. -/
theorem isCoprime_of_avoiding_divisors (c m : R) (hc : c ≠ 0)
    (hm : ∀ v : HeightOneSpectrum R, c ∈ v.asIdeal → m ∉ v.asIdeal) : IsCoprime c m := by
  apply (Ideal.isCoprime_span_singleton_iff c m).mp
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra h
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal
    (Ideal.span {c} ⊔ Ideal.span {m}) h
  have hcP : c ∈ P := (show Ideal.span {c} ≤ P from le_sup_left.trans hle)
    (Ideal.subset_span (Set.mem_singleton c))
  have hmP : m ∈ P := (show Ideal.span {m} ≤ P from le_sup_right.trans hle)
    (Ideal.subset_span (Set.mem_singleton m))
  have hP0 : P ≠ ⊥ := by
    intro hzero
    rw [hzero, Ideal.mem_bot] at hcP
    exact hc hcP
  let v : HeightOneSpectrum R := ⟨P, hP.isPrime, hP0⟩
  exact hm v hcP hmP

/-- Finite integral approximation and a Bezout inverse construct the residual
divisibility required by 104:3. All finite outside-target integrality is derived. -/
theorem exists_divisible_residual_scalar (T : Finset (HeightOneSpectrum R))
    (c m : R) (hcm : IsCoprime c m) (hm : ∀ v ∈ T, m ∉ v.asIdeal)
    (x : (v : T) → LocalRing R v.1) (W : (v : T) → Set (LocalField R v.1))
    (hW : ∀ v, W v ∈ 𝓝 (x v : LocalField R v.1)) :
    ∃ β : R, (∃ b : R, 1 - (c : K) ^ 2 * (β : K) ^ 2 = (m : K) * (b : K)) ∧
      (∀ v : T, algebraMap K (LocalField R v.1) (β : K) ∈ W v) ∧
      ∀ v : HeightOneSpectrum R,
        algebraMap K (LocalField R v) (β : K) ∈ LocalRing R v := by
  obtain ⟨b, d, hbd⟩ := hcm
  obtain ⟨β, ⟨z, hz⟩, hβ, hβint⟩ := exists_integer_congruence_nhds R T m b hm x W hW
  have hβeq : β = b + m * z := by linear_combination hz
  have hdiv : 1 - c ^ 2 * β ^ 2 = m * ((d - c * z) * (1 + c * β)) := by
    calc
      1 - c ^ 2 * β ^ 2 = (1 - c * β) * (1 + c * β) := by ring
      _ = (m * (d - c * z)) * (1 + c * β) := by
        congr 1
        rw [hβeq]
        linear_combination -hbd
      _ = _ := by ring
  refine ⟨β, ⟨(d - c * z) * (1 + c * β), ?_⟩, hβ, hβint⟩
  exact congrArg (fun r : R ↦ (r : K)) hdiv

end NormEuclidean.ResidualScalar
