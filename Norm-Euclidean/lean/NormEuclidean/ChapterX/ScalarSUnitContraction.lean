import NormEuclidean.ChapterX.PrimePowerDenominator
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Simultaneous finite and infinite scalar contraction away from one infinite place

Positive prime-power generators contract at the specified finite primes.
The actual number-field unit theorem supplies a unit contracting at every
infinite place except the excluded one. Its powers preserve the finite
valuations while achieving all the infinite bounds. This proves the S-unit
contraction input to 33G when the excluded place is infinite, not the complete
scalar approximation or excluded-place growth theorem.
-/

noncomputable section

namespace NormEuclidean.ScalarSUnitContraction

open IsDedekindDomain CompletedIntegralLattice PrimePowerDenominator Filter Topology
open scoped WithZero

variable {K : Type*} [Field K] [NumberField K]

/-- An integer supported on the target primes meets arbitrary strictly
positive valuation bounds at those primes. -/
theorem exists_finite_contraction (T : Finset (HeightOneSpectrum (integerSubring K)))
    (γ : T → (ℤᵐ⁰)ˣ) :
    ∃ d : integerSubring K, d ≠ 0 ∧ (∀ v : T, v.1.intValuation d < γ v) ∧
      ∀ w : HeightOneSpectrum (integerSubring K), w ∉ T → d ∉ w.asIdeal := by
  classical
  choose a ha0 hav haw using fun v : T ↦ exists_single_prime_scalar v.1
  have hlt (v : T) : v.1.intValuation (a v) < 1 := by
    exact (v.1.intValuation_lt_one_iff_mem (a v)).mpr (hav v)
  choose n hn using fun v : T ↦ exists_pow_lt₀ (hlt v) (γ v)
  let f : T → integerSubring K := fun v ↦ a v ^ n v
  let d : integerSubring K := ∏ v : T, f v
  refine ⟨d, Finset.prod_ne_zero_iff.mpr (fun v _ ↦ pow_ne_zero _ (ha0 v)), ?_, ?_⟩
  · intro v
    obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem f (Finset.mem_univ v)
    change d = a v ^ n v * b at hb
    rw [hb, map_mul, map_pow]
    exact (mul_le_of_le_one_right bot_le (v.1.intValuation_le_one b)).trans_lt (hn v)
  · intro w hw
    exact w.asIdeal.primeCompl.prod_mem (fun v _ ↦
      w.asIdeal.primeCompl.pow_mem (haw v w (fun h ↦ hw (h ▸ v.2))) (n v))

/-- O'Meara's scalar contraction input with an excluded infinite place:
the constructed scalar has prescribed finite support, arbitrary finite
valuation contraction and arbitrary bounds at every other infinite place. -/
theorem exists_simultaneous_contraction
    (T : Finset (HeightOneSpectrum (integerSubring K))) (q : NumberField.InfinitePlace K)
    (γ : T → (ℤᵐ⁰)ˣ) (η : NumberField.InfinitePlace K → ℝ)
    (hη : ∀ w : NumberField.InfinitePlace K, w ≠ q → 0 < η w) :
    ∃ ε : integerSubring K, ε ≠ 0 ∧ (∀ v : T, v.1.intValuation ε < γ v) ∧
      (∀ w : HeightOneSpectrum (integerSubring K), w ∉ T → ε ∉ w.asIdeal) ∧
      ∀ w : NumberField.InfinitePlace K, w ≠ q → w (ε : K) < η w := by
  classical
  obtain ⟨d, hd0, hdT, hdout⟩ := exists_finite_contraction T γ
  obtain ⟨u, hu⟩ := NumberField.Units.dirichletUnitTheorem.exists_unit (K := K) q
  let ur : (integerSubring K)ˣ := u
  have hcast : ((ur : integerSubring K) : K) = (u : K) := rfl
  have huv (v : HeightOneSpectrum (integerSubring K)) :
      v.intValuation (ur : integerSubring K) = 1 :=
    (v.intValuation_eq_one_iff_mem_primeCompl _).mpr
      (v.asIdeal.notMem_of_isUnit ur.isUnit)
  have hev (w : {w : NumberField.InfinitePlace K // w ≠ q}) :
      ∀ᶠ n : ℕ in atTop, w.1 (d : K) * w.1 (u : K) ^ n < η w.1 := by
    have hunitlt : w.1 (u : K) < 1 := by
      by_contra! h
      exact not_lt_of_ge (Real.log_nonneg h) (hu w.1 w.2)
    have ht : Tendsto (fun n : ℕ ↦ w.1 (d : K) * w.1 (u : K) ^ n) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt (NumberField.Units.pos_at_place u w.1))
          hunitlt).const_mul (w.1 (d : K))
    exact ht.eventually (gt_mem_nhds (hη w.1 w.2))
  obtain ⟨n, hn⟩ := (Filter.eventually_all.mpr hev).exists
  let ε : integerSubring K := d * (ur : integerSubring K) ^ n
  refine ⟨ε, mul_ne_zero hd0 (pow_ne_zero n (Units.ne_zero ur)), ?_, ?_, ?_⟩
  · intro v
    dsimp only [ε]
    rw [map_mul, map_pow, huv, one_pow, mul_one]
    exact hdT v
  · intro w hw
    exact w.asIdeal.primeCompl.mul_mem (hdout w hw)
      (w.asIdeal.primeCompl.pow_mem (w.asIdeal.notMem_of_isUnit ur.isUnit) n)
  · intro w hw
    dsimp only [ε]
    rw [Subring.coe_mul, Subring.coe_pow, hcast, map_mul, map_pow]
    exact hn ⟨w, hw⟩

end NormEuclidean.ScalarSUnitContraction
