import NormEuclidean.CompletedIdealNorm
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Global prime ideals in the original completed integer ring

The actual global integer embedding takes the defining prime to the
completed maximal ideal. Every other nonzero prime becomes the unit ideal.
The proofs use a global element of valuation one and do not assume an
ideal correspondence or a comparison of different ideals.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.CompletedPrimeIdeals

open IsDedekindDomain IsLocalRing Bong.NumberFieldCompletion
open Valuation.IsRankOneDiscrete
open scoped NumberField WithZero Classical

variable {F : Type*} [Field F] [NumberField F]

/-- The original global integer embedding preserves the defining valuation. -/
theorem embedding_valuation (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) :
    Valued.v ((integerEmbedding v a : integerRing v) : v.adicCompletion F) =
      v.intValuation a := by
  change Valued.v ((algebraMap (𝓞 F) F a : F) : v.adicCompletion F) = _
  rw [HeightOneSpectrum.adicCompletion.valued_coe F v, v.valuation_of_algebraMap]

/-- Membership in the completed maximal ideal detects the original prime exactly. -/
theorem embedding_mem_maximal (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) :
    integerEmbedding v a ∈ maximalIdeal (integerRing v) ↔ a ∈ v.asIdeal := by
  have h := Valuation.mem_maximalIdeal_iff
    (v := (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰))
    (a := integerEmbedding v a)
  exact h.trans (by rw [embedding_valuation, v.intValuation_lt_one_iff_mem])

/-- A global integral element of valuation one, without any principality assumption on the prime. -/
def globalUniformizer (v : HeightOneSpectrum (𝓞 F)) : 𝓞 F :=
  Classical.choose v.intValuation_exists_uniformizer

theorem globalUniformizer_valuation (v : HeightOneSpectrum (𝓞 F)) :
    v.intValuation (globalUniformizer v) = WithZero.exp (-1 : ℤ) :=
  Classical.choose_spec v.intValuation_exists_uniformizer

theorem globalUniformizer_mem (v : HeightOneSpectrum (𝓞 F)) :
    globalUniformizer v ∈ v.asIdeal := by
  rw [← v.intValuation_lt_one_iff_mem, globalUniformizer_valuation]
  exact (WithZero.exp_lt_exp).mpr (by norm_num : (-1 : ℤ) < 0)

/-- Its image generates the original completed maximal ideal. -/
theorem globalUniformizer_span (v : HeightOneSpectrum (𝓞 F)) :
    Ideal.span ({integerEmbedding v (globalUniformizer v)} : Set (integerRing v)) =
      maximalIdeal (integerRing v) := by
  have hu : Valuation.IsUniformizer
      (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)
      (integerEmbedding v (globalUniformizer v)) := by
    rw [Valuation.IsUniformizer.iff, embedding_valuation, globalUniformizer_valuation,
      generator_eq_exp_neg_one_of_surjective (v.valuedAdicCompletion_surjective F)]
    rfl
  exact hu.is_generator.symm

/-- Extension of the defining global prime is precisely the completed maximal ideal. -/
theorem map_own_prime (v : HeightOneSpectrum (𝓞 F)) :
    v.asIdeal.map (integerEmbedding v) = maximalIdeal (integerRing v) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact (embedding_mem_maximal v a).mpr ha
  · rw [← globalUniformizer_span v, Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem (integerEmbedding v) (globalUniformizer_mem v)

/-- Every other global prime contains an element that is a unit at this completion. -/
theorem exists_local_unit (v w : HeightOneSpectrum (𝓞 F)) (hw : w ≠ v) :
    ∃ a ∈ w.asIdeal, IsUnit (integerEmbedding v a) := by
  have hn : ¬ w.asIdeal ≤ v.asIdeal := by
    intro h
    apply hw
    exact HeightOneSpectrum.ext_iff.mpr (w.isMaximal.eq_of_le v.isPrime.ne_top h)
  obtain ⟨a, ha, hav⟩ := SetLike.not_le_iff_exists.mp hn
  refine ⟨a, ha, ?_⟩
  apply IsLocalRing.notMem_maximalIdeal.mp
  exact (embedding_mem_maximal v a).not.mpr hav

/-- A different nonzero prime extends to the unit ideal, including at dyadic places. -/
theorem map_other_prime (v w : HeightOneSpectrum (𝓞 F)) (hw : w ≠ v) :
    w.asIdeal.map (integerEmbedding v) = ⊤ := by
  obtain ⟨a, ha, hu⟩ := exists_local_unit v w hw
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem (integerEmbedding v) ha) hu

/-- All powers of the defining prime extend to the corresponding maximal-ideal powers. -/
theorem map_prime_power (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    (v.asIdeal ^ n).map (integerEmbedding v) = maximalIdeal (integerRing v) ^ n := by
  rw [Ideal.map_pow, map_own_prime]

/-- Every global prime factor has its explicit completed image. -/
theorem map_prime_factor (v w : HeightOneSpectrum (𝓞 F)) (I : Ideal (𝓞 F)) :
    (w.maxPowDividing I).map (integerEmbedding v) =
      if w = v then (v.maxPowDividing I).map (integerEmbedding v) else 1 := by
  classical
  by_cases hw : w = v
  · simp only [hw, ↓reduceIte]
  · simp only [if_neg hw, HeightOneSpectrum.maxPowDividing, Ideal.map_pow,
      map_other_prime v w hw, ← Ideal.one_eq_top, one_pow]

end NormEuclidean.CompletedPrimeIdeals
