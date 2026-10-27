import NormEuclidean.ChapterX.CompletedExtensionProduct
import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Completely split primes and actual completed degrees

The ideal-theoretic complete splitting criterion gives degree one in every
actual completion. The proof uses the fundamental ramification identity and
the already proved surjectivity of the completed tensor comparison.
-/

noncomputable section

namespace NormEuclidean.FinitePrimeSplitting

open IsDedekindDomain ExtensionIdeleNorm
open scoped NumberField NormEuclidean.CompletedExtensionProduct

universe u
variable {K E : Type u} [Field K] [NumberField K]
  [Field E] [NumberField E] [Algebra K E]

/-- Maximal prime-fiber cardinality forces every completed factor to have degree one. -/
theorem degree_one_of_prime_count (p : HeightOneSpectrum (𝓞 K))
    (hcount : (p.asIdeal.primesOver (𝓞 E)).ncard = Module.finrank K E)
    (w : FinitePlacesAbove (E := E) p) :
    Module.finrank (p.adicCompletion K) (w.1.adicCompletion E) = 1 := by
  classical
  have hcard : Fintype.card (FinitePlacesAbove (E := E) p) = Module.finrank K E := by
    rw [← Nat.card_eq_fintype_card]
    exact (Nat.card_congr (finitePlacesAboveEquivPrimesOver p)).trans hcount
  have hpos (z : FinitePlacesAbove (E := E) p) (_ : z ∈ Finset.univ) :
      1 ≤ Module.finrank (p.adicCompletion K) (z.1.adicCompletion E) :=
    Nat.succ_le_of_lt Module.finrank_pos
  have hsum : (∑ _ : FinitePlacesAbove (E := E) p, (1 : ℕ)) =
      ∑ z : FinitePlacesAbove (E := E) p,
        Module.finrank (p.adicCompletion K) (z.1.adicCompletion E) := by
    apply le_antisymm (Finset.sum_le_sum hpos)
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hcard] using
      CompletedExtensionProduct.local_degrees_le (E := E) p
  exact ((Finset.sum_eq_sum_iff_of_le hpos).mp hsum w (Finset.mem_univ w)).symm

variable [IsGalois K E]

/-- Complete ideal-theoretic splitting gives exactly the global degree many primes. -/
theorem prime_count_of_ramification_inertia_one (p : HeightOneSpectrum (𝓞 K))
    (hsplit : ∀ w : FinitePlacesAbove (E := E) p,
      w.1.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ w.1.asIdeal.inertiaDeg (𝓞 K) = 1) :
    (p.asIdeal.primesOver (𝓞 E)).ncard = Module.finrank K E := by
  letI : p.asIdeal.IsPrime := p.isPrime
  obtain ⟨w⟩ := finitePlacesAbove_nonempty (E := E) p
  letI : w.1.asIdeal.IsPrime := w.1.isPrime
  letI : w.1.asIdeal.LiesOver p.asIdeal :=
    ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    p.asIdeal (𝓞 E) (E ≃ₐ[K] E)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal w.1.asIdeal (E ≃ₐ[K] E),
    Ideal.inertiaDegIn_eq_inertiaDeg p.asIdeal w.1.asIdeal (E ≃ₐ[K] E),
    (hsplit w).1, (hsplit w).2, one_mul, mul_one, IsGalois.card_aut_eq_finrank] at h
  exact h

/-- A completely split prime has degree one in every actual completed extension factor. -/
theorem degree_one_of_ramification_inertia_one (p : HeightOneSpectrum (𝓞 K))
    (hsplit : ∀ w : FinitePlacesAbove (E := E) p,
      w.1.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ w.1.asIdeal.inertiaDeg (𝓞 K) = 1)
    (w : FinitePlacesAbove (E := E) p) :
    Module.finrank (p.adicCompletion K) (w.1.adicCompletion E) = 1 :=
  degree_one_of_prime_count p (prime_count_of_ramification_inertia_one p hsplit) w

end NormEuclidean.FinitePrimeSplitting
