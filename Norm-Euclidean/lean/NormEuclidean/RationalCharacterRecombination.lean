import NormEuclidean.RationalPrimaryCharacter
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Recombination of all rational primary characters

The primary decomposition has finite support at every rational class.
Its actual sum is that class. Reindexing the original integer prime
ideals by rational primes gives the full finite-place character sum.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.RationalCharacterRecombination

open IsDedekindDomain RationalPrimaryCharacter
open scoped Classical

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

theorem primary_finite_support (x : Circle) :
    Function.HasFiniteSupport (fun P : HeightOneSpectrum ℤ ↦ primary P x) := by
  exact DirectSum.hasFiniteSupport Component (decomposition.symm x)

/-- The finite sum of all primary projections is the original rational circle class. -/
theorem primary_sum (x : Circle) :
    ∑ᶠ P : HeightOneSpectrum ℤ, primary P x = x := by
  have h := congrArg decomposition (DirectSum.sum_support_of (decomposition.symm x))
  rw [map_sum, LinearEquiv.apply_symm_apply] at h
  have he (P : HeightOneSpectrum ℤ) (y : Component P) :
      decomposition (DirectSum.of (fun i ↦ Component i) P y) = (y : Circle) :=
    DirectSum.coeLinearMap_of Component P y
  simp only [he] at h
  change (∑ P ∈ (decomposition.symm x).support, primary P x) = x at h
  rw [finsum_eq_sum_of_support_subset (fun P : HeightOneSpectrum ℤ ↦ primary P x)
    (DirectSum.support_subset Component (decomposition.symm x))]
  exact h

/-- The standard prime-ideal equivalence agrees with the previously constructed primary prime. -/
theorem prime_equiv (p : Nat.Primes) :
    (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p = prime (p : ℕ) := by
  apply HeightOneSpectrum.ext_iff.mpr
  change (Ideal.span {(p : ℤ)}).map _ = Ideal.span {(p : ℤ)}
  simp only [Ideal.map_span, Set.image_singleton, map_natCast]

/-- The actual rational characters are nonzero at only finitely many rational primes. -/
theorem character_finite_support (q : ℚ) :
    Function.HasFiniteSupport (fun p : Nat.Primes ↦ character (p : ℕ) q) := by
  have he : (fun p : Nat.Primes ↦ character (p : ℕ) q) =
      (fun p ↦ primary ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p)
        (q : Circle)) := by
    funext p
    rw [prime_equiv, character_apply]
  rw [he]
  exact (primary_finite_support (q : Circle)).comp_of_injective
    (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm.injective

/-- All rational finite-place characters add up to the original rational class. -/
theorem character_sum (q : ℚ) :
    ∑ᶠ p : Nat.Primes, character (p : ℕ) q = (q : Circle) := by
  calc
    _ = ∑ᶠ p : Nat.Primes,
        primary ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p) (q : Circle) := by
      congr 1
      funext p
      rw [prime_equiv, character_apply]
    _ = ∑ᶠ P : HeightOneSpectrum ℤ, primary P (q : Circle) :=
      finsum_comp_equiv (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm
        (f := fun P ↦ primary P (q : Circle))
    _ = _ := primary_sum _

end NormEuclidean.RationalCharacterRecombination
