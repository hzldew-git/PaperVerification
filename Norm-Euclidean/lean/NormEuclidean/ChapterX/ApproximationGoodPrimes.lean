import NormEuclidean.ChapterX.CofiniteSelfDual

/-!
# Constructing the finite exceptional set for reflection approximation

The enlarged set includes dyadic primes, nonunit target values,
non-self-dual carriers and nonintegral global reflecting vectors.
All these exceptions are proved finite for actual completions.
-/

noncomputable section

namespace NormEuclidean.ApproximationGoodPrimes

open IsDedekindDomain CompletedIntegralLattice ScalarIntegralApproximation LocalPrimitivePairing
  Filter

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

set_option backward.isDefEq.respectTransparency false in
/-- The good-prime hypotheses for 104:3 and 104:4 are obtained by a finite enlargement. -/
theorem exists_good_superset (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (L : Submodule (integerSubring K) V) (hfg : L.FG)
    (hfull : Submodule.span K (L : Set V) = ⊤) (a : K) (ha : a ≠ 0) (x : V)
    (T : Finset (HeightOneSpectrum (integerSubring K))) :
    ∃ S : Finset (HeightOneSpectrum (integerSubring K)), T ⊆ S ∧
      (∀ p : HeightOneSpectrum (integerSubring K), (2 : integerSubring K) ∈ p.asIdeal → p ∈ S) ∧
      (∀ p : HeightOneSpectrum (integerSubring K), p ∉ S → p.valuation K a = 1) ∧
      (∀ p : HeightOneSpectrum (integerSubring K), p ∉ S →
        SelfDual (LocalRing (integerSubring K) p) (halfPolar (form _ p Q))
          (carrier (integerSubring K) p L)) ∧
      ∀ p : HeightOneSpectrum (integerSubring K), p ∉ S →
        inclusion (integerSubring K) p x ∈ carrier (integerSubring K) p L := by
  classical
  let good (p : HeightOneSpectrum (integerSubring K)) : Prop :=
    (2 : integerSubring K) ∉ p.asIdeal ∧ p.valuation K a = 1 ∧
      SelfDual (LocalRing (integerSubring K) p) (halfPolar (form _ p Q))
        (carrier (integerSubring K) p L) ∧
      inclusion (integerSubring K) p x ∈ carrier (integerSubring K) p L
  have htwo : ∀ᶠ p : HeightOneSpectrum (integerSubring K) in cofinite,
      (2 : integerSubring K) ∉ p.asIdeal := by
    apply eventually_cofinite.mpr
    simpa only [not_not] using
      finite_primes_containing (K := K) (integerSubring K) 2 (by norm_num)
  have hunit : ∀ᶠ p : HeightOneSpectrum (integerSubring K) in cofinite,
      p.valuation K a = 1 :=
    eventually_cofinite.mpr (CofiniteLocalIsotropy.finite_nonunit_valuations a ha)
  have hgood : ∀ᶠ p in cofinite, good p :=
    htwo.and (hunit.and ((CofiniteSelfDual.eventually_selfDual Q hQ L hfg hfull).and
      (CofiniteSelfDual.eventually_mem_carrier L hfg hfull x)))
  have hbad : {p | ¬ good p}.Finite := eventually_cofinite.mp hgood
  let S := T ∪ hbad.toFinset
  have hS (p : HeightOneSpectrum (integerSubring K)) (hp : p ∉ S) : good p := by
    by_contra h
    exact hp (Finset.mem_union_right T (by simpa using h))
  refine ⟨S, Finset.subset_union_left, ?_, fun p hp ↦ (hS p hp).2.1,
    fun p hp ↦ (hS p hp).2.2.1, fun p hp ↦ (hS p hp).2.2.2⟩
  intro p hp
  by_contra hnot
  exact (hS p hnot).1 hp

end NormEuclidean.ApproximationGoodPrimes
