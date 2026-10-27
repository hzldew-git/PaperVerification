import NormEuclidean.ChapterX.MixedScalarWeakApproximation
import NormEuclidean.ChapterX.ScalarIntegralApproximation

/-!
# Scalar precisions in actual completion neighborhoods

Valuation precisions and infinite absolute-value bounds give the actual
neighborhood control used by the residue correction and large perturbation.
Only finitely many finite completions fail integrality for a given field scalar.
-/

noncomputable section

namespace NormEuclidean.ScalarNeighborhoods

open IsDedekindDomain CompletedIntegralLattice ScalarIntegralApproximation
  MixedScalarWeakApproximation Filter Topology
open scoped WithZero

variable {K : Type*} [Field K] [NumberField K]

local instance : Module.Finite ℤ (integerSubring K) :=
  inferInstanceAs (Module.Finite ℤ (NumberField.RingOfIntegers K))
local instance : Module.Free ℤ (integerSubring K) :=
  inferInstanceAs (Module.Free ℤ (NumberField.RingOfIntegers K))

theorem norm_infinite_algebraMap (w : NumberField.InfinitePlace K) (a : K) :
    ‖algebraMap K w.Completion a‖ = w a := by
  convert norm_infinite_map w ((WithAbs.equiv w.1).symm a) using 1
  · rw [RingEquiv.apply_symm_apply]
  · rfl

theorem finite_precision (v : HeightOneSpectrum (integerSubring K))
    (a₀ : integerSubring K) (W : Set (LocalField (integerSubring K) v))
    (hW : W ∈ 𝓝 (algebraMap K (LocalField (integerSubring K) v) (a₀ : K))) :
    ∃ γ : (ℤᵐ⁰)ˣ, ∀ a : integerSubring K, v.intValuation (a - a₀) < γ →
      algebraMap K (LocalField (integerSubring K) v) (a : K) ∈ W := by
  obtain ⟨δ, hδ⟩ := Valued.mem_nhds.mp hW
  let γ : (ℤᵐ⁰)ˣ := Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
    (f := (.ofClass (Valued.v : Valuation (LocalField (integerSubring K) v) ℤᵐ⁰)))) δ
  refine ⟨γ, ?_⟩
  intro a ha
  apply hδ
  apply (Valuation.restrict_lt_iff_lt_embedding
    (Valued.v : Valuation (LocalField (integerSubring K) v) ℤᵐ⁰)).mpr
  change Valued.v (algebraMap K (LocalField (integerSubring K) v) (a : K) -
    algebraMap K (LocalField (integerSubring K) v) (a₀ : K)) < (γ : ℤᵐ⁰)
  rw [← map_sub, valuation_algebraMap]
  change v.valuation K (algebraMap (integerSubring K) K (a - a₀)) < (γ : ℤᵐ⁰)
  rwa [HeightOneSpectrum.valuation_of_algebraMap]

theorem infinite_precision (w : NumberField.InfinitePlace K) (a₀ : integerSubring K)
    (W : Set w.Completion) (hW : W ∈ 𝓝 (algebraMap K w.Completion (a₀ : K))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : integerSubring K, w ((a : K) - (a₀ : K)) < δ →
      algebraMap K w.Completion (a : K) ∈ W := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hW
  refine ⟨δ, hδ, ?_⟩
  intro a ha
  apply hball
  rw [Metric.mem_ball, dist_eq_norm_sub, ← map_sub, norm_infinite_algebraMap]
  exact ha

/-- The actual nonintegral finite places of any field scalar form a finite set,
including scalar zero. This is derived from a fraction-ring denominator. -/
theorem finite_nonintegral_places (a : K) :
    {v : HeightOneSpectrum (integerSubring K) |
      algebraMap K (LocalField (integerSubring K) v) a ∉
        LocalRing (integerSubring K) v}.Finite := by
  obtain ⟨b, d, hd, rfl⟩ := IsFractionRing.div_surjective (integerSubring K) a
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  apply (finite_primes_containing (K := K) (integerSubring K) d hd0).subset
  intro v hbad
  by_contra hv
  apply hbad
  have hdv : v.valuation K (algebraMap (integerSubring K) K d) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem v).mpr hv
  change Valued.v (algebraMap K (LocalField (integerSubring K) v)
    (algebraMap (integerSubring K) K b / algebraMap (integerSubring K) K d)) ≤ 1
  rw [map_div₀, map_div₀, valuation_algebraMap, valuation_algebraMap, hdv, div_one]
  exact v.valuation_le_one b

end NormEuclidean.ScalarNeighborhoods
