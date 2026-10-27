import NormEuclidean.ChapterX.PrimePowerDenominator

/-!
# Finite-place scalar strong approximation with outside-target integrality

Prime-power denominators and the proved integral Chinese-remainder
approximation control arbitrary completed scalars, not only integral targets.
The global scalar is integral at every finite prime outside the target set.
Archimedean targets and growth at an excluded place in O'Meara 33G remain
separate obligations.
-/

noncomputable section

namespace NormEuclidean.FiniteScalarStrongApproximation

open IsDedekindDomain CompletedIntegralLattice ScalarIntegralApproximation
  PrimePowerDenominator Filter Topology

variable {K : Type*} [Field K] [NumberField K]

/-- Scalar strong approximation at any finite collection of actual finite
completions, with integrality at every other finite prime. Dyadic places,
fractional targets and an empty target set are included. -/
theorem exists_scalar (T : Finset (HeightOneSpectrum (integerSubring K)))
    (x : (v : T) → LocalField (integerSubring K) v.1)
    (W : (v : T) → Set (LocalField (integerSubring K) v.1))
    (hW : ∀ v, W v ∈ 𝓝 (x v)) :
    ∃ a : K, (∀ v : T, algebraMap K (LocalField (integerSubring K) v.1) a ∈ W v) ∧
      ∀ w : HeightOneSpectrum (integerSubring K), w ∉ T →
        algebraMap K (LocalField (integerSubring K) w) a ∈ LocalRing (integerSubring K) w := by
  obtain ⟨d, hd0, hdx, hdout⟩ := exists_supported_denominator T x
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd0
  let dv (v : T) := algebraMap K (LocalField (integerSubring K) v.1) (d : K)
  have hdv (v : T) : dv v ≠ 0 := by
    intro h
    exact hdK ((algebraMap K (LocalField (integerSubring K) v.1)).injective
      (h.trans (map_zero _).symm))
  let y : (v : T) → LocalRing (integerSubring K) v.1 := fun v ↦ ⟨dv v * x v, hdx v⟩
  let f (v : T) (z : LocalField (integerSubring K) v.1) := z / dv v
  have hfy (v : T) : f v (y v) = x v := by
    exact mul_div_cancel_left₀ (x v) (hdv v)
  have hnb (v : T) : f v ⁻¹' W v ∈ 𝓝 (y v : LocalField (integerSubring K) v.1) := by
    have hc : Continuous (f v) := continuous_id.div_const (dv v)
    apply hc.continuousAt.preimage_mem_nhds
    simpa only [hfy] using hW v
  obtain ⟨b, hb, _⟩ := exists_simultaneous_integer_nhds (integerSubring K) T y
    (fun v ↦ f v ⁻¹' W v) hnb
  refine ⟨(b : K) / (d : K), ?_, ?_⟩
  · intro v
    rw [map_div₀]
    exact hb v
  · intro w hw
    have hdw : w.valuation K (d : K) = 1 := by
      change w.valuation K (algebraMap (integerSubring K) K d) = 1
      exact (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr (hdout w hw)
    change Valued.v (algebraMap K (LocalField (integerSubring K) w)
      ((b : K) / (d : K))) ≤ 1
    rw [map_div₀, map_div₀, valuation_algebraMap, valuation_algebraMap, hdw, div_one]
    exact w.valuation_le_one b

end NormEuclidean.FiniteScalarStrongApproximation
