import NormEuclidean.ChapterX.LocalUnitSquares

/-!
# Finite local represented-value neighborhoods in O'Meara 104:3

A nonzero represented value has an actual neighborhood of represented values
in the same completed integral module: multiply its vector by a local unit
whose square is near one. The unit-square neighborhood is proved by Hensel
lifting even at dyadic primes. Residual scalar neighborhoods follow by continuity.
Existence of the initial represented vector remains explicit.
-/

noncomputable section

namespace NormEuclidean.LocalValueNeighborhoods

open IsDedekindDomain CompletedIntegralLattice Filter Topology

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E]
variable (v : HeightOneSpectrum (integerSubring K)) [Module (LocalField (integerSubring K) v) E]

/-- Every nonzero actually represented finite local value has a neighborhood
represented in the same actual integral module. No local representation law,
odd-residue-characteristic assumption or regularity hypothesis is supplied. -/
theorem exists_value_neighborhood (Q : QuadraticForm (LocalField (integerSubring K) v) E)
    (N : Submodule (LocalRing (integerSubring K) v) E) (x : E) (hx : x ∈ N)
    (hx0 : Q x ≠ 0) :
    ∃ B : Set (LocalField (integerSubring K) v), B ∈ 𝓝 (Q x) ∧
      ∀ a ∈ B, ∃ y ∈ N, Q y = a := by
  obtain ⟨U, hU, hsquare⟩ := LocalUnitSquares.exists_square_neighborhood v
  let f (a : LocalField (integerSubring K) v) := a / Q x
  have hf : Continuous f := continuous_id.div_const _
  have hB : f ⁻¹' U ∈ 𝓝 (Q x) := hf.continuousAt.preimage_mem_nhds
    (by simpa only [f, div_self hx0] using hU)
  refine ⟨f ⁻¹' U, hB, ?_⟩
  intro a ha
  obtain ⟨u, hu⟩ := hsquare (f a) ha
  refine ⟨(u : LocalRing (integerSubring K) v) • x, N.smul_mem _ hx, ?_⟩
  change Q (((u : LocalRing (integerSubring K) v) : LocalField (integerSubring K) v) • x) = a
  rw [Q.map_smul]
  simp only [smul_eq_mul, ← pow_two, hu]
  exact div_mul_cancel₀ a hx0

/-- A single nonzero represented residual produces an actual scalar
neighborhood on which every residual is represented in the same local module.
This includes the exceptional dyadic places, but does not invent the initial vector. -/
theorem exists_residual_neighborhood
    (Q : QuadraticForm (LocalField (integerSubring K) v) E)
    (N : Submodule (LocalRing (integerSubring K) v) E)
    (a c β₀ : LocalField (integerSubring K) v) (x : E) (hx : x ∈ N)
    (hvalue : Q x = a * (1 - c ^ 2 * β₀ ^ 2)) (hx0 : Q x ≠ 0) :
    ∃ B : Set (LocalField (integerSubring K) v), B ∈ 𝓝 β₀ ∧
      ∀ β ∈ B, ∃ y ∈ N, Q y = a * (1 - c ^ 2 * β ^ 2) := by
  obtain ⟨U, hU, hrep⟩ := exists_value_neighborhood v Q N x hx hx0
  let f (β : LocalField (integerSubring K) v) := a * (1 - c ^ 2 * β ^ 2)
  have hf : Continuous f := by fun_prop
  have hB : f ⁻¹' U ∈ 𝓝 β₀ := hf.continuousAt.preimage_mem_nhds
    (by simpa only [f, ← hvalue] using hU)
  exact ⟨f ⁻¹' U, hB, fun β hβ ↦ hrep _ hβ⟩

end NormEuclidean.LocalValueNeighborhoods
