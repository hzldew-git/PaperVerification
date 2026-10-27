import NormEuclidean.ChapterX.CompletionHensel
import NormEuclidean.ChapterX.ScalarIntegralApproximation
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# Unit squares near one at every actual finite completion

Hensel lifting of X^2+X-delta has derivative one at zero, including at dyadic
places. Consequently 1+4*delta is a unit square for delta in the maximal ideal.
This yields an actual square neighborhood of one without requiring two to
be a unit in the local integer ring.
-/

noncomputable section

namespace NormEuclidean.LocalUnitSquares

open Polynomial IsDedekindDomain CompletedIntegralLattice Filter Topology
open scoped WithZero

/-- The derivative-one Hensel construction includes residue characteristic two. -/
theorem one_add_four_mul_square {S : Type*} [CommRing S] [IsLocalRing S]
    [HenselianRing S (IsLocalRing.maximalIdeal S)] (δ : S)
    (hδ : δ ∈ IsLocalRing.maximalIdeal S) :
    ∃ u : Sˣ, (u : S) ^ 2 = 1 + 4 * δ := by
  let I := IsLocalRing.maximalIdeal S
  let f : S[X] := X ^ 2 + X - C δ
  have hf : f.Monic := by
    dsimp only [f]
    rw [add_sub_assoc]
    exact monic_X_pow_add (by rw [degree_X_sub_C]; norm_num)
  have hf0 : f.eval 0 ∈ I := by simpa [f] using I.neg_mem hδ
  have hf' : IsUnit (Ideal.Quotient.mk I (f.derivative.eval 0)) := by
    have hder : f.derivative.eval 0 = (1 : S) := by simp [f]
    rw [hder, map_one]
    exact isUnit_one
  obtain ⟨z, hz, hzI⟩ := HenselianRing.is_henselian f hf 0 hf0 hf'
  have hroot : z ^ 2 + z - δ = 0 := by simpa [f, Polynomial.IsRoot] using hz
  have hzmem : z ∈ I := by simpa only [sub_zero] using hzI
  have hu : IsUnit (1 + 2 * z) := IsLocalRing.notMem_maximalIdeal.mp (by
    intro h
    have hone : (1 : S) ∈ I := by
      simpa only [add_sub_cancel_right] using I.sub_mem h (I.mul_mem_left 2 hzmem)
    exact (inferInstance : I.IsMaximal).ne_top (Ideal.eq_top_of_isUnit_mem I hone isUnit_one))
  refine ⟨hu.unit, ?_⟩
  rw [hu.unit_spec]
  linear_combination 4 * hroot

variable {K : Type*} [Field K] [NumberField K]

/-- In the actual finite completion, unit squares contain a neighborhood
of one. The valuation precision uses four, so no dyadic prime is excluded. -/
theorem exists_square_neighborhood (v : HeightOneSpectrum (integerSubring K)) :
    ∃ B : Set (LocalField (integerSubring K) v), B ∈ 𝓝 1 ∧
      ∀ t ∈ B, ∃ u : (LocalRing (integerSubring K) v)ˣ,
        ((u : LocalRing (integerSubring K) v) : LocalField (integerSubring K) v) ^ 2 = t := by
  let F := LocalField (integerSubring K) v
  let S := LocalRing (integerSubring K) v
  letI := CompletionHensel.henselian_completed_integers v
  have h4 : (4 : F) ≠ 0 := by norm_num
  have hv4 : Valued.v (4 : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr h4
  let γ : (ℤᵐ⁰)ˣ := Units.mk0 (Valued.v (4 : F)) hv4
  let B : Set F := {t | Valued.v (t - 1) < γ}
  refine ⟨B, ScalarIntegralApproximation.valuation_ball_mem_nhds (integerSubring K) v 1 γ, ?_⟩
  intro t ht
  have hδ : Valued.v ((t - 1) / 4) < (1 : ℤᵐ⁰) := by
    rw [map_div₀, div_lt_one₀ hv4.bot_lt]
    exact ht
  let δ : S := ⟨(t - 1) / 4, hδ.le⟩
  have hδI : δ ∈ IsLocalRing.maximalIdeal S := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have heq := (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mp hu
    exact hδ.ne heq
  obtain ⟨u, hu⟩ := one_add_four_mul_square δ hδI
  refine ⟨u, ?_⟩
  have h := congrArg (fun x : S ↦ (x : F)) hu
  change ((u : S) : F) ^ 2 = 1 + 4 * ((t - 1) / 4) at h
  rw [mul_div_cancel₀ _ h4, add_sub_cancel] at h
  exact h

end NormEuclidean.LocalUnitSquares
