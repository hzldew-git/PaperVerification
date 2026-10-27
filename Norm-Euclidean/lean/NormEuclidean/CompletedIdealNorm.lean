import NormEuclidean.CompletedHaarDensity
import NormEuclidean.DyadicTwoRootCount

/-!
# Actual completion norms from principal ideals

The metric norm on the original number-field completion is compared
with the actual DVR principal-ideal exponent and quotient cardinality.
The normalized uniformizer has norm (Np)^(-1), and integral units have
norm one. This supplies the analytic modulus used by local form measures.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.CompletedIdealNorm

open IsDedekindDomain IsLocalRing Bong.NumberFieldCompletion NumberField
open Valuation.IsRankOneDiscrete
open scoped NumberField WithZero

variable {K : Type*} [Field K] [NumberField K]

/-- The actual normalized completed uniformizer is an integral element. -/
def pi (p : HeightOneSpectrum (𝓞 K)) : integerRing p :=
  ⟨uniformizer p, by
    change Valued.v (uniformizer p) ≤ 1
    rw [valuation_uniformizer]
    exact (WithZero.exp_le_exp).mpr (by norm_num : (-1 : ℤ) ≤ 0)⟩

/-- The chosen actual uniformizer generates the original completed maximal ideal. -/
theorem pi_span (p : HeightOneSpectrum (𝓞 K)) :
    Ideal.span ({pi p} : Set (integerRing p)) = maximalIdeal (integerRing p) := by
  have hh : Valuation.IsUniformizer
      (Valued.v : Valuation (p.adicCompletion K) ℤᵐ⁰) (uniformizer p) := by
    rw [Valuation.IsUniformizer.iff, valuation_uniformizer,
      generator_eq_exp_neg_one_of_surjective (p.valuedAdicCompletion_surjective K)]
    rfl
  exact (Valuation.IsUniformizer.is_generator (π := pi p) hh).symm

/-- This is the metric norm of the actual uniformizer, with the original prime norm. -/
theorem pi_norm (p : HeightOneSpectrum (𝓞 K)) :
    ‖(pi p : p.adicCompletion K)‖ = (Ideal.absNorm p.asIdeal : ℝ)⁻¹ := by
  rw [pi, FinitePlace.norm_def, valuation_uniformizer]
  simp [WithZeroMulInt.toNNReal, WithZero.exp]

/-- Every actual completed integral unit has metric norm one. -/
theorem unit_norm (p : HeightOneSpectrum (𝓞 K)) (u : (integerRing p)ˣ) :
    ‖(u.val : p.adicCompletion K)‖ = 1 := by
  have hv := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp u.isUnit
  rw [FinitePlace.norm_def, hv, map_one]
  rfl

/-- Equality of principal ideals gives equality of actual completed metric norms. -/
theorem norm_eq_of_span_eq (p : HeightOneSpectrum (𝓞 K)) (x y : integerRing p)
    (h : Ideal.span ({x} : Set (integerRing p)) = Ideal.span ({y} : Set (integerRing p))) :
    ‖(x : p.adicCompletion K)‖ = ‖(y : p.adicCompletion K)‖ := by
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp h
  have he := congrArg (integerRing p).subtype hu
  change (x : p.adicCompletion K) * (u.val : p.adicCompletion K) = y at he
  rw [← he, norm_mul, unit_norm, mul_one]

/-- The actual principal-ideal exponent determines the actual metric norm. -/
theorem norm_of_span (p : HeightOneSpectrum (𝓞 K)) (x : integerRing p) (n : ℕ)
    (h : Ideal.span ({x} : Set (integerRing p)) = maximalIdeal (integerRing p) ^ n) :
    ‖(x : p.adicCompletion K)‖ = ((Ideal.absNorm p.asIdeal : ℝ) ^ n)⁻¹ := by
  have hs : Ideal.span ({x} : Set (integerRing p)) =
      Ideal.span ({pi p ^ n} : Set (integerRing p)) := by
    rw [← Ideal.span_singleton_pow, pi_span, h]
  rw [norm_eq_of_span_eq p x (pi p ^ n) hs]
  change ‖(pi p : p.adicCompletion K) ^ n‖ = _
  rw [norm_pow, pi_norm, inv_pow]

/-- The reciprocal modulus is exactly the finite quotient cardinality, before any measure choice. -/
theorem inverse_norm_eq_card (p : HeightOneSpectrum (𝓞 K)) (x : integerRing p) (n : ℕ)
    (h : Ideal.span ({x} : Set (integerRing p)) = maximalIdeal (integerRing p) ^ n) :
    ‖(x : p.adicCompletion K)‖⁻¹ =
      (Nat.card (integerRing p ⧸ Ideal.span ({x} : Set (integerRing p))) : ℝ) := by
  rw [norm_of_span p x n h, inv_inv, h, DyadicTwoRootCount.quotient_card,
    Nat.cast_pow, BinaryPlaceDensity.residue_card]

end NormEuclidean.CompletedIdealNorm
