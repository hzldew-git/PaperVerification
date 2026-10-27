import NormEuclidean.ChapterX.ScalarSUnitContraction
import NormEuclidean.ChapterX.ResidualScalar
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient

/-!
# The finite residue-class correction in O'Meara 33:11

An integral modulus supported on the bad primes has a finite quotient.
Uniformly small multiplication of a fixed representative system by an
S-unit gives a scalar close to one at the target places and divisible by
the modulus at the bad places. Bezout supplies the required residue class.
The excluded place in this theorem is an infinite number-field place.
-/

noncomputable section

namespace NormEuclidean.FiniteResidueScalarCorrection

open IsDedekindDomain ScalarSUnitContraction ResidualScalar

variable {K : Type*} [Field K] [NumberField K]
open scoped WithZero

local instance : Module.Finite ℤ (integerSubring K) :=
  inferInstanceAs (Module.Finite ℤ (NumberField.RingOfIntegers K))
local instance : Module.Free ℤ (integerSubring K) :=
  inferInstanceAs (Module.Free ℤ (NumberField.RingOfIntegers K))

/-- The source finite-residue correction: beta is integral everywhere,
close to one at finite and infinite targets, and arbitrarily divisible
at a disjoint finite set of bad primes. No residue correction law is assumed. -/
theorem exists_multiplier (T W : Finset (HeightOneSpectrum (integerSubring K)))
    (hTW : Disjoint T W) (q : NumberField.InfinitePlace K)
    (γ : T → (ℤᵐ⁰)ˣ) (θ : W → (ℤᵐ⁰)ˣ)
    (δ : NumberField.InfinitePlace K → ℝ) (hδ : ∀ w, w ≠ q → 0 < δ w) :
    ∃ β : integerSubring K,
      (∀ v : T, v.1.intValuation (β - 1) < γ v) ∧
      (∀ v : W, v.1.intValuation β < θ v) ∧
      ∀ w : NumberField.InfinitePlace K, w ≠ q → w ((β : K) - 1) < δ w := by
  classical
  obtain ⟨m, hm0, hmW, hmout⟩ := exists_finite_contraction W θ
  let I : Ideal (integerSubring K) := Ideal.span {m}
  have hI0 : I ≠ ⊥ := by
    intro h
    have hmI : m ∈ I := Ideal.subset_span (Set.mem_singleton m)
    rw [h, Ideal.mem_bot] at hmI
    exact hm0 hmI
  letI : Finite (integerSubring K ⧸ I) := I.finiteQuotientOfFreeOfNeBot hI0
  letI := Fintype.ofFinite (integerSubring K ⧸ I)
  choose r hr using (Ideal.Quotient.mk_surjective (I := I))
  let C (w : NumberField.InfinitePlace K) : ℝ := 1 + ∑ i, w (r i : K)
  have hCpos (w : NumberField.InfinitePlace K) : 0 < C w :=
    add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun i _ ↦ w.1.nonneg _))
  have hbound (w : NumberField.InfinitePlace K) (i : integerSubring K ⧸ I) :
      w (r i : K) ≤ C w := by
    exact (Finset.single_le_sum (fun j _ ↦ w.1.nonneg (r j : K)) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  obtain ⟨ε, hε0, hεT, hεout, hεinf⟩ := exists_simultaneous_contraction T q γ
    (fun w ↦ δ w / C w) (fun w hw ↦ div_pos (hδ w hw) (hCpos w))
  have hcm : IsCoprime ε m := (isCoprime_of_avoiding_divisors (integerSubring K) m ε hm0
    (fun v hmv ↦ by
      have hvW : v ∈ W := by by_contra h; exact hmout v h hmv
      exact hεout v (fun hvT ↦ Finset.disjoint_left.mp hTW hvT hvW))).symm
  obtain ⟨s, d, hsd⟩ := hcm
  let b := r (Ideal.Quotient.mk I (-s))
  have hbr : b + s ∈ I := by
    simpa only [sub_neg_eq_add] using Ideal.Quotient.eq.mp (hr (Ideal.Quotient.mk I (-s)))
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hbr
  let β := ε * b + 1
  have hβsub : β - 1 = ε * b := by dsimp only [β]; ring
  have hβdiv : β = m * (d + ε * t) := by
    calc
      β = ε * (b + s) + d * m := by dsimp only [β]; rw [← hsd]; ring
      _ = m * (d + ε * t) := by rw [ht]; ring
  refine ⟨β, ?_, ?_, ?_⟩
  · intro v
    rw [hβsub, map_mul]
    exact (mul_le_of_le_one_right bot_le (v.1.intValuation_le_one b)).trans_lt (hεT v)
  · intro v
    rw [hβdiv, map_mul]
    exact (mul_le_of_le_one_right bot_le (v.1.intValuation_le_one _)).trans_lt (hmW v)
  · intro w hw
    change w ((ε : K) * (b : K) + 1 - 1) < δ w
    rw [add_sub_cancel_right, map_mul]
    calc
      w (ε : K) * w (b : K) ≤ w (ε : K) * C w :=
        mul_le_mul_of_nonneg_left (hbound w _) (w.1.nonneg _)
      _ < (δ w / C w) * C w := mul_lt_mul_of_pos_right (hεinf w hw) (hCpos w)
      _ = δ w := div_mul_cancel₀ _ (hCpos w).ne'

end NormEuclidean.FiniteResidueScalarCorrection
