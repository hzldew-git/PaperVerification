import NormEuclidean.ChapterX.DyadicSquareIndex

/-!
# Local square counts and the product-formula weight of two

At every finite number-field place, the square-subgroup index times
the normalized absolute value of two is four. The dyadic exponent
therefore cancels when the local counts are multiplied globally.
-/

noncomputable section

namespace NormEuclidean.FiniteSquareWeight

open IsDedekindDomain Bong.Dyadic
open scoped NumberField WithZero

variable {K : Type*} [Field K] [NumberField K]

/-- At an odd prime the product-formula weight of two is one. -/
theorem norm_two_odd (p : HeightOneSpectrum (𝓞 K))
    (hp : (2 : 𝓞 K) ∉ p.asIdeal) : ‖(2 : p.adicCompletion K)‖ = 1 := by
  have h := (NumberField.FinitePlace.norm_eq_one_iff_notMem K p (2 : 𝓞 K)).mpr hp
  have he : NumberField.FinitePlace.embedding p ((algebraMap (𝓞 K) K) 2) =
      (2 : p.adicCompletion K) := by
    change algebraMap K (p.adicCompletion K) ((algebraMap (𝓞 K) K) 2) = 2
    rw [map_ofNat, map_ofNat]
  rwa [he] at h

/-- The dyadic weight of two is the inverse ramification power of the residue norm. -/
theorem norm_two_dyadic (p : HeightOneSpectrum (𝓞 K))
    (hp : (2 : 𝓞 K) ∈ p.asIdeal) :
    letI := Bong.NumberFieldCompletion.dyadicContext p hp
    ‖(2 : p.adicCompletion K)‖ =
      (Ideal.absNorm p.asIdeal : ℝ) ^ (-(ramificationIndex (p.adicCompletion K) : ℤ)) := by
  letI := Bong.NumberFieldCompletion.dyadicContext p hp
  have hn : Valued.v (2 : p.adicCompletion K) ≠ (0 : ℤᵐ⁰) :=
    (Valuation.ne_zero_iff _).mpr (by norm_num)
  rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hn]
  rw [NNReal.coe_zpow]
  congr 1
  calc
    (WithZero.unzero hn).toAdd = WithZero.log
        (↑(WithZero.unzero hn) : ℤᵐ⁰) := rfl
    _ = -(ramificationIndex (p.adicCompletion K) : ℤ) := by
      rw [WithZero.coe_unzero]
      exact (neg_eq_iff_eq_neg.mpr (DyadicSquareIndex.ramification_eq p hp)).symm

/-- The local square index and the normalized weight of two multiply to four. -/
theorem index_mul_two (p : HeightOneSpectrum (𝓞 K)) :
    ((Subgroup.square ((p.adicCompletion K)ˣ)).index : ℝ) *
      ‖(2 : p.adicCompletion K)‖ = 4 := by
  classical
  by_cases hp : (2 : 𝓞 K) ∈ p.asIdeal
  · letI := Bong.NumberFieldCompletion.dyadicContext p hp
    rw [DyadicSquareIndex.index p hp, DyadicSquareIndex.residue_card p hp,
      norm_two_dyadic p hp]
    have hq : (Ideal.absNorm p.asIdeal : ℝ) ≠ 0 := by
      exact_mod_cast (NumberField.HeightOneSpectrum.absNorm_ne_zero p)
    push_cast
    rw [zpow_neg, zpow_natCast]
    field_simp
  · rw [LocalSquareIndex.odd_index p hp, norm_two_odd p hp]
    norm_num

end NormEuclidean.FiniteSquareWeight
