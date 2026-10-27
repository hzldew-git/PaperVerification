import NormEuclidean.ChapterX.LocalSquareIndex
import Mathlib.NumberTheory.NumberField.ProductFormula

/-!
# Dyadic square indices at actual number-field completions

The normalized dyadic valuation and residue field are compared with the
actual completed valuation ring and the residue ring of the base prime.
This transports the proved unit-filtration count to the local factor
needed in O'Meara 65:7.
-/

noncomputable section

namespace NormEuclidean.DyadicSquareIndex

open IsDedekindDomain Bong.Dyadic LocalSquareIndex
open scoped NumberField WithZero

variable {K : Type*} [Field K] [NumberField K]

/-- The dyadic valuation-unit subgroup is the actual completed unit subgroup. -/
theorem units_eq (p : HeightOneSpectrum (𝓞 K)) (hp : (2 : 𝓞 K) ∈ p.asIdeal) :
    letI := Bong.NumberFieldCompletion.dyadicContext p hp
    LocalSquareIndex.units p = valuationUnitSubgroup (p.adicCompletion K) := by
  letI := Bong.NumberFieldCompletion.dyadicContext p hp
  ext a
  change Valued.v a.val = 1 ↔ Bong.NumberFieldCompletion.adicOrder p a.val = 0
  rw [Bong.NumberFieldCompletion.adicOrder_apply_of_ne_zero p a.ne_zero]
  constructor
  · intro h
    rw [h, WithZero.log_one, neg_zero]
    rfl
  · intro h
    have hl : -(WithZero.log (Valued.v a.val)) = (0 : ℤ) := by exact_mod_cast h
    have hn : Valued.v a.val ≠ (0 : ℤᵐ⁰) := (Valuation.ne_zero_iff _).mpr a.ne_zero
    have he := WithZero.exp_log hn
    rw [neg_eq_zero.mp hl, WithZero.exp_zero] at he
    exact he.symm

/-- The complete dyadic field square quotient has four residue-power factors. -/
theorem index (p : HeightOneSpectrum (𝓞 K)) (hp : (2 : 𝓞 K) ∈ p.asIdeal) :
    letI := Bong.NumberFieldCompletion.dyadicContext p hp
    (Subgroup.square ((p.adicCompletion K)ˣ)).index =
      4 * Nat.card (normalizedResidueField (p.adicCompletion K)) ^
        ramificationIndex (p.adicCompletion K) := by
  letI := Bong.NumberFieldCompletion.dyadicContext p hp
  rw [index_eq_two_mul_units, units_eq p hp]
  change 2 * Nat.card (ValuationUnitClass (p.adicCompletion K)) = _
  rw [card_valuationUnitClass]
  ring

/-- The normalized residue field has the absolute norm of the original prime. -/
theorem residue_card (p : HeightOneSpectrum (𝓞 K)) (hp : (2 : 𝓞 K) ∈ p.asIdeal) :
    letI := Bong.NumberFieldCompletion.dyadicContext p hp
    Nat.card (normalizedResidueField (p.adicCompletion K)) = Ideal.absNorm p.asIdeal := by
  letI := Bong.NumberFieldCompletion.dyadicContext p hp
  let F := p.adicCompletion K
  have he : normalizedValuationRing F = (Valued.v : Valuation F ℤᵐ⁰).valuationSubring := by
    apply (Valuation.isEquiv_iff_valuationSubring _ _).mp
    exact ValuativeRel.isEquiv _ _
  change Nat.card (IsLocalRing.ResidueField (normalizedValuationRing F)) = _
  rw [he]
  letI := Ideal.Quotient.field p.asIdeal
  let e := RingEquiv.ofBijective (Bong.NumberFieldCompletion.residueQuotientMap p)
    ⟨(Bong.NumberFieldCompletion.residueQuotientMap p).injective,
      Bong.NumberFieldCompletion.residueQuotientMap_surjective p⟩
  exact (Nat.card_congr e.toEquiv).symm.trans (Ideal.absNorm_apply p.asIdeal).symm

/-- The concrete dyadic ramification exponent is the negative logarithm of the value of two. -/
theorem ramification_eq (p : HeightOneSpectrum (𝓞 K)) (hp : (2 : 𝓞 K) ∈ p.asIdeal) :
    letI := Bong.NumberFieldCompletion.dyadicContext p hp
    (ramificationIndex (p.adicCompletion K) : ℤ) =
      -WithZero.log (Valued.v (2 : p.adicCompletion K)) := by
  letI := Bong.NumberFieldCompletion.dyadicContext p hp
  have h := ramificationIndex_spec (p.adicCompletion K)
  change ((ramificationIndex (p.adicCompletion K) : ℤ) : WithTop ℤ) =
    Bong.NumberFieldCompletion.adicOrder p (2 : p.adicCompletion K) at h
  rw [Bong.NumberFieldCompletion.adicOrder_apply_of_ne_zero p (by norm_num)] at h
  exact_mod_cast h

end NormEuclidean.DyadicSquareIndex
