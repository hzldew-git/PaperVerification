import TraceEuclidean.GeneralPowerIndex
import TraceEuclidean.VoightNumberFieldCore

/-!
# Order-index semantics for one certified polynomial row

This module contains the generic field-index bridge for a single row.  It has
no dependency on the aggregate archived certificate replay.
-/

namespace TraceEuclidean

noncomputable section

open NumberField Polynomial

/-- The root of a monic integral polynomial is integral over the integers
inside the rational `AdjoinRoot` algebra. -/
theorem voightAdjoinRoot_isIntegral
    (row : VoightPolynomialRow)
    (hmonic : row.polynomial.Monic) :
    IsIntegral ℤ (AdjoinRoot.root row.rationalPolynomial) := by
  have hroot := AdjoinRoot.eval₂_root row.rationalPolynomial
  refine ⟨row.polynomial, hmonic, ?_⟩
  change Polynomial.eval₂ (algebraMap ℤ (AdjoinRoot row.rationalPolynomial))
    (AdjoinRoot.root row.rationalPolynomial) row.polynomial = 0
  rw [IsScalarTower.algebraMap_eq ℤ ℚ
    (AdjoinRoot row.rationalPolynomial)]
  rw [AdjoinRoot.algebraMap_eq]
  rw [← Polynomial.eval₂_map]
  exact hroot

/-- The integral minimal polynomial of the canonical `AdjoinRoot` generator
is the certified integral polynomial. -/
theorem voightAdjoinRoot_minpoly
    (row : VoightPolynomialRow)
    (hmonic : row.polynomial.Monic)
    (hirr : Irreducible row.polynomial) :
    minpoly ℤ (AdjoinRoot.root row.rationalPolynomial) =
      row.polynomial := by
  let q := row.rationalPolynomial
  have hirrQ : Irreducible q := by
    dsimp [q, VoightPolynomialRow.rationalPolynomial]
    exact hmonic.irreducible_iff_irreducible_map_fraction_map.mp hirr
  letI : Fact (Irreducible q) := ⟨hirrQ⟩
  have hint : IsIntegral ℤ (AdjoinRoot.root q) := by
    simpa [q] using voightAdjoinRoot_isIntegral row hmonic
  have hminQ : minpoly ℚ (AdjoinRoot.root q) = q := by
    exact AdjoinRoot.minpoly_powerBasis_gen_of_monic
      (hmonic.map (Int.castRingHom ℚ))
  have hmap :
      minpoly ℚ (AdjoinRoot.root q) =
        (minpoly ℤ (AdjoinRoot.root q)).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
  have hmap' :
      minpoly ℚ (AdjoinRoot.root row.rationalPolynomial) =
        (minpoly ℤ (AdjoinRoot.root row.rationalPolynomial)).map
          (Int.castRingHom ℚ) := by
    simpa [q] using hmap
  have hminQ' :
      minpoly ℚ (AdjoinRoot.root row.rationalPolynomial) =
        row.rationalPolynomial := by
    simpa [q] using hminQ
  apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [← hmap', hminQ']
  rfl

/-- Cancelling two positive square-index discriminant identities shows that
the two indices agree exactly when the two field discriminants agree. -/
theorem positiveIndex_discriminant_eq_iff
    (actualIndex recordedIndex recordedDiscriminant : ℕ)
    (actualDiscriminant polynomialDiscriminant : ℤ)
    (hactualPos : 0 < actualIndex)
    (hrecordedPos : 0 < recordedIndex)
    (hrecordedDiscriminantPos : 0 < recordedDiscriminant)
    (hactual : polynomialDiscriminant =
      (actualIndex : ℤ) ^ 2 * actualDiscriminant)
    (hrecorded : polynomialDiscriminant =
      (recordedIndex : ℤ) ^ 2 * (recordedDiscriminant : ℤ)) :
    actualIndex = recordedIndex ↔
      actualDiscriminant = (recordedDiscriminant : ℤ) := by
  constructor
  · intro hindex
    have heq :
        (actualIndex : ℤ) ^ 2 * actualDiscriminant =
          (recordedIndex : ℤ) ^ 2 * (recordedDiscriminant : ℤ) :=
      hactual.symm.trans hrecorded
    rw [hindex] at heq
    have hfactor : (recordedIndex : ℤ) ^ 2 ≠ 0 := by
      positivity
    exact mul_left_cancel₀ hfactor heq
  · intro hdiscriminant
    have heq :
        (actualIndex : ℤ) ^ 2 * actualDiscriminant =
          (recordedIndex : ℤ) ^ 2 * (recordedDiscriminant : ℤ) :=
      hactual.symm.trans hrecorded
    rw [hdiscriminant] at heq
    have hfactor : (recordedDiscriminant : ℤ) ≠ 0 := by
      positivity
    have hsquares : (actualIndex : ℤ) ^ 2 =
        (recordedIndex : ℤ) ^ 2 :=
      mul_right_cancel₀ hfactor heq
    have hactualPos' : (0 : ℤ) < actualIndex := by
      exact_mod_cast hactualPos
    have hrecordedPos' : (0 : ℤ) < recordedIndex := by
      exact_mod_cast hrecordedPos
    have hcast : (actualIndex : ℤ) = recordedIndex := by
      nlinarith
    exact_mod_cast hcast

/-- Full order-index semantics for one certified row. -/
def VoightPolynomialRow.PresentsIndexedTotallyRealNumberField
    (row : VoightPolynomialRow) : Prop :=
  ∃ hirrQ : Irreducible row.rationalPolynomial,
    letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
    NumberField.IsTotallyReal (AdjoinRoot row.rationalPolynomial) ∧
      Module.finrank ℚ (AdjoinRoot row.rationalPolynomial) =
        row.polynomial.natDegree ∧
      ∃ a : RingOfIntegers (AdjoinRoot row.rationalPolynomial),
        (a : AdjoinRoot row.rationalPolynomial) =
            AdjoinRoot.root row.rationalPolynomial ∧
          minpoly ℤ (a : AdjoinRoot row.rationalPolynomial) =
            row.polynomial ∧
          IntermediateField.adjoin ℚ
              {(a : AdjoinRoot row.rationalPolynomial)} = ⊤ ∧
          ∃ actualIndex : ℕ, 0 < actualIndex ∧
            row.polynomial.discr =
              (actualIndex : ℤ) ^ 2 *
                NumberField.discr (AdjoinRoot row.rationalPolynomial) ∧
            (actualIndex = row.index ↔
              NumberField.discr (AdjoinRoot row.rationalPolynomial) =
                (row.fieldDiscriminant : ℤ))

/-- Monicity, irreducibility, real splitting, and a certified discriminant
identity give the full order-index presentation for one row. -/
theorem voightPolynomialRow_presentsIndexedTotallyRealNumberField
    (row : VoightPolynomialRow)
    (hmonic : row.polynomial.Monic)
    (hirr : Irreducible row.polynomial)
    (hsplits : row.realPolynomial.Splits)
    (hrecordedDiscriminantPos : 0 < row.fieldDiscriminant)
    (hrecordedIndexPos : 0 < row.index)
    (hrecorded : row.polynomial.discr =
      (row.index : ℤ) ^ 2 * (row.fieldDiscriminant : ℤ)) :
    row.PresentsIndexedTotallyRealNumberField := by
  have hirrQ : Irreducible row.rationalPolynomial := by
    rw [VoightPolynomialRow.rationalPolynomial]
    exact hmonic.irreducible_iff_irreducible_map_fraction_map.mp hirr
  refine ⟨hirrQ, ?_⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  change NumberField.IsTotallyReal (AdjoinRoot row.rationalPolynomial) ∧
    Module.finrank ℚ (AdjoinRoot row.rationalPolynomial) =
      row.polynomial.natDegree ∧ _
  have hreal : NumberField.IsTotallyReal
      (AdjoinRoot row.rationalPolynomial) := by
    apply adjoinRoot_isTotallyReal_of_splits_over_real
    rwa [rationalPolynomial_map_real]
  have hdegree :
      Module.finrank ℚ (AdjoinRoot row.rationalPolynomial) =
        row.polynomial.natDegree := by
    rw [adjoinRoot_finrank_eq_natDegree]
    exact hmonic.natDegree_map (Int.castRingHom ℚ)
  let a : RingOfIntegers (AdjoinRoot row.rationalPolynomial) :=
    ⟨AdjoinRoot.root row.rationalPolynomial,
      voightAdjoinRoot_isIntegral row hmonic⟩
  have hcoe : (a : AdjoinRoot row.rationalPolynomial) =
      AdjoinRoot.root row.rationalPolynomial := rfl
  have hmin : minpoly ℤ (a : AdjoinRoot row.rationalPolynomial) =
      row.polynomial := by
    change minpoly ℤ (AdjoinRoot.root row.rationalPolynomial) =
      row.polynomial
    exact voightAdjoinRoot_minpoly row hmonic hirr
  have hgen : IntermediateField.adjoin ℚ
      {(a : AdjoinRoot row.rationalPolynomial)} = ⊤ := by
    change IntermediateField.adjoin ℚ
      {AdjoinRoot.root row.rationalPolynomial} = ⊤
    let pb : PowerBasis ℚ (AdjoinRoot row.rationalPolynomial) :=
      AdjoinRoot.powerBasis hirrQ.ne_zero
    have hpb := pb.adjoin_gen_eq_top
    have hpgen : pb.gen = AdjoinRoot.root row.rationalPolynomial := by
      exact AdjoinRoot.powerBasis_gen hirrQ.ne_zero
    rw [hpgen] at hpb
    exact IntermediateField.adjoin_eq_top_of_algebra ℚ
      {AdjoinRoot.root row.rationalPolynomial} hpb
  obtain ⟨actualIndex, hactualIndexPos, hactual⟩ :=
    minpoly_discr_exists_positive_index
      (AdjoinRoot row.rationalPolynomial) row.polynomial.natDegree
        hdegree a hgen
  have hactual' : row.polynomial.discr =
      (actualIndex : ℤ) ^ 2 *
        NumberField.discr (AdjoinRoot row.rationalPolynomial) := by
    change (minpoly ℤ
      (AdjoinRoot.root row.rationalPolynomial)).discr =
        (actualIndex : ℤ) ^ 2 *
          NumberField.discr (AdjoinRoot row.rationalPolynomial) at hactual
    rw [voightAdjoinRoot_minpoly row hmonic hirr] at hactual
    exact hactual
  refine ⟨hreal, hdegree, a, hcoe, hmin, hgen, actualIndex,
    hactualIndexPos, hactual', ?_⟩
  exact positiveIndex_discriminant_eq_iff actualIndex row.index
    row.fieldDiscriminant
    (NumberField.discr (AdjoinRoot row.rationalPolynomial))
    row.polynomial.discr hactualIndexPos hrecordedIndexPos
    hrecordedDiscriminantPos hactual' hrecorded

end

end TraceEuclidean
