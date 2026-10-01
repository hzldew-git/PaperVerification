import TraceEuclidean.VoightOrderIndexCore
import TraceEuclidean.GeneralPowerIndex
import TraceEuclidean.VoightNumberFieldBridge

/-!
# Integral generators and order indices for the archived Voight rows

Every archived monic irreducible polynomial defines an integral primitive
generator of its `AdjoinRoot` number field.  This module connects the
polynomial discriminant to the actual field discriminant through the index
of the generator's power order.

For an archived row, the checked polynomial identity uses the recorded
`index` and `fieldDiscriminant`.  Comparing the two identities proves that
the recorded field discriminant is the actual one exactly when the recorded
index is the actual power-order index.  Thus the remaining maximal-order
certificate has a precise Lean statement.
-/

namespace TraceEuclidean

noncomputable section

open NumberField Polynomial

/-- One archived degree table supplies the positive recorded values and the
checked polynomial discriminant identity for every row it contains. -/
theorem voightPolynomialRow_recordedIndexData
    {degree : ℕ} {row : VoightPolynomialRow}
    (hrow : row ∈ voightPolynomialRows degree) :
    0 < row.fieldDiscriminant ∧ 0 < row.index ∧
      row.polynomial.discr =
        (row.index : ℤ) ^ 2 * (row.fieldDiscriminant : ℤ) := by
  have hvalid :=
    (List.all_eq_true.mp
      (voightPolynomialRows_structural_certificate degree)) row hrow
  have hconditions :=
    (voightPolynomialRow_structurallyValid_iff degree row).1 hvalid
  exact ⟨hconditions.2.2.1, hconditions.2.2.2,
    voightPolynomialDiscriminantInput degree row hrow⟩

/-- All 2,773 archived rows carry positive recorded data and the exact
checked polynomial discriminant identity. -/
theorem allVoightPolynomialRows_recordedIndexData :
    ∀ row ∈ allVoightPolynomialRows,
      0 < row.fieldDiscriminant ∧ 0 < row.index ∧
        row.polynomial.discr =
          (row.index : ℤ) ^ 2 * (row.fieldDiscriminant : ℤ) := by
  dsimp [allVoightPolynomialRows]
  exact forall_mem_append
    (fun row hrow ↦ voightPolynomialRow_recordedIndexData
      (degree := 5) (by simpa [voightPolynomialRows] using hrow))
    (forall_mem_append
      (fun row hrow ↦ voightPolynomialRow_recordedIndexData
        (degree := 6) (by simpa [voightPolynomialRows] using hrow))
      (forall_mem_append
        (fun row hrow ↦ voightPolynomialRow_recordedIndexData
          (degree := 7) (by simpa [voightPolynomialRows] using hrow))
        (forall_mem_append
          (fun row hrow ↦ voightPolynomialRow_recordedIndexData
            (degree := 8) (by simpa [voightPolynomialRows] using hrow))
          (forall_mem_append
            (fun row hrow ↦ voightPolynomialRow_recordedIndexData
              (degree := 9) (by simpa [voightPolynomialRows] using hrow))
            (fun row hrow ↦ voightPolynomialRow_recordedIndexData
              (degree := 10) (by simpa [voightPolynomialRows] using hrow))))))

/-- Every archived row presents a totally real number field together with an
actual positive power-order index.  Equality with the recorded index is
equivalent to equality of the actual and recorded field discriminants. -/
theorem allVoightPolynomialRows_present_indexedTotallyRealNumberField :
    ∀ row ∈ allVoightPolynomialRows,
      row.PresentsIndexedTotallyRealNumberField := by
  intro row hrow
  have hdata := allVoightPolynomialRows_recordedIndexData row hrow
  exact voightPolynomialRow_presentsIndexedTotallyRealNumberField row
    (allVoightPolynomialRows_monic row hrow)
    (allVoightPolynomialRows_irreducible row hrow)
    (allVoightPolynomialRows_splits row hrow)
    hdata.1 hdata.2.1 hdata.2.2

end

end TraceEuclidean
