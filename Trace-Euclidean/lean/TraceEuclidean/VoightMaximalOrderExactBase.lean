import TraceEuclidean.VoightSquarefreeExact

/-!
# Exact-field certificate aggregation for nonsquarefree Voight rows

The generated maximal-order modules prove one exact field-discriminant theorem
per archived row.  This file supplies the small proof-carrying record and the
executable selector used to aggregate those theorems into one public endpoint.
-/

namespace TraceEuclidean

/-- One archived row together with a proof that it presents an actual totally
real field having exactly the recorded field discriminant. -/
structure VoightExactFieldCertificate where
  row : VoightPolynomialRow
  exactness : row.PresentsExactTotallyRealNumberField

/-- Executable selector for rows whose recorded field discriminant is not
squarefree. -/
def VoightPolynomialRow.nonsquarefreeFieldDiscriminant
    (row : VoightPolynomialRow) : Bool :=
  decide (¬ Squarefree row.fieldDiscriminant)

/-- The executable selector has the expected mathematical meaning. -/
theorem voightPolynomialRow_nonsquarefreeFieldDiscriminant_iff
    (row : VoightPolynomialRow) :
    row.nonsquarefreeFieldDiscriminant = true ↔
      ¬ Squarefree row.fieldDiscriminant := by
  simp [VoightPolynomialRow.nonsquarefreeFieldDiscriminant]

/-- All archived rows whose recorded field discriminant is nonsquarefree. -/
def voightNonsquarefreeFieldDiscriminantRows :
    List VoightPolynomialRow :=
  allVoightPolynomialRows.filter
    VoightPolynomialRow.nonsquarefreeFieldDiscriminant

end TraceEuclidean
