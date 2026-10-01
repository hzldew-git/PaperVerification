import TraceEuclidean.VoightIntegralBasisCertificates
import TraceEuclidean.VoightSquarefreeIndexOne

/-! Exact field discriminants for all squarefree Voight rows. -/

namespace TraceEuclidean

/-- Exactly 156 archived squarefree rows have recorded power-order index
greater than one. -/
theorem voightSquarefreeNontrivialIndexRows_length :
    voightSquarefreeNontrivialIndexRows.length = 156 := by
  native_decide

/-- Every archived squarefree row of nontrivial recorded index is closed by
one of the generated integral-basis certificates. -/
theorem voightSquarefreeNontrivialIndexRows_present_exactTotallyRealNumberField :
    ∀ row ∈ voightSquarefreeNontrivialIndexRows,
      row.PresentsExactTotallyRealNumberField := by
  intro row hrow
  have hmapped :
      row ∈ voightSquarefreeNontrivialIndexCertificates.map
        (·.row) := by
    rw [voightSquarefreeNontrivialIndexCertificates_complete]
    exact hrow
  rcases List.mem_map.mp hmapped with
    ⟨entry, hentry, heq⟩
  subst row
  have hentryValid :=
    (List.forall_iff_forall_mem.mp
      voightSquarefreeNontrivialIndexCertificates_valid)
      entry hentry
  rcases hentryValid with ⟨hdegreePositive, hsource, hcertificate⟩
  have hstructural :=
    (List.all_eq_true.mp
      (voightPolynomialRows_structural_certificate entry.degree))
      entry.row hsource
  have hconditions :=
    (voightPolynomialRow_structurallyValid_iff
      entry.degree entry.row).1 hstructural
  have hdegree := voightPolynomial_isMonicOfDegree
    entry.degree entry.row hconditions.1 hconditions.2.1
  have hfiltered := List.mem_filter.mp hrow
  have hsquarefree :=
    (voightPolynomialRow_squarefreeNontrivialIndex_iff
      entry.row).1 hfiltered.2
  have hrecorded :=
    voightPolynomialRow_recordedIndexData hsource
  exact
    voightPolynomialRow_presentsExactTotallyRealNumberField_of_integralBasisCertificate
      entry.degree entry.row entry.certificate hdegreePositive hdegree
        (allVoightPolynomialRows_irreducible entry.row hfiltered.1)
        (allVoightPolynomialRows_splits entry.row hfiltered.1)
        hsquarefree.1 hrecorded.2.2 hcertificate

/-- Executable selector for every archived row with squarefree recorded field
discriminant. -/
def VoightPolynomialRow.squarefreeFieldDiscriminant
    (row : VoightPolynomialRow) : Bool :=
  decide (Squarefree row.fieldDiscriminant)

/-- The selector states exactly squarefreeness of the recorded field
discriminant. -/
theorem voightPolynomialRow_squarefreeFieldDiscriminant_iff
    (row : VoightPolynomialRow) :
    row.squarefreeFieldDiscriminant = true ↔
      Squarefree row.fieldDiscriminant := by
  simp [VoightPolynomialRow.squarefreeFieldDiscriminant]

/-- All archived rows with squarefree recorded field discriminant. -/
def voightSquarefreeFieldDiscriminantRows :
    List VoightPolynomialRow :=
  allVoightPolynomialRows.filter
    VoightPolynomialRow.squarefreeFieldDiscriminant

/-- Exactly 1,264 archived rows have squarefree recorded field
discriminant. -/
theorem voightSquarefreeFieldDiscriminantRows_length :
    voightSquarefreeFieldDiscriminantRows.length = 1264 := by
  native_decide

/-- Every archived row with squarefree recorded field discriminant presents
an actual totally real number field having exactly that discriminant. -/
theorem voightSquarefreeFieldDiscriminantRows_present_exactTotallyRealNumberField :
    ∀ row ∈ voightSquarefreeFieldDiscriminantRows,
      row.PresentsExactTotallyRealNumberField := by
  intro row hrow
  have hfiltered := List.mem_filter.mp hrow
  have hsquarefree :=
    (voightPolynomialRow_squarefreeFieldDiscriminant_iff row).1
      hfiltered.2
  have hdata :=
    allVoightPolynomialRows_recordedIndexData row hfiltered.1
  by_cases hindex : row.index = 1
  · apply
      voightSquarefreeIndexOneRows_present_exactTotallyRealNumberField
        row
    exact List.mem_filter.mpr
      ⟨hfiltered.1,
        (voightPolynomialRow_squarefreeIndexOne_iff row).2
          ⟨hindex, hsquarefree⟩⟩
  · have hnontrivial : 1 < row.index := by omega
    apply
      voightSquarefreeNontrivialIndexRows_present_exactTotallyRealNumberField
        row
    exact List.mem_filter.mpr
      ⟨hfiltered.1,
        (voightPolynomialRow_squarefreeNontrivialIndex_iff row).2
          ⟨hsquarefree, hnontrivial⟩⟩

end TraceEuclidean
