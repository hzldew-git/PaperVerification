import TraceEuclidean.VoightMaximalOrderExact.Chunk057
import TraceEuclidean.VoightMaximalOrderExact.Chunk058
import TraceEuclidean.VoightMaximalOrderExact.Chunk059
import TraceEuclidean.VoightMaximalOrderExact.Chunk060

set_option linter.all false

namespace TraceEuclidean

/-- Proof-carrying exact-field certificates for all 1,509 archived
rows with nonsquarefree recorded field discriminant. -/
def voightNonsquarefreeExactFieldCertificates :
    List VoightExactFieldCertificate :=
  VoightMaximalOrderExactChunk000.entries ++
    VoightMaximalOrderExactChunk001.entries ++
    VoightMaximalOrderExactChunk002.entries ++
    VoightMaximalOrderExactChunk003.entries ++
    VoightMaximalOrderExactChunk004.entries ++
    VoightMaximalOrderExactChunk005.entries ++
    VoightMaximalOrderExactChunk006.entries ++
    VoightMaximalOrderExactChunk007.entries ++
    VoightMaximalOrderExactChunk008.entries ++
    VoightMaximalOrderExactChunk009.entries ++
    VoightMaximalOrderExactChunk010.entries ++
    VoightMaximalOrderExactChunk011.entries ++
    VoightMaximalOrderExactChunk012.entries ++
    VoightMaximalOrderExactChunk013.entries ++
    VoightMaximalOrderExactChunk014.entries ++
    VoightMaximalOrderExactChunk015.entries ++
    VoightMaximalOrderExactChunk016.entries ++
    VoightMaximalOrderExactChunk017.entries ++
    VoightMaximalOrderExactChunk018.entries ++
    VoightMaximalOrderExactChunk019.entries ++
    VoightMaximalOrderExactChunk020.entries ++
    VoightMaximalOrderExactChunk021.entries ++
    VoightMaximalOrderExactChunk022.entries ++
    VoightMaximalOrderExactChunk023.entries ++
    VoightMaximalOrderExactChunk024.entries ++
    VoightMaximalOrderExactChunk025.entries ++
    VoightMaximalOrderExactChunk026.entries ++
    VoightMaximalOrderExactChunk027.entries ++
    VoightMaximalOrderExactChunk028.entries ++
    VoightMaximalOrderExactChunk029.entries ++
    VoightMaximalOrderExactChunk030.entries ++
    VoightMaximalOrderExactChunk031.entries ++
    VoightMaximalOrderExactChunk032.entries ++
    VoightMaximalOrderExactChunk033.entries ++
    VoightMaximalOrderExactChunk034.entries ++
    VoightMaximalOrderExactChunk035.entries ++
    VoightMaximalOrderExactChunk036.entries ++
    VoightMaximalOrderExactChunk037.entries ++
    VoightMaximalOrderExactChunk038.entries ++
    VoightMaximalOrderExactChunk039.entries ++
    VoightMaximalOrderExactChunk040.entries ++
    VoightMaximalOrderExactChunk041.entries ++
    VoightMaximalOrderExactChunk042.entries ++
    VoightMaximalOrderExactChunk043.entries ++
    VoightMaximalOrderExactChunk044.entries ++
    VoightMaximalOrderExactChunk045.entries ++
    VoightMaximalOrderExactChunk046.entries ++
    VoightMaximalOrderExactChunk047.entries ++
    VoightMaximalOrderExactChunk048.entries ++
    VoightMaximalOrderExactChunk049.entries ++
    VoightMaximalOrderExactChunk050.entries ++
    VoightMaximalOrderExactChunk051.entries ++
    VoightMaximalOrderExactChunk052.entries ++
    VoightMaximalOrderExactChunk053.entries ++
    VoightMaximalOrderExactChunk054.entries ++
    VoightMaximalOrderExactChunk055.entries ++
    VoightMaximalOrderExactChunk056.entries ++
    VoightMaximalOrderExactChunk057.entries ++
    VoightMaximalOrderExactChunk058.entries ++
    VoightMaximalOrderExactChunk059.entries ++
    VoightMaximalOrderExactChunk060.entries

/-- The generated certificate list contains exactly 1,509 rows. -/
theorem voightNonsquarefreeExactFieldCertificates_length :
    voightNonsquarefreeExactFieldCertificates.length = 1509 := by
  native_decide

/-- The generated proof-carrying list has exactly the same rows and
order as the executable nonsquarefree selector. -/
theorem voightNonsquarefreeExactFieldCertificates_complete :
    voightNonsquarefreeExactFieldCertificates.map (·.row) =
      voightNonsquarefreeFieldDiscriminantRows := by
  native_decide

/-- Every archived row with nonsquarefree recorded discriminant
presents an actual totally real field with exactly that discriminant. -/
theorem voightNonsquarefreeFieldDiscriminantRows_present_exactTotallyRealNumberField :
    ∀ row ∈ voightNonsquarefreeFieldDiscriminantRows,
      row.PresentsExactTotallyRealNumberField := by
  intro row hrow
  have hmapped :
      row ∈ voightNonsquarefreeExactFieldCertificates.map
        (·.row) := by
    rw [voightNonsquarefreeExactFieldCertificates_complete]
    exact hrow
  rcases List.mem_map.mp hmapped with ⟨entry, hentry, heq⟩
  subst row
  exact entry.exactness

/-- Every one of the 2,773 archived Voight rows now has exact field
semantics, including equality with its recorded field discriminant. -/
theorem allVoightPolynomialRows_present_exactTotallyRealNumberField :
    ∀ row ∈ allVoightPolynomialRows,
      row.PresentsExactTotallyRealNumberField := by
  intro row hrow
  by_cases hsquarefree : Squarefree row.fieldDiscriminant
  · apply
      voightSquarefreeFieldDiscriminantRows_present_exactTotallyRealNumberField
        row
    exact List.mem_filter.mpr
      ⟨hrow,
        (voightPolynomialRow_squarefreeFieldDiscriminant_iff row).2
          hsquarefree⟩
  · apply
      voightNonsquarefreeFieldDiscriminantRows_present_exactTotallyRealNumberField
        row
    exact List.mem_filter.mpr
      ⟨hrow,
        (voightPolynomialRow_nonsquarefreeFieldDiscriminant_iff row).2
          hsquarefree⟩

end TraceEuclidean
