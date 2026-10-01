import TraceEuclidean.VoightIntegralBasisCertificates.Chunk00
import TraceEuclidean.VoightIntegralBasisCertificates.Chunk01
import TraceEuclidean.VoightIntegralBasisCertificates.Chunk02
import TraceEuclidean.VoightIntegralBasisCertificates.Chunk03
import TraceEuclidean.VoightIntegralBasisCertificates.Chunk04
import TraceEuclidean.VoightIntegralBasisCertificates.Chunk05
import TraceEuclidean.VoightIntegralBasisCertificates.Chunk06
import TraceEuclidean.VoightIntegralBasisCertificates.Chunk07

/-! All squarefree, nontrivial-index Voight integral-basis certificates. -/

namespace TraceEuclidean

def voightSquarefreeNontrivialIndexCertificates :
    List VoightIntegralBasisCertificateEntry :=
  voightIntegralBasisCertificatesChunk00 ++
    voightIntegralBasisCertificatesChunk01 ++
    voightIntegralBasisCertificatesChunk02 ++
    voightIntegralBasisCertificatesChunk03 ++
    voightIntegralBasisCertificatesChunk04 ++
    voightIntegralBasisCertificatesChunk05 ++
    voightIntegralBasisCertificatesChunk06 ++
    voightIntegralBasisCertificatesChunk07

theorem voightSquarefreeNontrivialIndexCertificates_valid :
    List.Forall
      VoightIntegralBasisCertificateEntry.Valid
      voightSquarefreeNontrivialIndexCertificates := by
  dsimp [voightSquarefreeNontrivialIndexCertificates]
  simp only [List.forall_append]
  exact ⟨⟨⟨⟨⟨⟨⟨voightIntegralBasisCertificatesChunk00_check, voightIntegralBasisCertificatesChunk01_check⟩, voightIntegralBasisCertificatesChunk02_check⟩, voightIntegralBasisCertificatesChunk03_check⟩, voightIntegralBasisCertificatesChunk04_check⟩, voightIntegralBasisCertificatesChunk05_check⟩, voightIntegralBasisCertificatesChunk06_check⟩, voightIntegralBasisCertificatesChunk07_check⟩

/-- The generated certificate rows are exactly the archived
squarefree rows with recorded index greater than one. -/
theorem voightSquarefreeNontrivialIndexCertificates_complete :
    voightSquarefreeNontrivialIndexCertificates.map
        (·.row) =
      voightSquarefreeNontrivialIndexRows := by
  native_decide

end TraceEuclidean
