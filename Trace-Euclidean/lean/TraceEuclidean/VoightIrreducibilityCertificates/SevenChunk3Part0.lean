import TraceEuclidean.VoightIrreducibilityCertificates.SevenChunk2Part0

/-! Generated Rabin certificates for at most one hundred rows. -/

namespace TraceEuclidean

set_option linter.style.longLine false
set_option maxRecDepth 100000

def voightRabinCertificatesSevenChunk3Part0 :
    List RabinIrreducibilityCertificate :=
  [
    ⟨2,
      [[0, 1], [0, 0, 1], [0, 0, 0, 0, 1], [0, 1, 0, 1, 1, 1], [1, 1, 0, 1], [1, 0, 1, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 1], [0, 1]],
      [[], [], [0, 1], [1, 1, 0, 1], [], [1, 1, 1, 0, 0, 1], [0, 1, 1, 1, 0, 1]],
      [[], [1], [], [], [], [], []],
      [[], [0, 1, 0, 1, 1, 1], [], [], [], [], []]⟩
  ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Native replay is exact but intentionally has no heartbeat limit.
theorem voightRabinCertificatesSevenChunk3Part0_check :
    rabinCertificateBatchCheck 7
      (((voightPolynomialRowsSevenChunk3.drop 0).take 1).filter fun row => decide (row ∉ voightRabinExceptionsSeven)) voightRabinCertificatesSevenChunk3Part0 = true := by
  native_decide

theorem voightRowsSevenChunk3Part0_irreducible :
    ∀ row ∈ (((voightPolynomialRowsSevenChunk3.drop 0).take 1).filter fun row => decide (row ∉ voightRabinExceptionsSeven)), Irreducible row.polynomial :=
  irreducible_of_batchCheck_eq_true 7
    (certificates := voightRabinCertificatesSevenChunk3Part0) voightRabinCertificatesSevenChunk3Part0_check

end TraceEuclidean
