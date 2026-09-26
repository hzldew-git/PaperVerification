import TraceEuclidean.V15VoightIrreducibilityCertificates.SevenChunk2Part0

/-! Generated Rabin certificates for at most one hundred rows. -/

namespace TraceEuclidean

set_option linter.style.longLine false
set_option maxRecDepth 100000

def v15VoightRabinCertificatesSevenChunk3Part0 :
    List V15RabinIrreducibilityCertificate :=
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
theorem v15_voightRabinCertificatesSevenChunk3Part0_check :
    v15RabinCertificateBatchCheck 7
      (((v15VoightPolynomialRowsSevenChunk3.drop 0).take 1).filter fun row => decide (row ∉ v15VoightRabinExceptionsSeven)) v15VoightRabinCertificatesSevenChunk3Part0 = true := by
  native_decide

theorem v15_voightRowsSevenChunk3Part0_irreducible :
    ∀ row ∈ (((v15VoightPolynomialRowsSevenChunk3.drop 0).take 1).filter fun row => decide (row ∉ v15VoightRabinExceptionsSeven)), Irreducible row.polynomial :=
  v15_irreducible_of_batchCheck_eq_true 7
    (certificates := v15VoightRabinCertificatesSevenChunk3Part0) v15_voightRabinCertificatesSevenChunk3Part0_check

end TraceEuclidean
