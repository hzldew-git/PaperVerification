import TraceEuclidean.V15VoightResultantCertificates.EightChunk0

/-! This generated module checks at most one hundred archived rows. -/

namespace TraceEuclidean

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact integer elimination needs an unbounded heartbeat budget.
theorem v15_voightPolynomialRowsEightChunk1_resultant_certificate :
    (v15VoightPolynomialRowsEightChunk1).all
      (v15VoightResultantCertificate 8) = true := by
  native_decide

end TraceEuclidean
