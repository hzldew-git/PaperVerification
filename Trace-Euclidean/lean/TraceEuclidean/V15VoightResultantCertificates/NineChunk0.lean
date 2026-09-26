import TraceEuclidean.V15VoightResultantCertificates.EightChunk1

/-! This generated module checks at most one hundred archived rows. -/

namespace TraceEuclidean

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact integer elimination needs an unbounded heartbeat budget.
theorem v15_voightPolynomialRowsNineChunk0_resultant_certificate :
    (v15VoightPolynomialRowsNineChunk0).all
      (v15VoightResultantCertificate 9) = true := by
  native_decide

end TraceEuclidean
