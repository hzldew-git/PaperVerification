import TraceEuclidean.V15VoightResultantCertificates.FiveChunk5

/-! This generated module checks at most one hundred archived rows. -/

namespace TraceEuclidean

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact integer elimination needs an unbounded heartbeat budget.
theorem v15_voightPolynomialRowsFiveChunk6_resultant_certificate :
    (v15VoightPolynomialRowsFiveChunk6).all
      (v15VoightResultantCertificate 5) = true := by
  native_decide

end TraceEuclidean
