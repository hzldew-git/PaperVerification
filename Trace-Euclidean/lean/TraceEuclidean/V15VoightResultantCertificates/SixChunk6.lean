import TraceEuclidean.V15VoightResultantCertificates.SixChunk5

/-! This generated module checks at most one hundred archived rows. -/

namespace TraceEuclidean

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact integer elimination needs an unbounded heartbeat budget.
theorem v15_voightPolynomialRowsSixChunk6_resultant_certificate :
    (v15VoightPolynomialRowsSixChunk6).all
      (v15VoightResultantCertificate 6) = true := by
  native_decide

end TraceEuclidean
