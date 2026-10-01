import TraceEuclidean.VoightResultantCertificates.FiveChunk4

/-! This generated module checks at most one hundred archived rows. -/

namespace TraceEuclidean

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact integer elimination needs an unbounded heartbeat budget.
theorem voightPolynomialRowsFiveChunk5_resultant_certificate :
    (voightPolynomialRowsFiveChunk5).all
      (voightResultantCertificate 5) = true := by
  native_decide

end TraceEuclidean
