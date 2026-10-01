import TraceEuclidean.VoightResultantCertificates.SevenChunk0

/-! This generated module checks at most one hundred archived rows. -/

namespace TraceEuclidean

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact integer elimination needs an unbounded heartbeat budget.
theorem voightPolynomialRowsSevenChunk1_resultant_certificate :
    (voightPolynomialRowsSevenChunk1).all
      (voightResultantCertificate 7) = true := by
  native_decide

end TraceEuclidean
