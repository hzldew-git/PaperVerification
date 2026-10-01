import TraceEuclidean.VoightResultantCertificates.EightChunk1

/-! This generated module checks at most one hundred archived rows. -/

namespace TraceEuclidean

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact integer elimination needs an unbounded heartbeat budget.
theorem voightPolynomialRowsNineChunk0_resultant_certificate :
    (voightPolynomialRowsNineChunk0).all
      (voightResultantCertificate 9) = true := by
  native_decide

end TraceEuclidean
