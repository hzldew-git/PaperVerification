import TraceEuclidean.VoightResultantCertificates.NineChunk0

/-! This generated module checks at most one hundred archived rows. -/

namespace TraceEuclidean

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact integer elimination needs an unbounded heartbeat budget.
theorem voightPolynomialRowsTenChunk0_resultant_certificate :
    (voightPolynomialRowsTenChunk0).all
      (voightResultantCertificate 10) = true := by
  native_decide

end TraceEuclidean
