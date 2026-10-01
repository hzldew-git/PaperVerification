import TraceEuclidean.VoightResultantCertificates.SixChunk6

/-! This generated module checks at most one hundred archived rows. -/

namespace TraceEuclidean

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exact integer elimination needs an unbounded heartbeat budget.
theorem voightPolynomialRowsSixChunk7_resultant_certificate :
    (voightPolynomialRowsSixChunk7).all
      (voightResultantCertificate 6) = true := by
  native_decide

end TraceEuclidean
