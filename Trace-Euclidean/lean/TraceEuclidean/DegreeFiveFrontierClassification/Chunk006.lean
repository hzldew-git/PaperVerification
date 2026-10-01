import TraceEuclidean.DegreeFiveCertifiedCase
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk006
import TraceEuclidean.DegreeFiveCriticalMaximalOrder.Row07

/-! Proof-bearing classification of quintic frontier chunk 006. -/

namespace TraceEuclidean

universe u

def degreeFiveCertifiedCasesChunk006 :
    List DegreeFiveCertifiedCase.{u} :=
  [
    DegreeFiveCertifiedCase.reducible
      [1, -8, 13, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, -8, 13, -5, -2, 1], [-1, 1], [-1, 7, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -7, 13, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -7, 13, -5, -2, 1], [-1, 1], [0, 7, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.critical
      DegreeFiveCritical07.row
      (by norm_num [DegreeFiveCritical07.row])
      (by
        intro K _ _ a hpoly hgen
        exact DegreeFiveCritical07.field_discriminant_eq_recorded_of_minpoly
          a (by simpa [DegreeFiveCritical07.T] using hpoly) hgen),
    DegreeFiveCertifiedCase.reducible
      [-1, -6, 13, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, -6, 13, -5, -2, 1], [-1, 1], [1, 7, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -6, 13, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -6, 13, -5, -2, 1], [-2, 1], [0, 3, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, -5, 13, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, -5, 13, -5, -2, 1], [-2, 1], [1, 3, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [2, -10, 14, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, -10, 14, -5, -2, 1], [-1, 1], [-2, 8, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, -9, 14, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, -9, 14, -5, -2, 1], [-1, 1], [-1, 8, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -8, 14, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -8, 14, -5, -2, 1], [-2, 1], [0, 4, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [3, -12, 15, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[3, -12, 15, -5, -2, 1], [-1, 1], [-3, 9, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [2, -11, 15, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, -11, 15, -5, -2, 1], [-2, 1], [-1, 5, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [4, -14, 16, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[4, -14, 16, -5, -2, 1], [-2, 1], [-2, 6, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, -1, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, -1, -4, -2, 1], [1, 1], [0, 0, -1, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 0, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 0, -4, -2, 1], [0, 1], [1, 0, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 1, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 1, -4, -2, 1], [0, 1], [0, 1, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 1, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 1, -4, -2, 1], [0, 1], [1, 1, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, 1, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 1, -4, -2, 1], [0, 1], [2, 1, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 2, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 2, -4, -2, 1], [0, 1], [0, 2, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 2, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 2, -4, -2, 1], [0, 1], [1, 2, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, 2, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 2, -4, -2, 1], [0, 1], [2, 2, -4, -2, 1], 1, 4⟩ (by decide))
  ]

set_option linter.unnecessarySeqFocus false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation identifies the generated Rolle rows with their
-- proof-bearing classification cases.
theorem degreeFiveCertifiedCasesChunk006_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈
          (degreeFiveStageFiveEntriesChunk006.flatMap fun entry =>
            entry.a0Candidates.toList.map fun a0 =>
              [a0, entry.a1, entry.a2, entry.a3, entry.a4, 1]) ↔
        coefficients ∈
          degreeFiveCertifiedCasesChunk006.{u}.map
            DegreeFiveCertifiedCase.coefficients := by
  intro coefficients
  simp only [degreeFiveCertifiedCasesChunk006, List.map_cons, List.map_nil,
    DegreeFiveCertifiedCase.coefficients]
  norm_num [degreeFiveStageFiveEntriesChunk006,
    DegreeFiveCritical07.row,
    DegreeFiveStageFiveEntry.a0Candidates,
    DegreeFiveStageFiveEntry.baseCoefficients,
    quinticTranslationCandidates, integerIcc,
    quinticTranslationLowerBound, quinticTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    (aesop (config := { warnOnNonterminal := false }) <;> omega)

end TraceEuclidean
