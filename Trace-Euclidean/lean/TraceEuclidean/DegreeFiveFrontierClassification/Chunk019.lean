import TraceEuclidean.DegreeFiveCertifiedCase
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk019

/-! Proof-bearing classification of quintic frontier chunk 019. -/

namespace TraceEuclidean

universe u

def degreeFiveCertifiedCasesChunk019 :
    List DegreeFiveCertifiedCase.{u} :=
  [
    DegreeFiveCertifiedCase.reducible
      [0, -4, 10, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -4, 10, -6, -1, 1], [-2, 1], [0, 2, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, -3, 10, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, -3, 10, -6, -1, 1], [-1, 1], [1, 4, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, -2, 10, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, -2, 10, -6, -1, 1], [-1, 1], [2, 4, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, -6, 11, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, -6, 11, -6, -1, 1], [-1, 1], [-1, 5, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -5, 11, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -5, 11, -6, -1, 1], [0, 1], [-5, 11, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, -7, 12, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, -7, 12, -6, -1, 1], [-1, 1], [-1, 6, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [2, -9, 13, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, -9, 13, -6, -1, 1], [-1, 1], [-2, 7, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, -3, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, -3, -5, -1, 1], [-3, 1], [0, 0, 1, 2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, -2, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, -2, -5, -1, 1], [0, 1], [0, -2, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, -2, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, -2, -5, -1, 1], [0, 1], [1, -2, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 2, -2, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 2, -2, -5, -1, 1], [1, 1], [1, 1, -3, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, -1, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, -1, -5, -1, 1], [0, 1], [0, -1, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, -1, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, -1, -5, -1, 1], [0, 1], [1, -1, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, -1, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, -1, -5, -1, 1], [0, 1], [2, -1, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 3, -1, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 3, -1, -5, -1, 1], [1, 1], [1, 2, -3, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [2, 4, -1, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 4, -1, -5, -1, 1], [-1, 1], [-2, -6, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 0, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 0, -5, -1, 1], [0, 1], [1, 0, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, 0, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 0, -5, -1, 1], [0, 1], [2, 0, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 3, 0, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 0, -5, -1, 1], [0, 1], [3, 0, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 4, 0, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 4, 0, -5, -1, 1], [-1, 1], [-1, -5, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [2, 5, 0, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 5, 0, -5, -1, 1], [1, 1], [2, 3, -3, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [3, 6, 0, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[3, 6, 0, -5, -1, 1], [1, 1], [3, 3, -3, -2, 1], 1, 4⟩ (by decide))
  ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation identifies the generated Rolle rows with their
-- proof-bearing classification cases.
theorem degreeFiveCertifiedCasesChunk019_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈
          (degreeFiveStageFiveEntriesChunk019.flatMap fun entry =>
            entry.a0Candidates.toList.map fun a0 =>
              [a0, entry.a1, entry.a2, entry.a3, entry.a4, 1]) ↔
        coefficients ∈
          degreeFiveCertifiedCasesChunk019.{u}.map
            DegreeFiveCertifiedCase.coefficients := by
  intro coefficients
  simp only [degreeFiveCertifiedCasesChunk019, List.map_cons, List.map_nil,
    DegreeFiveCertifiedCase.coefficients]
  norm_num [degreeFiveStageFiveEntriesChunk019,
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
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat]

end TraceEuclidean
