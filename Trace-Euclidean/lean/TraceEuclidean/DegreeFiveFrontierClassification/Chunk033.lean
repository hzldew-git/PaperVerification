import TraceEuclidean.DegreeFiveCertifiedCase
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk033

/-! Proof-bearing classification of quintic frontier chunk 033. -/

namespace TraceEuclidean

universe u

def degreeFiveCertifiedCasesChunk033 :
    List DegreeFiveCertifiedCase.{u} :=
  [
    DegreeFiveCertifiedCase.reducible
      [1, 3, -1, -4, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 3, -1, -4, 0, 1], [-1, 1], [-1, -4, -3, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [2, 4, -1, -4, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 4, -1, -4, 0, 1], [1, 1], [2, 2, -3, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 0, -4, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 0, -4, 0, 1], [0, 1], [1, 0, -4, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, 0, -4, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 0, -4, 0, 1], [0, 1], [2, 0, -4, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 3, 0, -4, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 3, 0, -4, 0, 1], [-1, 1, 1], [1, -2, -1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 3, 0, -4, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 0, -4, 0, 1], [-1, 1], [0, -3, -3, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 3, 0, -4, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 3, 0, -4, 0, 1], [-1, -1, 1], [-1, -2, 1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 4, 0, -4, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, 0, -4, 0, 1], [0, 1], [4, 0, -4, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 1, -4, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 1, -4, 0, 1], [0, 1], [0, 1, -4, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 1, -4, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 1, -4, 0, 1], [0, 1], [1, 1, -4, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, 1, -4, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 1, -4, 0, 1], [-1, 1], [0, -2, -3, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 3, 1, -4, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 3, 1, -4, 0, 1], [-1, 1], [1, -2, -3, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 4, 1, -4, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 4, 1, -4, 0, 1], [-1, 1], [2, -2, -3, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 2, -4, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 2, -4, 0, 1], [0, 1], [0, 2, -4, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 2, -4, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 2, -4, 0, 1], [-1, 1], [0, -1, -3, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 2, 2, -4, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 2, 2, -4, 0, 1], [-1, 1], [1, -1, -3, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 3, -4, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 3, -4, 0, 1], [-1, 1], [0, 0, -3, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 1, 3, -4, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 1, 3, -4, 0, 1], [-1, 1], [1, 0, -3, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -1, 4, -4, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -1, 4, -4, 0, 1], [0, 1], [-1, 4, -4, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, -2, -3, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, -2, -3, 0, 1], [-2, 1], [0, 0, 1, 2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, -1, -3, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, -1, -3, 0, 1], [0, 1], [0, -1, -3, 0, 1], 1, 4⟩ (by decide))
  ]

set_option linter.unnecessarySeqFocus false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation identifies the generated Rolle rows with their
-- proof-bearing classification cases.
theorem degreeFiveCertifiedCasesChunk033_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈
          (degreeFiveStageFiveEntriesChunk033.flatMap fun entry =>
            entry.a0Candidates.toList.map fun a0 =>
              [a0, entry.a1, entry.a2, entry.a3, entry.a4, 1]) ↔
        coefficients ∈
          degreeFiveCertifiedCasesChunk033.{u}.map
            DegreeFiveCertifiedCase.coefficients := by
  intro coefficients
  simp only [degreeFiveCertifiedCasesChunk033, List.map_cons, List.map_nil,
    DegreeFiveCertifiedCase.coefficients]
  norm_num [degreeFiveStageFiveEntriesChunk033,
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
