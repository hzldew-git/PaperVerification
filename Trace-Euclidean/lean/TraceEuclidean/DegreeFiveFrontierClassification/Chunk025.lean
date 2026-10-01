import TraceEuclidean.DegreeFiveCertifiedCase
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk025

/-! Proof-bearing classification of quintic frontier chunk 025. -/

namespace TraceEuclidean

universe u

def degreeFiveCertifiedCasesChunk025 :
    List DegreeFiveCertifiedCase.{u} :=
  [
    DegreeFiveCertifiedCase.reducible
      [-2, 2, 3, -3, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 2, 3, -3, -1, 1], [1, 1], [-2, 4, -1, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -1, 4, -3, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -1, 4, -3, -1, 1], [-1, 1], [0, 1, -3, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 0, 4, -3, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 0, 4, -3, -1, 1], [-1, 1], [1, 1, -3, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 1, -2, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 1, -2, -1, 1], [0, 1], [0, 1, -2, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 1, -2, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 1, -2, -1, 1], [-1, 1], [0, -1, -2, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 2, -2, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 2, -2, -1, 1], [-1, 1], [0, 0, -2, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -1, 3, -2, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -1, 3, -2, -1, 1], [0, 1], [-1, 3, -2, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 1, -1, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 1, -1, -1, 1], [1, 1], [0, 0, 1, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -2, -7, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -2, -7, -6, 0, 1], [0, 1], [-2, -7, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, -1, -7, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, -1, -7, -6, 0, 1], [1, 1], [1, -2, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -1, -6, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -1, -6, -6, 0, 1], [0, 1], [-1, -6, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 0, -6, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 0, -6, -6, 0, 1], [1, 1], [1, -1, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [2, 1, -6, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 1, -6, -6, 0, 1], [1, 1], [2, -1, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -1, -5, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -1, -5, -6, 0, 1], [0, 1], [-1, -5, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, -5, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, -5, -6, 0, 1], [1, 1], [0, 0, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 1, -5, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 1, -5, -6, 0, 1], [1, 1], [1, 0, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [2, 2, -5, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 2, -5, -6, 0, 1], [1, 1], [2, 0, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [3, 3, -5, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[3, 3, -5, -6, 0, 1], [1, 1], [3, 0, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, -4, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, -4, -6, 0, 1], [2, 1], [0, 0, -2, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, -4, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, -4, -6, 0, 1], [0, 1], [1, -4, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, -4, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, -4, -6, 0, 1], [0, 1], [2, -4, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 2, -4, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 2, -4, -6, 0, 1], [1, 1], [1, 1, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 3, -4, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 3, -4, -6, 0, 1], [-1, 1, 1], [-1, -4, -1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [2, 3, -4, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 3, -4, -6, 0, 1], [1, 1], [2, 1, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [3, 4, -4, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[3, 4, -4, -6, 0, 1], [1, 1], [3, 1, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [4, 5, -4, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[4, 5, -4, -6, 0, 1], [-1, 1], [-4, -9, -5, 1, 1], 1, 4⟩ (by decide))
  ]

set_option linter.unnecessarySeqFocus false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation identifies the generated Rolle rows with their
-- proof-bearing classification cases.
theorem degreeFiveCertifiedCasesChunk025_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈
          (degreeFiveStageFiveEntriesChunk025.flatMap fun entry =>
            entry.a0Candidates.toList.map fun a0 =>
              [a0, entry.a1, entry.a2, entry.a3, entry.a4, 1]) ↔
        coefficients ∈
          degreeFiveCertifiedCasesChunk025.{u}.map
            DegreeFiveCertifiedCase.coefficients := by
  intro coefficients
  simp only [degreeFiveCertifiedCasesChunk025, List.map_cons, List.map_nil,
    DegreeFiveCertifiedCase.coefficients]
  norm_num [degreeFiveStageFiveEntriesChunk025,
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
