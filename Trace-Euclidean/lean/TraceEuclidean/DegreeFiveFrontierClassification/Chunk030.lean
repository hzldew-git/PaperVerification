import TraceEuclidean.DegreeFiveCertifiedCase
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk030
import TraceEuclidean.DegreeFiveSafeResultants.Row210
import TraceEuclidean.DegreeFiveSafeResultants.Row211

/-! Proof-bearing classification of quintic frontier chunk 030. -/

namespace TraceEuclidean

universe u

def degreeFiveCertifiedCasesChunk030 :
    List DegreeFiveCertifiedCase.{u} :=
  [
    DegreeFiveCertifiedCase.reducible
      [-1, -1, 7, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, -1, 7, -6, 0, 1], [-1, 1], [1, 2, -5, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -2, -6, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -2, -6, -5, 0, 1], [0, 1], [-2, -6, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -1, -5, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -1, -5, -5, 0, 1], [0, 1], [-1, -5, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, -4, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, -4, -5, 0, 1], [1, 1], [0, 0, -4, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 1, -4, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 1, -4, -5, 0, 1], [1, 1], [1, 0, -4, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [2, 2, -4, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 2, -4, -5, 0, 1], [1, 1], [2, 0, -4, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, -3, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, -3, -5, 0, 1], [0, 1], [0, -3, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, -3, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, -3, -5, 0, 1], [0, 1], [1, -3, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 2, -3, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 2, -3, -5, 0, 1], [1, 1], [1, 1, -4, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [2, 3, -3, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 3, -3, -5, 0, 1], [1, 1], [2, 1, -4, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [3, 4, -3, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[3, 4, -3, -5, 0, 1], [-1, 1], [-3, -7, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, -2, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, -2, -5, 0, 1], [2, 1], [0, 0, -1, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, -2, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, -2, -5, 0, 1], [0, 1], [1, -2, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, -2, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, -2, -5, 0, 1], [0, 1], [2, -2, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 3, -2, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, -2, -5, 0, 1], [0, 1], [3, -2, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 3, -2, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 3, -2, -5, 0, 1], [1, 1], [1, 2, -4, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [2, 4, -2, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 4, -2, -5, 0, 1], [-1, 1], [-2, -6, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [3, 5, -2, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[3, 5, -2, -5, 0, 1], [1, 1], [3, 2, -4, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [4, 6, -2, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[4, 6, -2, -5, 0, 1], [-2, 1], [-2, -4, -1, 2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, -1, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, -1, -5, 0, 1], [0, 1], [0, -1, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, -1, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, -1, -5, 0, 1], [0, 1], [1, -1, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, -1, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, -1, -5, 0, 1], [0, 1], [2, -1, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 3, -1, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, -1, -5, 0, 1], [0, 1], [3, -1, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow210.row
      (by norm_num [DegreeFiveSafeRow210.row])
      DegreeFiveSafeRow210.properties,
    DegreeFiveCertifiedCase.reducible
      [-1, 4, -1, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 4, -1, -5, 0, 1], [-1, 1, 1], [1, -3, -1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 4, -1, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, -1, -5, 0, 1], [0, 1], [4, -1, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 4, -1, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 4, -1, -5, 0, 1], [-1, 1], [-1, -5, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow211.row
      (by norm_num [DegreeFiveSafeRow211.row])
      DegreeFiveSafeRow211.properties,
    DegreeFiveCertifiedCase.reducible
      [2, 5, -1, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 5, -1, -5, 0, 1], [-2, 1], [-1, -3, -1, 2, 1], 1, 4⟩ (by decide))
  ]

set_option linter.unnecessarySeqFocus false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation identifies the generated Rolle rows with their
-- proof-bearing classification cases.
theorem degreeFiveCertifiedCasesChunk030_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈
          (degreeFiveStageFiveEntriesChunk030.flatMap fun entry =>
            entry.a0Candidates.toList.map fun a0 =>
              [a0, entry.a1, entry.a2, entry.a3, entry.a4, 1]) ↔
        coefficients ∈
          degreeFiveCertifiedCasesChunk030.{u}.map
            DegreeFiveCertifiedCase.coefficients := by
  intro coefficients
  simp only [degreeFiveCertifiedCasesChunk030, List.map_cons, List.map_nil,
    DegreeFiveCertifiedCase.coefficients]
  norm_num [degreeFiveStageFiveEntriesChunk030,
    DegreeFiveSafeRow210.row,
    DegreeFiveSafeRow211.row,
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
