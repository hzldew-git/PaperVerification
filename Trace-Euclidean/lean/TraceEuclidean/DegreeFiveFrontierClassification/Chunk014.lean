import TraceEuclidean.DegreeFiveCertifiedCase
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk014
import TraceEuclidean.DegreeFiveSafeResultants.Row106
import TraceEuclidean.DegreeFiveSafeResultants.Row107
import TraceEuclidean.DegreeFiveSafeResultants.Row108
import TraceEuclidean.DegreeFiveSafeResultants.Row109
import TraceEuclidean.DegreeFiveSafeResultants.Row110

/-! Proof-bearing classification of quintic frontier chunk 014. -/

namespace TraceEuclidean

universe u

def degreeFiveCertifiedCasesChunk014 :
    List DegreeFiveCertifiedCase.{u} :=
  [
    DegreeFiveCertifiedCase.reducible
      [0, 3, -1, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, -1, -6, -1, 1], [-3, 1], [0, -1, 0, 2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow106.row
      (by norm_num [DegreeFiveSafeRow106.row])
      DegreeFiveSafeRow106.properties,
    DegreeFiveCertifiedCase.reducible
      [1, 4, -1, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 4, -1, -6, -1, 1], [1, 1], [1, 3, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [2, 5, -1, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 5, -1, -6, -1, 1], [-1, 1], [-2, -7, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [3, 6, -1, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[3, 6, -1, -6, -1, 1], [1, 1], [3, 3, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [4, 7, -1, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[4, 7, -1, -6, -1, 1], [1, 1], [4, 3, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 0, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 0, -6, -1, 1], [0, 1], [1, 0, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, 0, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 0, -6, -1, 1], [0, 1], [2, 0, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 3, 0, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 0, -6, -1, 1], [0, 1], [3, 0, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 4, 0, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 4, 0, -6, -1, 1], [-1, 1, 1], [1, -3, -2, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 4, 0, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, 0, -6, -1, 1], [0, 1], [4, 0, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow107.row
      (by norm_num [DegreeFiveSafeRow107.row])
      DegreeFiveSafeRow107.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 5, 0, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 5, 0, -6, -1, 1], [0, 1], [5, 0, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 5, 0, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 5, 0, -6, -1, 1], [-1, 1], [-1, -6, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [2, 6, 0, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 6, 0, -6, -1, 1], [1, 1], [2, 4, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [3, 7, 0, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[3, 7, 0, -6, -1, 1], [1, 1], [3, 4, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [4, 8, 0, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[4, 8, 0, -6, -1, 1], [1, 1], [4, 4, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [5, 9, 0, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[5, 9, 0, -6, -1, 1], [1, 1], [5, 4, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 1, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 1, -6, -1, 1], [0, 1], [0, 1, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 1, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 1, -6, -1, 1], [0, 1], [1, 1, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, 1, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 1, -6, -1, 1], [0, 1], [2, 1, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 3, 1, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 1, -6, -1, 1], [0, 1], [3, 1, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 4, 1, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 4, 1, -6, -1, 1], [1, 1], [-1, 5, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 4, 1, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, 1, -6, -1, 1], [0, 1], [4, 1, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 4, 1, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 4, 1, -6, -1, 1], [-1, 1], [-1, -5, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 5, 1, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 5, 1, -6, -1, 1], [-1, 1, 1], [2, -3, -2, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow108.row
      (by norm_num [DegreeFiveSafeRow108.row])
      DegreeFiveSafeRow108.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 5, 1, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 5, 1, -6, -1, 1], [-1, 1], [0, -5, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow109.row
      (by norm_num [DegreeFiveSafeRow109.row])
      DegreeFiveSafeRow109.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 6, 1, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 6, 1, -6, -1, 1], [0, 1], [6, 1, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 6, 1, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 6, 1, -6, -1, 1], [1, 1], [1, 5, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [2, 6, 1, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 6, 1, -6, -1, 1], [-2, -2, 1], [-1, -2, 1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow110.row
      (by norm_num [DegreeFiveSafeRow110.row])
      DegreeFiveSafeRow110.properties,
    DegreeFiveCertifiedCase.reducible
      [2, 7, 1, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 7, 1, -6, -1, 1], [1, 1], [2, 5, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [2, 8, 1, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 8, 1, -6, -1, 1], [-2, 0, 1], [-1, -4, -1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [3, 8, 1, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[3, 8, 1, -6, -1, 1], [1, 1], [3, 5, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [4, 9, 1, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[4, 9, 1, -6, -1, 1], [1, 1], [4, 5, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [5, 10, 1, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[5, 10, 1, -6, -1, 1], [1, 1], [5, 5, -4, -2, 1], 1, 4⟩ (by decide))
  ]

set_option linter.unnecessarySeqFocus false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation identifies the generated Rolle rows with their
-- proof-bearing classification cases.
theorem degreeFiveCertifiedCasesChunk014_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈
          (degreeFiveStageFiveEntriesChunk014.flatMap fun entry =>
            entry.a0Candidates.toList.map fun a0 =>
              [a0, entry.a1, entry.a2, entry.a3, entry.a4, 1]) ↔
        coefficients ∈
          degreeFiveCertifiedCasesChunk014.{u}.map
            DegreeFiveCertifiedCase.coefficients := by
  intro coefficients
  simp only [degreeFiveCertifiedCasesChunk014, List.map_cons, List.map_nil,
    DegreeFiveCertifiedCase.coefficients]
  norm_num [degreeFiveStageFiveEntriesChunk014,
    DegreeFiveSafeRow106.row,
    DegreeFiveSafeRow107.row,
    DegreeFiveSafeRow108.row,
    DegreeFiveSafeRow109.row,
    DegreeFiveSafeRow110.row,
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
