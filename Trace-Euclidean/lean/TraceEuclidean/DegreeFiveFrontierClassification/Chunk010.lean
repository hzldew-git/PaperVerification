import TraceEuclidean.DegreeFiveCertifiedCase
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk010
import TraceEuclidean.DegreeFiveSafeResultants.Row103

/-! Proof-bearing classification of quintic frontier chunk 010. -/

namespace TraceEuclidean

universe u

def degreeFiveCertifiedCasesChunk010 :
    List DegreeFiveCertifiedCase.{u} :=
  [
    DegreeFiveCertifiedCase.reducible
      [-2, -3, 10, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, -3, 10, -4, -2, 1], [-2, 1], [1, 2, -4, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, -7, 11, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, -7, 11, -4, -2, 1], [-1, 1], [-1, 6, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -6, 11, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -6, 11, -4, -2, 1], [-2, 1], [0, 3, -4, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [2, -9, 12, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, -9, 12, -4, -2, 1], [-2, 1], [-1, 4, -4, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, -8, 12, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, -8, 12, -4, -2, 1], [-1, 1], [-1, 7, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [3, -11, 13, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[3, -11, 13, -4, -2, 1], [-1, 1], [-3, 8, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 1, -3, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 1, -3, -2, 1], [0, 1], [0, 1, -3, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 1, -3, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 1, -3, -2, 1], [0, 1], [1, 1, -3, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 2, -3, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 2, -3, -2, 1], [0, 1], [0, 2, -3, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 2, -3, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 2, -3, -2, 1], [0, 1], [1, 2, -3, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, 2, -3, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 2, -3, -2, 1], [-1, 1], [0, -2, -4, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 3, -3, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 3, -3, -2, 1], [0, 1], [0, 3, -3, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 3, -3, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 3, -3, -2, 1], [-1, 1], [0, -1, -4, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 2, 3, -3, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 2, 3, -3, -2, 1], [-1, 1], [1, -1, -4, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, 3, -3, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 3, -3, -2, 1], [0, 1], [2, 3, -3, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 3, 3, -3, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 3, -3, -2, 1], [0, 1], [3, 3, -3, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 4, 3, -3, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 4, 3, -3, -2, 1], [1, 1], [1, 3, 0, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -1, 4, -3, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -1, 4, -3, -2, 1], [0, 1], [-1, 4, -3, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 4, -3, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 4, -3, -2, 1], [-1, 1], [0, 0, -4, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 1, 4, -3, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 1, 4, -3, -2, 1], [-1, 1], [1, 0, -4, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 4, -3, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 4, -3, -2, 1], [0, 1], [1, 4, -3, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 2, 4, -3, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 2, 4, -3, -2, 1], [-1, 1], [2, 0, -4, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow103.row
      (by norm_num [DegreeFiveSafeRow103.row])
      DegreeFiveSafeRow103.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 2, 4, -3, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 4, -3, -2, 1], [0, 1], [2, 4, -3, -2, 1], 1, 4⟩ (by decide))
  ]

set_option linter.unnecessarySeqFocus false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation identifies the generated Rolle rows with their
-- proof-bearing classification cases.
theorem degreeFiveCertifiedCasesChunk010_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈
          (degreeFiveStageFiveEntriesChunk010.flatMap fun entry =>
            entry.a0Candidates.toList.map fun a0 =>
              [a0, entry.a1, entry.a2, entry.a3, entry.a4, 1]) ↔
        coefficients ∈
          degreeFiveCertifiedCasesChunk010.{u}.map
            DegreeFiveCertifiedCase.coefficients := by
  intro coefficients
  simp only [degreeFiveCertifiedCasesChunk010, List.map_cons, List.map_nil,
    DegreeFiveCertifiedCase.coefficients]
  norm_num [degreeFiveStageFiveEntriesChunk010,
    DegreeFiveSafeRow103.row,
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
