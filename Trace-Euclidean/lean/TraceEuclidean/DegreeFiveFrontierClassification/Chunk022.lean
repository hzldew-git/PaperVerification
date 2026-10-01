import TraceEuclidean.DegreeFiveCertifiedCase
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk022
import TraceEuclidean.DegreeFiveSafeResultants.Row177

/-! Proof-bearing classification of quintic frontier chunk 022. -/

namespace TraceEuclidean

universe u

def degreeFiveCertifiedCasesChunk022 :
    List DegreeFiveCertifiedCase.{u} :=
  [
    DegreeFiveCertifiedCase.reducible
      [-5, 5, 5, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-5, 5, 5, -5, -1, 1], [-1, 1], [5, 0, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-6, 6, 5, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-6, 6, 5, -5, -1, 1], [-1, 1], [6, 0, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -1, 6, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -1, 6, -5, -1, 1], [-1, 1], [0, 1, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 0, 6, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 0, 6, -5, -1, 1], [-1, 1], [1, 1, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 6, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 6, -5, -1, 1], [-2, 1], [0, 0, -3, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 1, 6, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 1, 6, -5, -1, 1], [-2, 1], [1, 0, -3, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow177.row
      (by norm_num [DegreeFiveSafeRow177.row])
      DegreeFiveSafeRow177.properties,
    DegreeFiveCertifiedCase.reducible
      [-3, 2, 6, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 2, 6, -5, -1, 1], [-1, 1], [3, 1, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 2, 6, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 2, 6, -5, -1, 1], [-1, -1, 1], [2, -4, 0, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 3, 6, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 3, 6, -5, -1, 1], [-1, 1], [4, 1, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -2, 7, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -2, 7, -5, -1, 1], [-2, 1], [0, 1, -3, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, -1, 7, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, -1, 7, -5, -1, 1], [-1, 1], [1, 2, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -1, 7, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -1, 7, -5, -1, 1], [0, 1], [-1, 7, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 0, 7, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 0, 7, -5, -1, 1], [-1, 1], [2, 2, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 1, 7, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 1, 7, -5, -1, 1], [-1, 1], [3, 2, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -3, 8, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -3, 8, -5, -1, 1], [-1, 1], [0, 3, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, -2, 8, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, -2, 8, -5, -1, 1], [-1, 1], [1, 3, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -4, 9, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -4, 9, -5, -1, 1], [0, 1], [-4, 9, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, -6, 10, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, -6, 10, -5, -1, 1], [-1, 1], [-1, 5, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, -2, -4, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, -2, -4, -1, 1], [1, 1], [0, 0, -2, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, -1, -4, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, -1, -4, -1, 1], [0, 1], [0, -1, -4, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, -1, -4, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, -1, -4, -1, 1], [0, 1], [1, -1, -4, -1, 1], 1, 4⟩ (by decide))
  ]

set_option linter.unnecessarySeqFocus false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation identifies the generated Rolle rows with their
-- proof-bearing classification cases.
theorem degreeFiveCertifiedCasesChunk022_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈
          (degreeFiveStageFiveEntriesChunk022.flatMap fun entry =>
            entry.a0Candidates.toList.map fun a0 =>
              [a0, entry.a1, entry.a2, entry.a3, entry.a4, 1]) ↔
        coefficients ∈
          degreeFiveCertifiedCasesChunk022.{u}.map
            DegreeFiveCertifiedCase.coefficients := by
  intro coefficients
  simp only [degreeFiveCertifiedCasesChunk022, List.map_cons, List.map_nil,
    DegreeFiveCertifiedCase.coefficients]
  norm_num [degreeFiveStageFiveEntriesChunk022,
    DegreeFiveSafeRow177.row,
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
