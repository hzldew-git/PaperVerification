import TraceEuclidean.DegreeFiveCertifiedCase
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk031
import TraceEuclidean.DegreeFiveSafeResultants.Row212
import TraceEuclidean.DegreeFiveSafeResultants.Row213
import TraceEuclidean.DegreeFiveSafeResultants.Row214
import TraceEuclidean.DegreeFiveSafeResultants.Row215

/-! Proof-bearing classification of quintic frontier chunk 031. -/

namespace TraceEuclidean

universe u

def degreeFiveCertifiedCasesChunk031 :
    List DegreeFiveCertifiedCase.{u} :=
  [
    DegreeFiveCertifiedCase.reducible
      [2, 6, -1, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 6, -1, -5, 0, 1], [-2, 0, 1], [-1, -3, 0, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [3, 6, -1, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[3, 6, -1, -5, 0, 1], [1, 1], [3, 3, -4, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 0, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 0, -5, 0, 1], [0, 1], [1, 0, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, 0, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 0, -5, 0, 1], [0, 1], [2, 0, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 3, 0, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 0, -5, 0, 1], [0, 1], [3, 0, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow212.row
      (by norm_num [DegreeFiveSafeRow212.row])
      DegreeFiveSafeRow212.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 4, 0, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, 0, -5, 0, 1], [-2, 1], [0, -2, -1, 2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow213.row
      (by norm_num [DegreeFiveSafeRow213.row])
      DegreeFiveSafeRow213.properties,
    DegreeFiveCertifiedCase.reducible
      [-2, 5, 0, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 5, 0, -5, 0, 1], [-2, 1], [1, -2, -1, 2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 5, 0, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 5, 0, -5, 0, 1], [-1, 1], [1, -4, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 5, 0, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 5, 0, -5, 0, 1], [0, 1], [5, 0, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 5, 0, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 5, 0, -5, 0, 1], [1, 1], [1, 4, -4, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [2, 5, 0, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 5, 0, -5, 0, 1], [2, 1], [1, 2, -1, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 6, 0, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 6, 0, -5, 0, 1], [0, 1], [6, 0, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 1, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 1, -5, 0, 1], [0, 1], [0, 1, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 1, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 1, -5, 0, 1], [0, 1], [1, 1, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, 1, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 1, -5, 0, 1], [-2, 1], [0, -1, -1, 2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow214.row
      (by norm_num [DegreeFiveSafeRow214.row])
      DegreeFiveSafeRow214.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 3, 1, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 1, -5, 0, 1], [-1, 1], [0, -3, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 4, 1, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 4, 1, -5, 0, 1], [-1, 1], [1, -3, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 4, 1, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, 1, -5, 0, 1], [0, 1], [4, 1, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 4, 1, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 4, 1, -5, 0, 1], [-1, -1, 1], [-1, -3, 1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 5, 1, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 5, 1, -5, 0, 1], [-1, 1], [2, -3, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow215.row
      (by norm_num [DegreeFiveSafeRow215.row])
      DegreeFiveSafeRow215.properties,
    DegreeFiveCertifiedCase.reducible
      [-3, 6, 1, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 6, 1, -5, 0, 1], [-1, 1], [3, -3, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 6, 1, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 6, 1, -5, 0, 1], [-2, 0, 1], [1, -3, 0, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 2, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 2, -5, 0, 1], [-2, 1], [0, 0, -1, 2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 2, -5, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 2, -5, 0, 1], [0, 1], [1, 2, -5, 0, 1], 1, 4⟩ (by decide))
  ]

set_option linter.unnecessarySeqFocus false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation identifies the generated Rolle rows with their
-- proof-bearing classification cases.
theorem degreeFiveCertifiedCasesChunk031_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈
          (degreeFiveStageFiveEntriesChunk031.flatMap fun entry =>
            entry.a0Candidates.toList.map fun a0 =>
              [a0, entry.a1, entry.a2, entry.a3, entry.a4, 1]) ↔
        coefficients ∈
          degreeFiveCertifiedCasesChunk031.{u}.map
            DegreeFiveCertifiedCase.coefficients := by
  intro coefficients
  simp only [degreeFiveCertifiedCasesChunk031, List.map_cons, List.map_nil,
    DegreeFiveCertifiedCase.coefficients]
  norm_num [degreeFiveStageFiveEntriesChunk031,
    DegreeFiveSafeRow212.row,
    DegreeFiveSafeRow213.row,
    DegreeFiveSafeRow214.row,
    DegreeFiveSafeRow215.row,
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
