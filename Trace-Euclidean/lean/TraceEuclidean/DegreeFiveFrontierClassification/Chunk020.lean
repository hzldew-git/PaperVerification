import TraceEuclidean.DegreeFiveCertifiedCase
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk020
import TraceEuclidean.DegreeFiveSafeResultants.Row164
import TraceEuclidean.DegreeFiveSafeResultants.Row165
import TraceEuclidean.DegreeFiveSafeResultants.Row166
import TraceEuclidean.DegreeFiveSafeResultants.Row167
import TraceEuclidean.DegreeFiveSafeResultants.Row168
import TraceEuclidean.DegreeFiveSafeResultants.Row169
import TraceEuclidean.DegreeFiveSafeResultants.Row170

/-! Proof-bearing classification of quintic frontier chunk 020. -/

namespace TraceEuclidean

universe u

def degreeFiveCertifiedCasesChunk020 :
    List DegreeFiveCertifiedCase.{u} :=
  [
    DegreeFiveCertifiedCase.reducible
      [0, 0, 1, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 1, -5, -1, 1], [0, 1], [0, 1, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 1, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 1, -5, -1, 1], [0, 1], [1, 1, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, 1, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 1, -5, -1, 1], [0, 1], [2, 1, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 3, 1, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 3, 1, -5, -1, 1], [1, 1], [-1, 4, -3, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 3, 1, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 1, -5, -1, 1], [0, 1], [3, 1, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 4, 1, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, 1, -5, -1, 1], [-1, 1], [0, -4, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow164.row
      (by norm_num [DegreeFiveSafeRow164.row])
      DegreeFiveSafeRow164.properties,
    DegreeFiveCertifiedCase.reducible
      [1, 5, 1, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 5, 1, -5, -1, 1], [1, 1], [1, 4, -3, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [2, 6, 1, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 6, 1, -5, -1, 1], [1, 1], [2, 4, -3, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [3, 7, 1, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[3, 7, 1, -5, -1, 1], [1, 1], [3, 4, -3, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 2, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 2, -5, -1, 1], [2, 1], [0, 0, 1, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 2, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 2, -5, -1, 1], [0, 1], [1, 2, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, 2, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 2, -5, -1, 1], [0, 1], [2, 2, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow165.row
      (by norm_num [DegreeFiveSafeRow165.row])
      DegreeFiveSafeRow165.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 3, 2, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 2, -5, -1, 1], [-1, 1], [0, -3, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 4, 2, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 4, 2, -5, -1, 1], [-1, 1, 1], [2, -2, -2, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 4, 2, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 4, 2, -5, -1, 1], [-1, 1], [1, -3, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 4, 2, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, 2, -5, -1, 1], [0, 1], [4, 2, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 4, 2, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 4, 2, -5, -1, 1], [-1, -2, 1], [-1, -2, 1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow166.row
      (by norm_num [DegreeFiveSafeRow166.row])
      DegreeFiveSafeRow166.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 5, 2, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 5, 2, -5, -1, 1], [0, 1], [5, 2, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow167.row
      (by norm_num [DegreeFiveSafeRow167.row])
      DegreeFiveSafeRow167.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 6, 2, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 6, 2, -5, -1, 1], [0, 1], [6, 2, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 6, 2, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 6, 2, -5, -1, 1], [1, 1], [1, 5, -3, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [2, 6, 2, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 6, 2, -5, -1, 1], [-1, -1, 1], [-2, -4, 0, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [2, 7, 2, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 7, 2, -5, -1, 1], [-2, 1], [-1, -4, -3, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 3, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 3, -5, -1, 1], [0, 1], [0, 3, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 3, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 3, -5, -1, 1], [0, 1], [1, 3, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow168.row
      (by norm_num [DegreeFiveSafeRow168.row])
      DegreeFiveSafeRow168.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 2, 3, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 3, -5, -1, 1], [-1, 1], [0, -2, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 3, 3, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 3, 3, -5, -1, 1], [-1, 1], [1, -2, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 3, 3, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 3, -5, -1, 1], [0, 1], [3, 3, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 4, 3, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 4, 3, -5, -1, 1], [-1, 1], [2, -2, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow169.row
      (by norm_num [DegreeFiveSafeRow169.row])
      DegreeFiveSafeRow169.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 4, 3, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, 3, -5, -1, 1], [0, 1], [4, 3, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 5, 3, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 5, 3, -5, -1, 1], [-1, 1], [3, -2, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow170.row
      (by norm_num [DegreeFiveSafeRow170.row])
      DegreeFiveSafeRow170.properties,
    DegreeFiveCertifiedCase.reducible
      [-1, 5, 3, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 5, 3, -5, -1, 1], [1, 1], [-1, 6, -3, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 5, 3, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 5, 3, -5, -1, 1], [0, 1], [5, 3, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 5, 3, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 5, 3, -5, -1, 1], [-1, -1, 1], [-1, -4, 0, 1], 2, 3⟩ (by decide))
  ]

set_option linter.unnecessarySeqFocus false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation identifies the generated Rolle rows with their
-- proof-bearing classification cases.
theorem degreeFiveCertifiedCasesChunk020_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈
          (degreeFiveStageFiveEntriesChunk020.flatMap fun entry =>
            entry.a0Candidates.toList.map fun a0 =>
              [a0, entry.a1, entry.a2, entry.a3, entry.a4, 1]) ↔
        coefficients ∈
          degreeFiveCertifiedCasesChunk020.{u}.map
            DegreeFiveCertifiedCase.coefficients := by
  intro coefficients
  simp only [degreeFiveCertifiedCasesChunk020, List.map_cons, List.map_nil,
    DegreeFiveCertifiedCase.coefficients]
  norm_num [degreeFiveStageFiveEntriesChunk020,
    DegreeFiveSafeRow164.row,
    DegreeFiveSafeRow165.row,
    DegreeFiveSafeRow166.row,
    DegreeFiveSafeRow167.row,
    DegreeFiveSafeRow168.row,
    DegreeFiveSafeRow169.row,
    DegreeFiveSafeRow170.row,
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
