import TraceEuclidean.DegreeFiveCertifiedCase
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk007
import TraceEuclidean.DegreeFiveSafeResultants.Row086
import TraceEuclidean.DegreeFiveSafeResultants.Row087
import TraceEuclidean.DegreeFiveSafeResultants.Row088
import TraceEuclidean.DegreeFiveSafeResultants.Row089
import TraceEuclidean.DegreeFiveSafeResultants.Row090
import TraceEuclidean.DegreeFiveSafeResultants.Row091

/-! Proof-bearing classification of quintic frontier chunk 007. -/

namespace TraceEuclidean

universe u

def degreeFiveCertifiedCasesChunk007 :
    List DegreeFiveCertifiedCase.{u} :=
  [
    DegreeFiveCertifiedCase.reducible
      [0, 3, 2, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 2, -4, -2, 1], [-3, 1], [0, -1, -1, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 4, 2, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 4, 2, -4, -2, 1], [1, 1], [1, 3, -1, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 3, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 3, -4, -2, 1], [-3, 1], [0, 0, -1, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 3, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 3, -4, -2, 1], [0, 1], [1, 3, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow086.row
      (by norm_num [DegreeFiveSafeRow086.row])
      DegreeFiveSafeRow086.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 2, 3, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 3, -4, -2, 1], [-1, 1], [0, -2, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 3, 3, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 3, 3, -4, -2, 1], [-1, 1], [1, -2, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 3, 3, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 3, -4, -2, 1], [0, 1], [3, 3, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 4, 3, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, 3, -4, -2, 1], [0, 1], [4, 3, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 5, 3, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 5, 3, -4, -2, 1], [1, 1], [1, 4, -1, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [2, 6, 3, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 6, 3, -4, -2, 1], [1, 1], [2, 4, -1, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 4, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 4, -4, -2, 1], [0, 1], [0, 4, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 1, 4, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 1, 4, -4, -2, 1], [-1, 1, 1], [1, 0, -3, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 4, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 4, -4, -2, 1], [-1, 1], [0, -1, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 2, 4, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 2, 4, -4, -2, 1], [-1, 1], [1, -1, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, 4, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 4, -4, -2, 1], [0, 1], [2, 4, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 3, 4, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 3, 4, -4, -2, 1], [-1, 1], [2, -1, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow087.row
      (by norm_num [DegreeFiveSafeRow087.row])
      DegreeFiveSafeRow087.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 3, 4, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 4, -4, -2, 1], [0, 1], [3, 4, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 4, 4, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 4, 4, -4, -2, 1], [1, 1], [-1, 5, -1, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 4, 4, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, 4, -4, -2, 1], [0, 1], [4, 4, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 5, 4, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 5, 4, -4, -2, 1], [0, 1], [5, 4, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 5, 4, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 5, 4, -4, -2, 1], [-1, -1, 1], [-1, -4, -1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 6, 4, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 6, 4, -4, -2, 1], [1, 1], [1, 5, -1, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [2, 7, 4, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 7, 4, -4, -2, 1], [-2, 1], [-1, -4, -4, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -1, 5, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -1, 5, -4, -2, 1], [0, 1], [-1, 5, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 5, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 5, -4, -2, 1], [-1, 1], [0, 0, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 1, 5, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 1, 5, -4, -2, 1], [-1, 1], [1, 0, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 5, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 5, -4, -2, 1], [0, 1], [1, 5, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 2, 5, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 2, 5, -4, -2, 1], [-1, 1], [2, 0, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow088.row
      (by norm_num [DegreeFiveSafeRow088.row])
      DegreeFiveSafeRow088.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 2, 5, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 5, -4, -2, 1], [0, 1], [2, 5, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 3, 5, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 3, 5, -4, -2, 1], [-1, 1], [3, 0, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow089.row
      (by norm_num [DegreeFiveSafeRow089.row])
      DegreeFiveSafeRow089.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow090.row
      (by norm_num [DegreeFiveSafeRow090.row])
      DegreeFiveSafeRow090.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 3, 5, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 5, -4, -2, 1], [0, 1], [3, 5, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 4, 5, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 4, 5, -4, -2, 1], [1, 1], [-2, 6, -1, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow091.row
      (by norm_num [DegreeFiveSafeRow091.row])
      DegreeFiveSafeRow091.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 4, 5, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, 5, -4, -2, 1], [0, 1], [4, 5, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 5, 5, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 5, 5, -4, -2, 1], [1, 1], [-1, 6, -1, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 5, 5, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 5, 5, -4, -2, 1], [0, 1], [5, 5, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 5, 5, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 5, 5, -4, -2, 1], [-1, -2, 1], [-1, -3, 0, 1], 2, 3⟩ (by decide))
  ]

set_option linter.unnecessarySeqFocus false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation identifies the generated Rolle rows with their
-- proof-bearing classification cases.
theorem degreeFiveCertifiedCasesChunk007_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈
          (degreeFiveStageFiveEntriesChunk007.flatMap fun entry =>
            entry.a0Candidates.toList.map fun a0 =>
              [a0, entry.a1, entry.a2, entry.a3, entry.a4, 1]) ↔
        coefficients ∈
          degreeFiveCertifiedCasesChunk007.{u}.map
            DegreeFiveCertifiedCase.coefficients := by
  intro coefficients
  simp only [degreeFiveCertifiedCasesChunk007, List.map_cons, List.map_nil,
    DegreeFiveCertifiedCase.coefficients]
  norm_num [degreeFiveStageFiveEntriesChunk007,
    DegreeFiveSafeRow086.row,
    DegreeFiveSafeRow087.row,
    DegreeFiveSafeRow088.row,
    DegreeFiveSafeRow089.row,
    DegreeFiveSafeRow090.row,
    DegreeFiveSafeRow091.row,
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
