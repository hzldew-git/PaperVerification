import TraceEuclidean.DegreeFiveCertifiedCase
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk026
import TraceEuclidean.DegreeFiveSafeResultants.Row178
import TraceEuclidean.DegreeFiveSafeResultants.Row179
import TraceEuclidean.DegreeFiveSafeResultants.Row180
import TraceEuclidean.DegreeFiveSafeResultants.Row181
import TraceEuclidean.DegreeFiveSafeResultants.Row182
import TraceEuclidean.DegreeFiveSafeResultants.Row183
import TraceEuclidean.DegreeFiveSafeResultants.Row184
import TraceEuclidean.DegreeFiveCriticalMaximalOrder.Row21

/-! Proof-bearing classification of quintic frontier chunk 026. -/

namespace TraceEuclidean

universe u

def degreeFiveCertifiedCasesChunk026 :
    List DegreeFiveCertifiedCase.{u} :=
  [
    DegreeFiveCertifiedCase.reducible
      [0, 0, -3, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, -3, -6, 0, 1], [0, 1], [0, -3, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, -3, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, -3, -6, 0, 1], [0, 1], [1, -3, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, -3, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, -3, -6, 0, 1], [0, 1], [2, -3, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow178.row
      (by norm_num [DegreeFiveSafeRow178.row])
      DegreeFiveSafeRow178.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 3, -3, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, -3, -6, 0, 1], [0, 1], [3, -3, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 3, -3, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 3, -3, -6, 0, 1], [1, 1], [1, 2, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 4, -3, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, -3, -6, 0, 1], [0, 1], [4, -3, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow179.row
      (by norm_num [DegreeFiveSafeRow179.row])
      DegreeFiveSafeRow179.properties,
    DegreeFiveCertifiedCase.reducible
      [2, 4, -3, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 4, -3, -6, 0, 1], [1, 1], [2, 2, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow180.row
      (by norm_num [DegreeFiveSafeRow180.row])
      DegreeFiveSafeRow180.properties,
    DegreeFiveCertifiedCase.reducible
      [3, 5, -3, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[3, 5, -3, -6, 0, 1], [-1, 1], [-3, -8, -5, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [4, 6, -3, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[4, 6, -3, -6, 0, 1], [1, 1], [4, 2, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [5, 7, -3, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[5, 7, -3, -6, 0, 1], [1, 1], [5, 2, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [6, 8, -3, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[6, 8, -3, -6, 0, 1], [1, 1], [6, 2, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, -2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, -2, -6, 0, 1], [0, 1], [0, -2, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, -2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, -2, -6, 0, 1], [0, 1], [1, -2, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, -2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, -2, -6, 0, 1], [0, 1], [2, -2, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 3, -2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, -2, -6, 0, 1], [0, 1], [3, -2, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow181.row
      (by norm_num [DegreeFiveSafeRow181.row])
      DegreeFiveSafeRow181.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 4, -2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, -2, -6, 0, 1], [0, 1], [4, -2, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 4, -2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 4, -2, -6, 0, 1], [1, 1], [1, 3, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 5, -2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 5, -2, -6, 0, 1], [-1, 1, 1], [1, -4, -1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 5, -2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 5, -2, -6, 0, 1], [0, 1], [5, -2, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow182.row
      (by norm_num [DegreeFiveSafeRow182.row])
      DegreeFiveSafeRow182.properties,
    DegreeFiveCertifiedCase.reducible
      [2, 5, -2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 5, -2, -6, 0, 1], [-1, 1], [-2, -7, -5, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 6, -2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 6, -2, -6, 0, 1], [-1, 1], [-1, -7, -5, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.critical
      DegreeFiveCritical21.row
      (by norm_num [DegreeFiveCritical21.row])
      (by
        intro K _ _ a hpoly hgen
        exact DegreeFiveCritical21.field_discriminant_eq_recorded_of_minpoly
          a (by simpa [DegreeFiveCritical21.T] using hpoly) hgen),
    DegreeFiveCertifiedCase.reducible
      [3, 6, -2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[3, 6, -2, -6, 0, 1], [1, 1], [3, 3, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [3, 7, -2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[3, 7, -2, -6, 0, 1], [-3, -1, 1], [-1, -2, 1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [4, 7, -2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[4, 7, -2, -6, 0, 1], [1, 1], [4, 3, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [4, 8, -2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[4, 8, -2, -6, 0, 1], [-2, 0, 1], [-2, -4, 0, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [5, 8, -2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[5, 8, -2, -6, 0, 1], [1, 1], [5, 3, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [6, 9, -2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[6, 9, -2, -6, 0, 1], [-2, 1], [-3, -6, -2, 2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, -1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, -1, -6, 0, 1], [0, 1], [0, -1, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, -1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, -1, -6, 0, 1], [0, 1], [1, -1, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, -1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, -1, -6, 0, 1], [0, 1], [2, -1, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 3, -1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, -1, -6, 0, 1], [0, 1], [3, -1, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 3, -1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 3, -1, -6, 0, 1], [-1, -2, 1], [-1, -1, 2, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow183.row
      (by norm_num [DegreeFiveSafeRow183.row])
      DegreeFiveSafeRow183.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 4, -1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, -1, -6, 0, 1], [0, 1], [4, -1, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow184.row
      (by norm_num [DegreeFiveSafeRow184.row])
      DegreeFiveSafeRow184.properties
  ]

set_option linter.unnecessarySeqFocus false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation identifies the generated Rolle rows with their
-- proof-bearing classification cases.
theorem degreeFiveCertifiedCasesChunk026_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈
          (degreeFiveStageFiveEntriesChunk026.flatMap fun entry =>
            entry.a0Candidates.toList.map fun a0 =>
              [a0, entry.a1, entry.a2, entry.a3, entry.a4, 1]) ↔
        coefficients ∈
          degreeFiveCertifiedCasesChunk026.{u}.map
            DegreeFiveCertifiedCase.coefficients := by
  intro coefficients
  simp only [degreeFiveCertifiedCasesChunk026, List.map_cons, List.map_nil,
    DegreeFiveCertifiedCase.coefficients]
  norm_num [degreeFiveStageFiveEntriesChunk026,
    DegreeFiveSafeRow178.row,
    DegreeFiveSafeRow179.row,
    DegreeFiveSafeRow180.row,
    DegreeFiveSafeRow181.row,
    DegreeFiveSafeRow182.row,
    DegreeFiveSafeRow183.row,
    DegreeFiveSafeRow184.row,
    DegreeFiveCritical21.row,
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
