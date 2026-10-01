import TraceEuclidean.DegreeFiveCertifiedCase
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk028
import TraceEuclidean.DegreeFiveSafeResultants.Row197
import TraceEuclidean.DegreeFiveSafeResultants.Row198
import TraceEuclidean.DegreeFiveSafeResultants.Row199
import TraceEuclidean.DegreeFiveSafeResultants.Row200
import TraceEuclidean.DegreeFiveSafeResultants.Row201
import TraceEuclidean.DegreeFiveSafeResultants.Row202
import TraceEuclidean.DegreeFiveSafeResultants.Row203
import TraceEuclidean.DegreeFiveSafeResultants.Row204
import TraceEuclidean.DegreeFiveSafeResultants.Row205
import TraceEuclidean.DegreeFiveSafeResultants.Row206
import TraceEuclidean.DegreeFiveCriticalMaximalOrder.Row24

/-! Proof-bearing classification of quintic frontier chunk 028. -/

namespace TraceEuclidean

universe u

def degreeFiveCertifiedCasesChunk028 :
    List DegreeFiveCertifiedCase.{u} :=
  [
    DegreeFiveCertifiedCase.reducible
      [0, 0, 1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 1, -6, 0, 1], [0, 1], [0, 1, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 1, -6, 0, 1], [0, 1], [1, 1, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, 1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 1, -6, 0, 1], [0, 1], [2, 1, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 3, 1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 3, 1, -6, 0, 1], [-1, 2, 1], [1, -1, -2, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 3, 1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 1, -6, 0, 1], [0, 1], [3, 1, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow197.row
      (by norm_num [DegreeFiveSafeRow197.row])
      DegreeFiveSafeRow197.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 4, 1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, 1, -6, 0, 1], [-1, 1], [0, -4, -5, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow198.row
      (by norm_num [DegreeFiveSafeRow198.row])
      DegreeFiveSafeRow198.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow199.row
      (by norm_num [DegreeFiveSafeRow199.row])
      DegreeFiveSafeRow199.properties,
    DegreeFiveCertifiedCase.reducible
      [-1, 5, 1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 5, 1, -6, 0, 1], [-1, 1], [1, -4, -5, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 5, 1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 5, 1, -6, 0, 1], [0, 1], [5, 1, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow200.row
      (by norm_num [DegreeFiveSafeRow200.row])
      DegreeFiveSafeRow200.properties,
    DegreeFiveCertifiedCase.reducible
      [-2, 6, 1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 6, 1, -6, 0, 1], [-1, 1], [2, -4, -5, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow201.row
      (by norm_num [DegreeFiveSafeRow201.row])
      DegreeFiveSafeRow201.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 6, 1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 6, 1, -6, 0, 1], [-2, 1], [0, -3, -2, 2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow202.row
      (by norm_num [DegreeFiveSafeRow202.row])
      DegreeFiveSafeRow202.properties,
    DegreeFiveCertifiedCase.reducible
      [2, 6, 1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 6, 1, -6, 0, 1], [-1, -1, 1], [-2, -4, 1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 7, 1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 7, 1, -6, 0, 1], [-1, 1], [3, -4, -5, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 7, 1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 7, 1, -6, 0, 1], [-2, 1], [1, -3, -2, 2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow203.row
      (by norm_num [DegreeFiveSafeRow203.row])
      DegreeFiveSafeRow203.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 7, 1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 7, 1, -6, 0, 1], [0, 1], [7, 1, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 8, 1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 8, 1, -6, 0, 1], [-2, 1], [2, -3, -2, 2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow204.row
      (by norm_num [DegreeFiveSafeRow204.row])
      DegreeFiveSafeRow204.properties,
    DegreeFiveCertifiedCase.reducible
      [-2, 8, 1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 8, 1, -6, 0, 1], [-2, 0, 1], [1, -4, 0, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 9, 1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 9, 1, -6, 0, 1], [-3, 0, 1], [1, -3, 0, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 2, -6, 0, 1], [0, 1], [0, 2, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 2, -6, 0, 1], [0, 1], [1, 2, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, 2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 2, -6, 0, 1], [0, 1], [2, 2, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow205.row
      (by norm_num [DegreeFiveSafeRow205.row])
      DegreeFiveSafeRow205.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 3, 2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 2, -6, 0, 1], [-1, 1], [0, -3, -5, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 4, 2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 4, 2, -6, 0, 1], [-1, 1], [1, -3, -5, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 4, 2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, 2, -6, 0, 1], [-2, 1], [0, -2, -2, 2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 5, 2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 5, 2, -6, 0, 1], [-2, 1], [1, -2, -2, 2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow206.row
      (by norm_num [DegreeFiveSafeRow206.row])
      DegreeFiveSafeRow206.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 5, 2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 5, 2, -6, 0, 1], [0, 1], [5, 2, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 5, 2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 5, 2, -6, 0, 1], [-1, -1, 1], [-1, -4, 1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 6, 2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 6, 2, -6, 0, 1], [-1, 1], [3, -3, -5, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.critical
      DegreeFiveCritical24.row
      (by norm_num [DegreeFiveCritical24.row])
      (by
        intro K _ _ a hpoly hgen
        exact DegreeFiveCritical24.field_discriminant_eq_recorded_of_minpoly
          a (by simpa [DegreeFiveCritical24.T] using hpoly) hgen),
    DegreeFiveCertifiedCase.reducible
      [-1, 6, 2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 6, 2, -6, 0, 1], [1, 1], [-1, 7, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 7, 2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 7, 2, -6, 0, 1], [-1, 1], [4, -3, -5, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 7, 2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 7, 2, -6, 0, 1], [-3, 1, 1], [1, -2, -1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-5, 8, 2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-5, 8, 2, -6, 0, 1], [-1, 1], [5, -3, -5, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 8, 2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 8, 2, -6, 0, 1], [-2, 0, 1], [2, -4, 0, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-6, 9, 2, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-6, 9, 2, -6, 0, 1], [2, 1], [-3, 6, -2, -2, 1], 1, 4⟩ (by decide))
  ]

set_option linter.unnecessarySeqFocus false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation identifies the generated Rolle rows with their
-- proof-bearing classification cases.
theorem degreeFiveCertifiedCasesChunk028_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈
          (degreeFiveStageFiveEntriesChunk028.flatMap fun entry =>
            entry.a0Candidates.toList.map fun a0 =>
              [a0, entry.a1, entry.a2, entry.a3, entry.a4, 1]) ↔
        coefficients ∈
          degreeFiveCertifiedCasesChunk028.{u}.map
            DegreeFiveCertifiedCase.coefficients := by
  intro coefficients
  simp only [degreeFiveCertifiedCasesChunk028, List.map_cons, List.map_nil,
    DegreeFiveCertifiedCase.coefficients]
  norm_num [degreeFiveStageFiveEntriesChunk028,
    DegreeFiveSafeRow197.row,
    DegreeFiveSafeRow198.row,
    DegreeFiveSafeRow199.row,
    DegreeFiveSafeRow200.row,
    DegreeFiveSafeRow201.row,
    DegreeFiveSafeRow202.row,
    DegreeFiveSafeRow203.row,
    DegreeFiveSafeRow204.row,
    DegreeFiveSafeRow205.row,
    DegreeFiveSafeRow206.row,
    DegreeFiveCritical24.row,
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
