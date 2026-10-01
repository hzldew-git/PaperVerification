import TraceEuclidean.DegreeFiveCertifiedCase
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk018
import TraceEuclidean.DegreeFiveSafeResultants.Row159
import TraceEuclidean.DegreeFiveSafeResultants.Row160
import TraceEuclidean.DegreeFiveSafeResultants.Row161
import TraceEuclidean.DegreeFiveSafeResultants.Row162
import TraceEuclidean.DegreeFiveSafeResultants.Row163
import TraceEuclidean.DegreeFiveCriticalMaximalOrder.Row18

/-! Proof-bearing classification of quintic frontier chunk 018. -/

namespace TraceEuclidean

universe u

def degreeFiveCertifiedCasesChunk018 :
    List DegreeFiveCertifiedCase.{u} :=
  [
    DegreeFiveCertifiedCase.reducible
      [0, -1, 7, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -1, 7, -6, -1, 1], [-1, 1], [0, 1, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 0, 7, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 0, 7, -6, -1, 1], [-1, 1], [1, 1, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 7, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 7, -6, -1, 1], [0, 1], [0, 7, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 1, 7, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 1, 7, -6, -1, 1], [-1, 1], [2, 1, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.critical
      DegreeFiveCritical18.row
      (by norm_num [DegreeFiveCritical18.row])
      (by
        intro K _ _ a hpoly hgen
        exact DegreeFiveCritical18.field_discriminant_eq_recorded_of_minpoly
          a (by simpa [DegreeFiveCritical18.T] using hpoly) hgen),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 7, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 7, -6, -1, 1], [0, 1], [1, 7, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 2, 7, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 2, 7, -6, -1, 1], [-1, 1], [3, 1, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow159.row
      (by norm_num [DegreeFiveSafeRow159.row])
      DegreeFiveSafeRow159.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow160.row
      (by norm_num [DegreeFiveSafeRow160.row])
      DegreeFiveSafeRow160.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 2, 7, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 7, -6, -1, 1], [-2, 1], [0, -1, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 3, 7, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 3, 7, -6, -1, 1], [-1, 1], [4, 1, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow161.row
      (by norm_num [DegreeFiveSafeRow161.row])
      DegreeFiveSafeRow161.properties,
    DegreeFiveCertifiedCase.reducible
      [-2, 3, 7, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 3, 7, -6, -1, 1], [-2, 1], [1, -1, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-5, 4, 7, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-5, 4, 7, -6, -1, 1], [-1, 1], [5, 1, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 4, 7, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 4, 7, -6, -1, 1], [-2, 1], [2, -1, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-6, 5, 7, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-6, 5, 7, -6, -1, 1], [-2, 1], [3, -1, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-7, 6, 7, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-7, 6, 7, -6, -1, 1], [-1, 1], [7, 1, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -2, 8, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -2, 8, -6, -1, 1], [-1, 1], [0, 2, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, -1, 8, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, -1, 8, -6, -1, 1], [-1, 1], [1, 2, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -1, 8, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -1, 8, -6, -1, 1], [0, 1], [-1, 8, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 0, 8, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 0, 8, -6, -1, 1], [-1, 1], [2, 2, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow162.row
      (by norm_num [DegreeFiveSafeRow162.row])
      DegreeFiveSafeRow162.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 0, 8, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 8, -6, -1, 1], [-2, 1], [0, 0, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 1, 8, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 1, 8, -6, -1, 1], [-1, 1], [3, 2, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 1, 8, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 1, 8, -6, -1, 1], [-2, 1], [1, 0, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 2, 8, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 2, 8, -6, -1, 1], [-2, 1], [2, 0, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 2, 8, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 2, 8, -6, -1, 1], [-1, -1, 1], [3, -5, 0, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-5, 3, 8, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-5, 3, 8, -6, -1, 1], [-1, 1], [5, 2, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -3, 9, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -3, 9, -6, -1, 1], [-1, 1], [0, 3, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, -2, 9, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, -2, 9, -6, -1, 1], [-1, 1], [1, 3, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -2, 9, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -2, 9, -6, -1, 1], [-2, 1], [0, 1, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, -1, 9, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, -1, 9, -6, -1, 1], [-2, 1], [1, 1, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow163.row
      (by norm_num [DegreeFiveSafeRow163.row])
      DegreeFiveSafeRow163.properties,
    DegreeFiveCertifiedCase.reducible
      [-3, 0, 9, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 0, 9, -6, -1, 1], [-1, 1], [3, 3, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 1, 9, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 1, 9, -6, -1, 1], [-1, 1], [4, 3, -6, 0, 1], 1, 4⟩ (by decide))
  ]

set_option linter.unnecessarySeqFocus false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation identifies the generated Rolle rows with their
-- proof-bearing classification cases.
theorem degreeFiveCertifiedCasesChunk018_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈
          (degreeFiveStageFiveEntriesChunk018.flatMap fun entry =>
            entry.a0Candidates.toList.map fun a0 =>
              [a0, entry.a1, entry.a2, entry.a3, entry.a4, 1]) ↔
        coefficients ∈
          degreeFiveCertifiedCasesChunk018.{u}.map
            DegreeFiveCertifiedCase.coefficients := by
  intro coefficients
  simp only [degreeFiveCertifiedCasesChunk018, List.map_cons, List.map_nil,
    DegreeFiveCertifiedCase.coefficients]
  norm_num [degreeFiveStageFiveEntriesChunk018,
    DegreeFiveSafeRow159.row,
    DegreeFiveSafeRow160.row,
    DegreeFiveSafeRow161.row,
    DegreeFiveSafeRow162.row,
    DegreeFiveSafeRow163.row,
    DegreeFiveCritical18.row,
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
