import TraceEuclidean.DegreeFiveCertifiedCase
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk016
import TraceEuclidean.DegreeFiveSafeResultants.Row130
import TraceEuclidean.DegreeFiveSafeResultants.Row131
import TraceEuclidean.DegreeFiveSafeResultants.Row132
import TraceEuclidean.DegreeFiveSafeResultants.Row133
import TraceEuclidean.DegreeFiveSafeResultants.Row134
import TraceEuclidean.DegreeFiveSafeResultants.Row135
import TraceEuclidean.DegreeFiveSafeResultants.Row136
import TraceEuclidean.DegreeFiveSafeResultants.Row137
import TraceEuclidean.DegreeFiveSafeResultants.Row138
import TraceEuclidean.DegreeFiveCriticalMaximalOrder.Row16

/-! Proof-bearing classification of quintic frontier chunk 016. -/

namespace TraceEuclidean

universe u

def degreeFiveCertifiedCasesChunk016 :
    List DegreeFiveCertifiedCase.{u} :=
  [
    DegreeFiveCertifiedCase.reducible
      [0, 0, 4, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 4, -6, -1, 1], [0, 1], [0, 4, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 4, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 4, -6, -1, 1], [0, 1], [1, 4, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 2, 4, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 2, 4, -6, -1, 1], [1, -3, 1], [-1, -1, 2, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, 4, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 4, -6, -1, 1], [-1, 1], [0, -2, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 3, 4, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 3, 4, -6, -1, 1], [-1, 1], [1, -2, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 3, 4, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 4, -6, -1, 1], [0, 1], [3, 4, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 4, 4, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 4, 4, -6, -1, 1], [-1, 1], [2, -2, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow130.row
      (by norm_num [DegreeFiveSafeRow130.row])
      DegreeFiveSafeRow130.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 4, 4, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, 4, -6, -1, 1], [0, 1], [4, 4, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 5, 4, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 5, 4, -6, -1, 1], [-1, 1], [3, -2, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow131.row
      (by norm_num [DegreeFiveSafeRow131.row])
      DegreeFiveSafeRow131.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow132.row
      (by norm_num [DegreeFiveSafeRow132.row])
      DegreeFiveSafeRow132.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 5, 4, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 5, 4, -6, -1, 1], [0, 1], [5, 4, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 5, 4, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 5, 4, -6, -1, 1], [-1, -2, 1], [-1, -3, 1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 6, 4, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 6, 4, -6, -1, 1], [-1, 1], [4, -2, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow133.row
      (by norm_num [DegreeFiveSafeRow133.row])
      DegreeFiveSafeRow133.properties,
    DegreeFiveCertifiedCase.reducible
      [-2, 6, 4, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 6, 4, -6, -1, 1], [1, 1], [-2, 8, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow134.row
      (by norm_num [DegreeFiveSafeRow134.row])
      DegreeFiveSafeRow134.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 6, 4, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 6, 4, -6, -1, 1], [0, 1], [6, 4, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 6, 4, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 6, 4, -6, -1, 1], [-1, -1, 1], [-1, -5, 0, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-5, 7, 4, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-5, 7, 4, -6, -1, 1], [-1, 1], [5, -2, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow135.row
      (by norm_num [DegreeFiveSafeRow135.row])
      DegreeFiveSafeRow135.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow136.row
      (by norm_num [DegreeFiveSafeRow136.row])
      DegreeFiveSafeRow136.properties,
    DegreeFiveCertifiedCase.reducible
      [-2, 7, 4, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 7, 4, -6, -1, 1], [2, 1], [-1, 4, 0, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 7, 4, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 7, 4, -6, -1, 1], [1, 1], [-1, 8, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 7, 4, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 7, 4, -6, -1, 1], [0, 1], [7, 4, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.critical
      DegreeFiveCritical16.row
      (by norm_num [DegreeFiveCritical16.row])
      (by
        intro K _ _ a hpoly hgen
        exact DegreeFiveCritical16.field_discriminant_eq_recorded_of_minpoly
          a (by simpa [DegreeFiveCritical16.T] using hpoly) hgen),
    DegreeFiveCertifiedCase.reducible
      [-5, 8, 4, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-5, 8, 4, -6, -1, 1], [-1, 1, 1], [5, -3, -2, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 8, 4, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 8, 4, -6, -1, 1], [-2, 0, 1], [2, -4, -1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 8, 4, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 8, 4, -6, -1, 1], [-3, -1, 1], [1, -3, 0, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow137.row
      (by norm_num [DegreeFiveSafeRow137.row])
      DegreeFiveSafeRow137.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow138.row
      (by norm_num [DegreeFiveSafeRow138.row])
      DegreeFiveSafeRow138.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 8, 4, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 8, 4, -6, -1, 1], [0, 1], [8, 4, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 9, 4, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 9, 4, -6, -1, 1], [-3, 0, 1], [1, -3, -1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 9, 4, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 9, 4, -6, -1, 1], [-2, 1], [1, -4, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -1, 5, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -1, 5, -6, -1, 1], [0, 1], [-1, 5, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 5, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 5, -6, -1, 1], [0, 1], [0, 5, -6, -1, 1], 1, 4⟩ (by decide))
  ]

set_option linter.unnecessarySeqFocus false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation identifies the generated Rolle rows with their
-- proof-bearing classification cases.
theorem degreeFiveCertifiedCasesChunk016_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈
          (degreeFiveStageFiveEntriesChunk016.flatMap fun entry =>
            entry.a0Candidates.toList.map fun a0 =>
              [a0, entry.a1, entry.a2, entry.a3, entry.a4, 1]) ↔
        coefficients ∈
          degreeFiveCertifiedCasesChunk016.{u}.map
            DegreeFiveCertifiedCase.coefficients := by
  intro coefficients
  simp only [degreeFiveCertifiedCasesChunk016, List.map_cons, List.map_nil,
    DegreeFiveCertifiedCase.coefficients]
  norm_num [degreeFiveStageFiveEntriesChunk016,
    DegreeFiveSafeRow130.row,
    DegreeFiveSafeRow131.row,
    DegreeFiveSafeRow132.row,
    DegreeFiveSafeRow133.row,
    DegreeFiveSafeRow134.row,
    DegreeFiveSafeRow135.row,
    DegreeFiveSafeRow136.row,
    DegreeFiveSafeRow137.row,
    DegreeFiveSafeRow138.row,
    DegreeFiveCritical16.row,
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
