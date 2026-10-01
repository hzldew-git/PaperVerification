import TraceEuclidean.DegreeFiveCertifiedCase
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk008
import TraceEuclidean.DegreeFiveSafeResultants.Row092
import TraceEuclidean.DegreeFiveSafeResultants.Row093
import TraceEuclidean.DegreeFiveSafeResultants.Row094
import TraceEuclidean.DegreeFiveSafeResultants.Row095
import TraceEuclidean.DegreeFiveSafeResultants.Row096
import TraceEuclidean.DegreeFiveSafeResultants.Row097
import TraceEuclidean.DegreeFiveSafeResultants.Row098
import TraceEuclidean.DegreeFiveCriticalMaximalOrder.Row08
import TraceEuclidean.DegreeFiveCriticalMaximalOrder.Row09
import TraceEuclidean.DegreeFiveCriticalMaximalOrder.Row10

/-! Proof-bearing classification of quintic frontier chunk 008. -/

namespace TraceEuclidean

universe u

def degreeFiveCertifiedCasesChunk008 :
    List DegreeFiveCertifiedCase.{u} :=
  [
    DegreeFiveCertifiedCase.reducible
      [0, 6, 5, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 6, 5, -4, -2, 1], [-2, 1], [0, -3, -4, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -1, 6, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -1, 6, -4, -2, 1], [-1, 1], [0, 1, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 0, 6, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 0, 6, -4, -2, 1], [-1, 1], [1, 1, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 6, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 6, -4, -2, 1], [0, 1], [0, 6, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 1, 6, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 1, 6, -4, -2, 1], [-1, 1], [2, 1, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 1, 6, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 1, 6, -4, -2, 1], [1, -3, 1], [-1, -2, 1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 6, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 6, -4, -2, 1], [0, 1], [1, 6, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 2, 6, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 2, 6, -4, -2, 1], [-1, 1], [3, 1, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.critical
      DegreeFiveCritical08.row
      (by norm_num [DegreeFiveCritical08.row])
      (by
        intro K _ _ a hpoly hgen
        exact DegreeFiveCritical08.field_discriminant_eq_recorded_of_minpoly
          a (by simpa [DegreeFiveCritical08.T] using hpoly) hgen),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow092.row
      (by norm_num [DegreeFiveSafeRow092.row])
      DegreeFiveSafeRow092.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 2, 6, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 6, -4, -2, 1], [0, 1], [2, 6, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 3, 6, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 3, 6, -4, -2, 1], [1, 1], [-4, 7, -1, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 3, 6, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 3, 6, -4, -2, 1], [-1, 1, 1], [3, 0, -3, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.critical
      DegreeFiveCritical09.row
      (by norm_num [DegreeFiveCritical09.row])
      (by
        intro K _ _ a hpoly hgen
        exact DegreeFiveCritical09.field_discriminant_eq_recorded_of_minpoly
          a (by simpa [DegreeFiveCritical09.T] using hpoly) hgen),
    DegreeFiveCertifiedCase.reducible
      [-1, 3, 6, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 3, 6, -4, -2, 1], [-1, -1, 1], [1, -4, -1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 3, 6, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 6, -4, -2, 1], [0, 1], [3, 6, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 4, 6, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 4, 6, -4, -2, 1], [-2, 0, 1], [2, -2, -2, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 4, 6, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 4, 6, -4, -2, 1], [1, 1], [-3, 7, -1, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.critical
      DegreeFiveCritical10.row
      (by norm_num [DegreeFiveCritical10.row])
      (by
        intro K _ _ a hpoly hgen
        exact DegreeFiveCritical10.field_discriminant_eq_recorded_of_minpoly
          a (by simpa [DegreeFiveCritical10.T] using hpoly) hgen),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow093.row
      (by norm_num [DegreeFiveSafeRow093.row])
      DegreeFiveSafeRow093.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 4, 6, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, 6, -4, -2, 1], [-2, 1], [0, -2, -4, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 5, 6, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 5, 6, -4, -2, 1], [-3, -1, 1], [1, -2, -1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 5, 6, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 5, 6, -4, -2, 1], [-2, 1], [1, -2, -4, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -2, 7, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -2, 7, -4, -2, 1], [-1, 1], [0, 2, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, -1, 7, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, -1, 7, -4, -2, 1], [-1, 1], [1, 2, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -1, 7, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -1, 7, -4, -2, 1], [0, 1], [-1, 7, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 0, 7, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 0, 7, -4, -2, 1], [-1, 1], [2, 2, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow094.row
      (by norm_num [DegreeFiveSafeRow094.row])
      DegreeFiveSafeRow094.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 0, 7, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 7, -4, -2, 1], [0, 1], [0, 7, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 1, 7, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 1, 7, -4, -2, 1], [-1, 1], [3, 2, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow095.row
      (by norm_num [DegreeFiveSafeRow095.row])
      DegreeFiveSafeRow095.properties,
    DegreeFiveCertifiedCase.reducible
      [-1, 1, 7, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 1, 7, -4, -2, 1], [-1, -2, 1], [1, -3, 0, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 7, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 7, -4, -2, 1], [0, 1], [1, 7, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 2, 7, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 2, 7, -4, -2, 1], [-1, 1], [4, 2, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow096.row
      (by norm_num [DegreeFiveSafeRow096.row])
      DegreeFiveSafeRow096.properties,
    DegreeFiveCertifiedCase.reducible
      [-2, 2, 7, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 2, 7, -4, -2, 1], [-1, -1, 1], [2, -4, -1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow097.row
      (by norm_num [DegreeFiveSafeRow097.row])
      DegreeFiveSafeRow097.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 2, 7, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 7, -4, -2, 1], [-2, 1], [0, -1, -4, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-5, 3, 7, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-5, 3, 7, -4, -2, 1], [-1, 1], [5, 2, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow098.row
      (by norm_num [DegreeFiveSafeRow098.row])
      DegreeFiveSafeRow098.properties,
    DegreeFiveCertifiedCase.reducible
      [-3, 3, 7, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 3, 7, -4, -2, 1], [-3, 0, 1], [1, -1, -2, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 3, 7, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 3, 7, -4, -2, 1], [-2, 1], [1, -1, -4, 0, 1], 1, 4⟩ (by decide))
  ]

set_option linter.unnecessarySeqFocus false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation identifies the generated Rolle rows with their
-- proof-bearing classification cases.
theorem degreeFiveCertifiedCasesChunk008_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈
          (degreeFiveStageFiveEntriesChunk008.flatMap fun entry =>
            entry.a0Candidates.toList.map fun a0 =>
              [a0, entry.a1, entry.a2, entry.a3, entry.a4, 1]) ↔
        coefficients ∈
          degreeFiveCertifiedCasesChunk008.{u}.map
            DegreeFiveCertifiedCase.coefficients := by
  intro coefficients
  simp only [degreeFiveCertifiedCasesChunk008, List.map_cons, List.map_nil,
    DegreeFiveCertifiedCase.coefficients]
  norm_num [degreeFiveStageFiveEntriesChunk008,
    DegreeFiveSafeRow092.row,
    DegreeFiveSafeRow093.row,
    DegreeFiveSafeRow094.row,
    DegreeFiveSafeRow095.row,
    DegreeFiveSafeRow096.row,
    DegreeFiveSafeRow097.row,
    DegreeFiveSafeRow098.row,
    DegreeFiveCritical08.row,
    DegreeFiveCritical09.row,
    DegreeFiveCritical10.row,
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
