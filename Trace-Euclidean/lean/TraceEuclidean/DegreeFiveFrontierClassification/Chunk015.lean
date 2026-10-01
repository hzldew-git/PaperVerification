import TraceEuclidean.DegreeFiveCertifiedCase
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk015
import TraceEuclidean.DegreeFiveSafeResultants.Row111
import TraceEuclidean.DegreeFiveSafeResultants.Row112
import TraceEuclidean.DegreeFiveSafeResultants.Row113
import TraceEuclidean.DegreeFiveSafeResultants.Row114
import TraceEuclidean.DegreeFiveSafeResultants.Row115
import TraceEuclidean.DegreeFiveSafeResultants.Row116
import TraceEuclidean.DegreeFiveSafeResultants.Row117
import TraceEuclidean.DegreeFiveSafeResultants.Row118
import TraceEuclidean.DegreeFiveSafeResultants.Row119
import TraceEuclidean.DegreeFiveSafeResultants.Row120
import TraceEuclidean.DegreeFiveSafeResultants.Row121
import TraceEuclidean.DegreeFiveSafeResultants.Row122
import TraceEuclidean.DegreeFiveSafeResultants.Row123
import TraceEuclidean.DegreeFiveSafeResultants.Row124
import TraceEuclidean.DegreeFiveSafeResultants.Row125
import TraceEuclidean.DegreeFiveSafeResultants.Row126
import TraceEuclidean.DegreeFiveSafeResultants.Row127
import TraceEuclidean.DegreeFiveSafeResultants.Row128
import TraceEuclidean.DegreeFiveSafeResultants.Row129
import TraceEuclidean.DegreeFiveCriticalMaximalOrder.Row12
import TraceEuclidean.DegreeFiveCriticalMaximalOrder.Row13
import TraceEuclidean.DegreeFiveCriticalMaximalOrder.Row14
import TraceEuclidean.DegreeFiveCriticalMaximalOrder.Row15

/-! Proof-bearing classification of quintic frontier chunk 015. -/

namespace TraceEuclidean

universe u

def degreeFiveCertifiedCasesChunk015 :
    List DegreeFiveCertifiedCase.{u} :=
  [
    DegreeFiveCertifiedCase.reducible
      [6, 11, 1, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[6, 11, 1, -6, -1, 1], [-2, 1], [-3, -7, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 2, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 2, -6, -1, 1], [0, 1], [0, 2, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 2, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 2, -6, -1, 1], [0, 1], [1, 2, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, 2, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 2, -6, -1, 1], [0, 1], [2, 2, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.critical
      DegreeFiveCritical12.row
      (by norm_num [DegreeFiveCritical12.row])
      (by
        intro K _ _ a hpoly hgen
        exact DegreeFiveCritical12.field_discriminant_eq_recorded_of_minpoly
          a (by simpa [DegreeFiveCritical12.T] using hpoly) hgen),
    DegreeFiveCertifiedCase.reducible
      [0, 3, 2, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 2, -6, -1, 1], [0, 1], [3, 2, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow111.row
      (by norm_num [DegreeFiveSafeRow111.row])
      DegreeFiveSafeRow111.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 4, 2, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, 2, -6, -1, 1], [-1, 1], [0, -4, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow112.row
      (by norm_num [DegreeFiveSafeRow112.row])
      DegreeFiveSafeRow112.properties,
    DegreeFiveCertifiedCase.reducible
      [-1, 5, 2, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 5, 2, -6, -1, 1], [-1, 1], [1, -4, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 5, 2, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 5, 2, -6, -1, 1], [0, 1], [5, 2, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.critical
      DegreeFiveCritical13.row
      (by norm_num [DegreeFiveCritical13.row])
      (by
        intro K _ _ a hpoly hgen
        exact DegreeFiveCritical13.field_discriminant_eq_recorded_of_minpoly
          a (by simpa [DegreeFiveCritical13.T] using hpoly) hgen),
    DegreeFiveCertifiedCase.reducible
      [-3, 6, 2, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 6, 2, -6, -1, 1], [-1, 1, 1], [3, -3, -2, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 6, 2, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 6, 2, -6, -1, 1], [-1, 1], [2, -4, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow113.row
      (by norm_num [DegreeFiveSafeRow113.row])
      DegreeFiveSafeRow113.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 6, 2, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 6, 2, -6, -1, 1], [0, 1], [6, 2, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow114.row
      (by norm_num [DegreeFiveSafeRow114.row])
      DegreeFiveSafeRow114.properties,
    DegreeFiveCertifiedCase.critical
      DegreeFiveCritical14.row
      (by norm_num [DegreeFiveCritical14.row])
      (by
        intro K _ _ a hpoly hgen
        exact DegreeFiveCritical14.field_discriminant_eq_recorded_of_minpoly
          a (by simpa [DegreeFiveCritical14.T] using hpoly) hgen),
    DegreeFiveCertifiedCase.reducible
      [0, 7, 2, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 7, 2, -6, -1, 1], [0, 1], [7, 2, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 7, 2, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 7, 2, -6, -1, 1], [1, 1], [1, 6, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow115.row
      (by norm_num [DegreeFiveSafeRow115.row])
      DegreeFiveSafeRow115.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 8, 2, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 8, 2, -6, -1, 1], [0, 1], [8, 2, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow116.row
      (by norm_num [DegreeFiveSafeRow116.row])
      DegreeFiveSafeRow116.properties,
    DegreeFiveCertifiedCase.reducible
      [2, 8, 2, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 8, 2, -6, -1, 1], [1, 1], [2, 6, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [3, 8, 2, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[3, 8, 2, -6, -1, 1], [-1, -1, 1], [-3, -5, 0, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow117.row
      (by norm_num [DegreeFiveSafeRow117.row])
      DegreeFiveSafeRow117.properties,
    DegreeFiveCertifiedCase.reducible
      [3, 9, 2, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[3, 9, 2, -6, -1, 1], [1, 1], [3, 6, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [3, 10, 2, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[3, 10, 2, -6, -1, 1], [-3, -1, 1], [-1, -3, 0, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [4, 10, 2, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[4, 10, 2, -6, -1, 1], [-2, 1], [-2, -6, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 3, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 3, -6, -1, 1], [0, 1], [0, 3, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 3, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 3, -6, -1, 1], [0, 1], [1, 3, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, 3, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 3, -6, -1, 1], [0, 1], [2, 3, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow118.row
      (by norm_num [DegreeFiveSafeRow118.row])
      DegreeFiveSafeRow118.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 3, 3, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 3, -6, -1, 1], [-1, 1], [0, -3, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow119.row
      (by norm_num [DegreeFiveSafeRow119.row])
      DegreeFiveSafeRow119.properties,
    DegreeFiveCertifiedCase.reducible
      [-1, 4, 3, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 4, 3, -6, -1, 1], [-1, 1], [1, -3, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 4, 3, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, 3, -6, -1, 1], [0, 1], [4, 3, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 5, 3, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 5, 3, -6, -1, 1], [-1, 1], [2, -3, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow120.row
      (by norm_num [DegreeFiveSafeRow120.row])
      DegreeFiveSafeRow120.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 5, 3, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 5, 3, -6, -1, 1], [0, 1], [5, 3, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow121.row
      (by norm_num [DegreeFiveSafeRow121.row])
      DegreeFiveSafeRow121.properties,
    DegreeFiveCertifiedCase.reducible
      [-3, 6, 3, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 6, 3, -6, -1, 1], [-1, 1], [3, -3, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow122.row
      (by norm_num [DegreeFiveSafeRow122.row])
      DegreeFiveSafeRow122.properties,
    DegreeFiveCertifiedCase.reducible
      [-1, 6, 3, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 6, 3, -6, -1, 1], [1, 1], [-1, 7, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 6, 3, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 6, 3, -6, -1, 1], [0, 1], [6, 3, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow123.row
      (by norm_num [DegreeFiveSafeRow123.row])
      DegreeFiveSafeRow123.properties,
    DegreeFiveCertifiedCase.reducible
      [-4, 7, 3, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 7, 3, -6, -1, 1], [-1, 1], [4, -3, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.critical
      DegreeFiveCritical15.row
      (by norm_num [DegreeFiveCritical15.row])
      (by
        intro K _ _ a hpoly hgen
        exact DegreeFiveCritical15.field_discriminant_eq_recorded_of_minpoly
          a (by simpa [DegreeFiveCritical15.T] using hpoly) hgen),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow124.row
      (by norm_num [DegreeFiveSafeRow124.row])
      DegreeFiveSafeRow124.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow125.row
      (by norm_num [DegreeFiveSafeRow125.row])
      DegreeFiveSafeRow125.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 7, 3, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 7, 3, -6, -1, 1], [0, 1], [7, 3, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow126.row
      (by norm_num [DegreeFiveSafeRow126.row])
      DegreeFiveSafeRow126.properties,
    DegreeFiveCertifiedCase.reducible
      [2, 7, 3, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 7, 3, -6, -1, 1], [2, 1], [1, 3, 0, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 8, 3, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 8, 3, -6, -1, 1], [-2, 0, 1], [1, -4, -1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow127.row
      (by norm_num [DegreeFiveSafeRow127.row])
      DegreeFiveSafeRow127.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 8, 3, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 8, 3, -6, -1, 1], [0, 1], [8, 3, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 8, 3, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 8, 3, -6, -1, 1], [1, 1], [1, 7, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow128.row
      (by norm_num [DegreeFiveSafeRow128.row])
      DegreeFiveSafeRow128.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 9, 3, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 9, 3, -6, -1, 1], [0, 1], [9, 3, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow129.row
      (by norm_num [DegreeFiveSafeRow129.row])
      DegreeFiveSafeRow129.properties,
    DegreeFiveCertifiedCase.reducible
      [2, 9, 3, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 9, 3, -6, -1, 1], [-2, 1], [-1, -5, -4, 1, 1], 1, 4⟩ (by decide))
  ]

set_option linter.unnecessarySeqFocus false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation identifies the generated Rolle rows with their
-- proof-bearing classification cases.
theorem degreeFiveCertifiedCasesChunk015_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈
          (degreeFiveStageFiveEntriesChunk015.flatMap fun entry =>
            entry.a0Candidates.toList.map fun a0 =>
              [a0, entry.a1, entry.a2, entry.a3, entry.a4, 1]) ↔
        coefficients ∈
          degreeFiveCertifiedCasesChunk015.{u}.map
            DegreeFiveCertifiedCase.coefficients := by
  intro coefficients
  simp only [degreeFiveCertifiedCasesChunk015, List.map_cons, List.map_nil,
    DegreeFiveCertifiedCase.coefficients]
  norm_num [degreeFiveStageFiveEntriesChunk015,
    DegreeFiveSafeRow111.row,
    DegreeFiveSafeRow112.row,
    DegreeFiveSafeRow113.row,
    DegreeFiveSafeRow114.row,
    DegreeFiveSafeRow115.row,
    DegreeFiveSafeRow116.row,
    DegreeFiveSafeRow117.row,
    DegreeFiveSafeRow118.row,
    DegreeFiveSafeRow119.row,
    DegreeFiveSafeRow120.row,
    DegreeFiveSafeRow121.row,
    DegreeFiveSafeRow122.row,
    DegreeFiveSafeRow123.row,
    DegreeFiveSafeRow124.row,
    DegreeFiveSafeRow125.row,
    DegreeFiveSafeRow126.row,
    DegreeFiveSafeRow127.row,
    DegreeFiveSafeRow128.row,
    DegreeFiveSafeRow129.row,
    DegreeFiveCritical12.row,
    DegreeFiveCritical13.row,
    DegreeFiveCritical14.row,
    DegreeFiveCritical15.row,
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
