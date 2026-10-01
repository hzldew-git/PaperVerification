import TraceEuclidean.DegreeFiveCertifiedCase
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk001
import TraceEuclidean.DegreeFiveSafeResultants.Row002
import TraceEuclidean.DegreeFiveSafeResultants.Row003
import TraceEuclidean.DegreeFiveSafeResultants.Row004
import TraceEuclidean.DegreeFiveSafeResultants.Row005
import TraceEuclidean.DegreeFiveSafeResultants.Row006
import TraceEuclidean.DegreeFiveSafeResultants.Row007
import TraceEuclidean.DegreeFiveSafeResultants.Row008
import TraceEuclidean.DegreeFiveSafeResultants.Row009
import TraceEuclidean.DegreeFiveSafeResultants.Row010
import TraceEuclidean.DegreeFiveSafeResultants.Row011
import TraceEuclidean.DegreeFiveSafeResultants.Row012
import TraceEuclidean.DegreeFiveCriticalMaximalOrder.Row02

/-! Proof-bearing classification of quintic frontier chunk 001. -/

namespace TraceEuclidean

universe u

def degreeFiveCertifiedCasesChunk001 :
    List DegreeFiveCertifiedCase.{u} :=
  [
    DegreeFiveCertifiedCase.reducible
      [0, 5, 3, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 5, 3, -5, -2, 1], [0, 1], [5, 3, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow002.row
      (by norm_num [DegreeFiveSafeRow002.row])
      DegreeFiveSafeRow002.properties,
    DegreeFiveCertifiedCase.reducible
      [1, 6, 3, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 6, 3, -5, -2, 1], [1, 1], [1, 5, -2, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [2, 7, 3, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 7, 3, -5, -2, 1], [1, 1], [2, 5, -2, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [3, 8, 3, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[3, 8, 3, -5, -2, 1], [-3, 1], [-1, -3, -2, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 4, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 4, -5, -2, 1], [0, 1], [0, 4, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 4, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 4, -5, -2, 1], [0, 1], [1, 4, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow003.row
      (by norm_num [DegreeFiveSafeRow003.row])
      DegreeFiveSafeRow003.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 2, 4, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 4, -5, -2, 1], [-1, 1], [0, -2, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 3, 4, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 3, 4, -5, -2, 1], [-1, 1, 1], [2, -1, -3, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 3, 4, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 3, 4, -5, -2, 1], [-1, 1], [1, -2, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 3, 4, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 4, -5, -2, 1], [0, 1], [3, 4, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 4, 4, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 4, 4, -5, -2, 1], [-1, 1], [2, -2, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow004.row
      (by norm_num [DegreeFiveSafeRow004.row])
      DegreeFiveSafeRow004.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 4, 4, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, 4, -5, -2, 1], [0, 1], [4, 4, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 5, 4, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 5, 4, -5, -2, 1], [1, 1], [-1, 6, -2, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 5, 4, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 5, 4, -5, -2, 1], [0, 1], [5, 4, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow005.row
      (by norm_num [DegreeFiveSafeRow005.row])
      DegreeFiveSafeRow005.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 6, 4, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 6, 4, -5, -2, 1], [-3, 1], [0, -2, -2, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow006.row
      (by norm_num [DegreeFiveSafeRow006.row])
      DegreeFiveSafeRow006.properties,
    DegreeFiveCertifiedCase.reducible
      [1, 7, 4, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 7, 4, -5, -2, 1], [1, 1], [1, 6, -2, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [2, 7, 4, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 7, 4, -5, -2, 1], [-1, -1, 1], [-2, -5, -1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [2, 8, 4, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 8, 4, -5, -2, 1], [1, 1], [2, 6, -2, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [3, 9, 4, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[3, 9, 4, -5, -2, 1], [1, 1], [3, 6, -2, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [4, 10, 4, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[4, 10, 4, -5, -2, 1], [-2, 1], [-2, -6, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -1, 5, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -1, 5, -5, -2, 1], [0, 1], [-1, 5, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 5, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 5, -5, -2, 1], [0, 1], [0, 5, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow007.row
      (by norm_num [DegreeFiveSafeRow007.row])
      DegreeFiveSafeRow007.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 1, 5, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 5, -5, -2, 1], [-1, 1], [0, -1, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 2, 5, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 2, 5, -5, -2, 1], [-1, 1], [1, -1, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, 5, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 5, -5, -2, 1], [0, 1], [2, 5, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 3, 5, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 3, 5, -5, -2, 1], [-1, 1], [2, -1, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow008.row
      (by norm_num [DegreeFiveSafeRow008.row])
      DegreeFiveSafeRow008.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 3, 5, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 5, -5, -2, 1], [-3, 1], [0, -1, -2, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 4, 5, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 4, 5, -5, -2, 1], [-3, 1], [1, -1, -2, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow009.row
      (by norm_num [DegreeFiveSafeRow009.row])
      DegreeFiveSafeRow009.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow010.row
      (by norm_num [DegreeFiveSafeRow010.row])
      DegreeFiveSafeRow010.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 4, 5, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, 5, -5, -2, 1], [0, 1], [4, 5, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow011.row
      (by norm_num [DegreeFiveSafeRow011.row])
      DegreeFiveSafeRow011.properties,
    DegreeFiveCertifiedCase.reducible
      [-2, 5, 5, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 5, 5, -5, -2, 1], [1, 1], [-2, 7, -2, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.critical
      DegreeFiveCritical02.row
      (by norm_num [DegreeFiveCritical02.row])
      (by
        intro K _ _ a hpoly hgen
        exact DegreeFiveCritical02.field_discriminant_eq_recorded_of_minpoly
          a (by simpa [DegreeFiveCritical02.T] using hpoly) hgen),
    DegreeFiveCertifiedCase.reducible
      [0, 5, 5, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 5, 5, -5, -2, 1], [0, 1], [5, 5, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 6, 5, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 6, 5, -5, -2, 1], [-2, 0, 1], [1, -3, -2, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 6, 5, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 6, 5, -5, -2, 1], [1, 1], [-1, 7, -2, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 6, 5, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 6, 5, -5, -2, 1], [0, 1], [6, 5, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 6, 5, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 6, 5, -5, -2, 1], [-1, -1, 1], [-1, -5, -1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 7, 5, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 7, 5, -5, -2, 1], [0, 1], [7, 5, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow012.row
      (by norm_num [DegreeFiveSafeRow012.row])
      DegreeFiveSafeRow012.properties,
    DegreeFiveCertifiedCase.reducible
      [1, 8, 5, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 8, 5, -5, -2, 1], [1, 1], [1, 7, -2, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [2, 8, 5, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 8, 5, -5, -2, 1], [-2, -2, 1], [-1, -3, 0, 1], 2, 3⟩ (by decide))
  ]

set_option linter.unnecessarySeqFocus false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation identifies the generated Rolle rows with their
-- proof-bearing classification cases.
theorem degreeFiveCertifiedCasesChunk001_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈
          (degreeFiveStageFiveEntriesChunk001.flatMap fun entry =>
            entry.a0Candidates.toList.map fun a0 =>
              [a0, entry.a1, entry.a2, entry.a3, entry.a4, 1]) ↔
        coefficients ∈
          degreeFiveCertifiedCasesChunk001.{u}.map
            DegreeFiveCertifiedCase.coefficients := by
  intro coefficients
  simp only [degreeFiveCertifiedCasesChunk001, List.map_cons, List.map_nil,
    DegreeFiveCertifiedCase.coefficients]
  norm_num [degreeFiveStageFiveEntriesChunk001,
    DegreeFiveSafeRow002.row,
    DegreeFiveSafeRow003.row,
    DegreeFiveSafeRow004.row,
    DegreeFiveSafeRow005.row,
    DegreeFiveSafeRow006.row,
    DegreeFiveSafeRow007.row,
    DegreeFiveSafeRow008.row,
    DegreeFiveSafeRow009.row,
    DegreeFiveSafeRow010.row,
    DegreeFiveSafeRow011.row,
    DegreeFiveSafeRow012.row,
    DegreeFiveCritical02.row,
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
