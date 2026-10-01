import TraceEuclidean.DegreeFiveCertifiedCase
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk027
import TraceEuclidean.DegreeFiveSafeResultants.Row185
import TraceEuclidean.DegreeFiveSafeResultants.Row186
import TraceEuclidean.DegreeFiveSafeResultants.Row187
import TraceEuclidean.DegreeFiveSafeResultants.Row188
import TraceEuclidean.DegreeFiveSafeResultants.Row189
import TraceEuclidean.DegreeFiveSafeResultants.Row190
import TraceEuclidean.DegreeFiveSafeResultants.Row191
import TraceEuclidean.DegreeFiveSafeResultants.Row192
import TraceEuclidean.DegreeFiveSafeResultants.Row193
import TraceEuclidean.DegreeFiveSafeResultants.Row194
import TraceEuclidean.DegreeFiveSafeResultants.Row195
import TraceEuclidean.DegreeFiveSafeResultants.Row196
import TraceEuclidean.DegreeFiveCriticalMaximalOrder.Row22
import TraceEuclidean.DegreeFiveCriticalMaximalOrder.Row23

/-! Proof-bearing classification of quintic frontier chunk 027. -/

namespace TraceEuclidean

universe u

def degreeFiveCertifiedCasesChunk027 :
    List DegreeFiveCertifiedCase.{u} :=
  [
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow185.row
      (by norm_num [DegreeFiveSafeRow185.row])
      DegreeFiveSafeRow185.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 5, -1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 5, -1, -6, 0, 1], [0, 1], [5, -1, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 5, -1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 5, -1, -6, 0, 1], [-1, 1], [-1, -6, -5, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow186.row
      (by norm_num [DegreeFiveSafeRow186.row])
      DegreeFiveSafeRow186.properties,
    DegreeFiveCertifiedCase.reducible
      [-2, 6, -1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 6, -1, -6, 0, 1], [-1, 1, 1], [2, -4, -1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow187.row
      (by norm_num [DegreeFiveSafeRow187.row])
      DegreeFiveSafeRow187.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 6, -1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 6, -1, -6, 0, 1], [-1, 1], [0, -6, -5, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow188.row
      (by norm_num [DegreeFiveSafeRow188.row])
      DegreeFiveSafeRow188.properties,
    DegreeFiveCertifiedCase.reducible
      [2, 6, -1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 6, -1, -6, 0, 1], [1, 1], [2, 4, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 7, -1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 7, -1, -6, 0, 1], [0, 1], [7, -1, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow189.row
      (by norm_num [DegreeFiveSafeRow189.row])
      DegreeFiveSafeRow189.properties,
    DegreeFiveCertifiedCase.reducible
      [2, 7, -1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 7, -1, -6, 0, 1], [2, 1], [1, 3, -2, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [3, 7, -1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[3, 7, -1, -6, 0, 1], [1, 1], [3, 4, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [2, 8, -1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 8, -1, -6, 0, 1], [-2, 0, 1], [-1, -4, 0, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow190.row
      (by norm_num [DegreeFiveSafeRow190.row])
      DegreeFiveSafeRow190.properties,
    DegreeFiveCertifiedCase.reducible
      [4, 8, -1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[4, 8, -1, -6, 0, 1], [-2, 1], [-2, -5, -2, 2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [3, 9, -1, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[3, 9, -1, -6, 0, 1], [-3, 0, 1], [-1, -3, 0, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 0, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 0, -6, 0, 1], [0, 1], [1, 0, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, 0, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 0, -6, 0, 1], [0, 1], [2, 0, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 3, 0, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 0, -6, 0, 1], [0, 1], [3, 0, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 4, 0, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 4, 0, -6, 0, 1], [1, 1], [-1, 5, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 4, 0, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, 0, -6, 0, 1], [0, 1], [4, 0, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 4, 0, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 4, 0, -6, 0, 1], [-1, 1], [-1, -5, -5, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow191.row
      (by norm_num [DegreeFiveSafeRow191.row])
      DegreeFiveSafeRow191.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 5, 0, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 5, 0, -6, 0, 1], [-1, 1], [0, -5, -5, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow192.row
      (by norm_num [DegreeFiveSafeRow192.row])
      DegreeFiveSafeRow192.properties,
    DegreeFiveCertifiedCase.critical
      DegreeFiveCritical22.row
      (by norm_num [DegreeFiveCritical22.row])
      (by
        intro K _ _ a hpoly hgen
        exact DegreeFiveCritical22.field_discriminant_eq_recorded_of_minpoly
          a (by simpa [DegreeFiveCritical22.T] using hpoly) hgen),
    DegreeFiveCertifiedCase.reducible
      [-1, 6, 0, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 6, 0, -6, 0, 1], [-1, 1], [1, -5, -5, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 6, 0, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 6, 0, -6, 0, 1], [0, 1], [6, 0, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 6, 0, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 6, 0, -6, 0, 1], [1, 1], [1, 5, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.critical
      DegreeFiveCritical23.row
      (by norm_num [DegreeFiveCritical23.row])
      (by
        intro K _ _ a hpoly hgen
        exact DegreeFiveCritical23.field_discriminant_eq_recorded_of_minpoly
          a (by simpa [DegreeFiveCritical23.T] using hpoly) hgen),
    DegreeFiveCertifiedCase.reducible
      [-3, 7, 0, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 7, 0, -6, 0, 1], [-1, 1, 1], [3, -4, -1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 7, 0, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 7, 0, -6, 0, 1], [-1, 1], [2, -5, -5, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow193.row
      (by norm_num [DegreeFiveSafeRow193.row])
      DegreeFiveSafeRow193.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 7, 0, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 7, 0, -6, 0, 1], [0, 1], [7, 0, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow194.row
      (by norm_num [DegreeFiveSafeRow194.row])
      DegreeFiveSafeRow194.properties,
    DegreeFiveCertifiedCase.reducible
      [2, 7, 0, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 7, 0, -6, 0, 1], [-2, 1], [-1, -4, -2, 2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [3, 7, 0, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[3, 7, 0, -6, 0, 1], [-1, -1, 1], [-3, -4, 1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow195.row
      (by norm_num [DegreeFiveSafeRow195.row])
      DegreeFiveSafeRow195.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 8, 0, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 8, 0, -6, 0, 1], [-2, 1], [0, -4, -2, 2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow196.row
      (by norm_num [DegreeFiveSafeRow196.row])
      DegreeFiveSafeRow196.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 9, 0, -6, 0, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 9, 0, -6, 0, 1], [0, 1], [9, 0, -6, 0, 1], 1, 4⟩ (by decide))
  ]

set_option linter.unnecessarySeqFocus false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation identifies the generated Rolle rows with their
-- proof-bearing classification cases.
theorem degreeFiveCertifiedCasesChunk027_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈
          (degreeFiveStageFiveEntriesChunk027.flatMap fun entry =>
            entry.a0Candidates.toList.map fun a0 =>
              [a0, entry.a1, entry.a2, entry.a3, entry.a4, 1]) ↔
        coefficients ∈
          degreeFiveCertifiedCasesChunk027.{u}.map
            DegreeFiveCertifiedCase.coefficients := by
  intro coefficients
  simp only [degreeFiveCertifiedCasesChunk027, List.map_cons, List.map_nil,
    DegreeFiveCertifiedCase.coefficients]
  norm_num [degreeFiveStageFiveEntriesChunk027,
    DegreeFiveSafeRow185.row,
    DegreeFiveSafeRow186.row,
    DegreeFiveSafeRow187.row,
    DegreeFiveSafeRow188.row,
    DegreeFiveSafeRow189.row,
    DegreeFiveSafeRow190.row,
    DegreeFiveSafeRow191.row,
    DegreeFiveSafeRow192.row,
    DegreeFiveSafeRow193.row,
    DegreeFiveSafeRow194.row,
    DegreeFiveSafeRow195.row,
    DegreeFiveSafeRow196.row,
    DegreeFiveCritical22.row,
    DegreeFiveCritical23.row,
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
