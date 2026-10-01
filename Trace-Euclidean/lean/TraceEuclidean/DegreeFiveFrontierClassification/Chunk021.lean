import TraceEuclidean.DegreeFiveCertifiedCase
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk021
import TraceEuclidean.DegreeFiveSafeResultants.Row171
import TraceEuclidean.DegreeFiveSafeResultants.Row172
import TraceEuclidean.DegreeFiveSafeResultants.Row173
import TraceEuclidean.DegreeFiveSafeResultants.Row174
import TraceEuclidean.DegreeFiveSafeResultants.Row175
import TraceEuclidean.DegreeFiveSafeResultants.Row176
import TraceEuclidean.DegreeFiveCriticalMaximalOrder.Row19

/-! Proof-bearing classification of quintic frontier chunk 021. -/

namespace TraceEuclidean

universe u

def degreeFiveCertifiedCasesChunk021 :
    List DegreeFiveCertifiedCase.{u} :=
  [
    DegreeFiveCertifiedCase.reducible
      [-2, 6, 3, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 6, 3, -5, -1, 1], [-2, 0, 1], [1, -3, -1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow171.row
      (by norm_num [DegreeFiveSafeRow171.row])
      DegreeFiveSafeRow171.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 6, 3, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 6, 3, -5, -1, 1], [-2, 1], [0, -3, -3, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 4, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 4, -5, -1, 1], [0, 1], [0, 4, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 4, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 4, -5, -1, 1], [-1, 1], [0, -1, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 2, 4, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 2, 4, -5, -1, 1], [-1, 1], [1, -1, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, 4, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 4, -5, -1, 1], [0, 1], [2, 4, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 3, 4, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 3, 4, -5, -1, 1], [-1, 1], [2, -1, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.critical
      DegreeFiveCritical19.row
      (by norm_num [DegreeFiveCritical19.row])
      (by
        intro K _ _ a hpoly hgen
        exact DegreeFiveCritical19.field_discriminant_eq_recorded_of_minpoly
          a (by simpa [DegreeFiveCritical19.T] using hpoly) hgen),
    DegreeFiveCertifiedCase.reducible
      [0, 3, 4, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 4, -5, -1, 1], [0, 1], [3, 4, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 4, 4, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 4, 4, -5, -1, 1], [-1, 1], [3, -1, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow172.row
      (by norm_num [DegreeFiveSafeRow172.row])
      DegreeFiveSafeRow172.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow173.row
      (by norm_num [DegreeFiveSafeRow173.row])
      DegreeFiveSafeRow173.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 4, 4, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, 4, -5, -1, 1], [-2, 1], [0, -2, -3, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 5, 4, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 5, 4, -5, -1, 1], [-1, 1], [4, -1, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow174.row
      (by norm_num [DegreeFiveSafeRow174.row])
      DegreeFiveSafeRow174.properties,
    DegreeFiveCertifiedCase.reducible
      [-2, 5, 4, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 5, 4, -5, -1, 1], [-2, 1], [1, -2, -3, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 6, 4, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 6, 4, -5, -1, 1], [-2, 1], [2, -2, -3, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 6, 4, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 6, 4, -5, -1, 1], [-3, 0, 1], [1, -2, -1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -1, 5, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -1, 5, -5, -1, 1], [0, 1], [-1, 5, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 5, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 5, -5, -1, 1], [-1, 1], [0, 0, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 1, 5, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 1, 5, -5, -1, 1], [-1, 1], [1, 0, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 5, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 5, -5, -1, 1], [0, 1], [1, 5, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 2, 5, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 2, 5, -5, -1, 1], [-1, 1], [2, 0, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow175.row
      (by norm_num [DegreeFiveSafeRow175.row])
      DegreeFiveSafeRow175.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 2, 5, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 5, -5, -1, 1], [-2, 1], [0, -1, -3, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 3, 5, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 3, 5, -5, -1, 1], [-1, 1], [3, 0, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 3, 5, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 3, 5, -5, -1, 1], [-2, 1], [1, -1, -3, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 3, 5, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 3, 5, -5, -1, 1], [-1, -1, 1], [1, -4, 0, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 4, 5, -5, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 4, 5, -5, -1, 1], [-2, 1], [2, -1, -3, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow176.row
      (by norm_num [DegreeFiveSafeRow176.row])
      DegreeFiveSafeRow176.properties
  ]

set_option linter.unnecessarySeqFocus false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation identifies the generated Rolle rows with their
-- proof-bearing classification cases.
theorem degreeFiveCertifiedCasesChunk021_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈
          (degreeFiveStageFiveEntriesChunk021.flatMap fun entry =>
            entry.a0Candidates.toList.map fun a0 =>
              [a0, entry.a1, entry.a2, entry.a3, entry.a4, 1]) ↔
        coefficients ∈
          degreeFiveCertifiedCasesChunk021.{u}.map
            DegreeFiveCertifiedCase.coefficients := by
  intro coefficients
  simp only [degreeFiveCertifiedCasesChunk021, List.map_cons, List.map_nil,
    DegreeFiveCertifiedCase.coefficients]
  norm_num [degreeFiveStageFiveEntriesChunk021,
    DegreeFiveSafeRow171.row,
    DegreeFiveSafeRow172.row,
    DegreeFiveSafeRow173.row,
    DegreeFiveSafeRow174.row,
    DegreeFiveSafeRow175.row,
    DegreeFiveSafeRow176.row,
    DegreeFiveCritical19.row,
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
