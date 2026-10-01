import TraceEuclidean.DegreeFiveCertifiedCase
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk009
import TraceEuclidean.DegreeFiveSafeResultants.Row099
import TraceEuclidean.DegreeFiveSafeResultants.Row100
import TraceEuclidean.DegreeFiveSafeResultants.Row101
import TraceEuclidean.DegreeFiveSafeResultants.Row102
import TraceEuclidean.DegreeFiveCriticalMaximalOrder.Row11

/-! Proof-bearing classification of quintic frontier chunk 009. -/

namespace TraceEuclidean

universe u

def degreeFiveCertifiedCasesChunk009 :
    List DegreeFiveCertifiedCase.{u} :=
  [
    DegreeFiveCertifiedCase.reducible
      [-6, 4, 7, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-6, 4, 7, -4, -2, 1], [-1, 1], [6, 2, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow099.row
      (by norm_num [DegreeFiveSafeRow099.row])
      DegreeFiveSafeRow099.properties,
    DegreeFiveCertifiedCase.reducible
      [-4, 4, 7, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 4, 7, -4, -2, 1], [1, 1], [-4, 8, -1, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -3, 8, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -3, 8, -4, -2, 1], [-1, 1], [0, 3, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, -2, 8, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, -2, 8, -4, -2, 1], [-1, 1], [1, 3, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -2, 8, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -2, 8, -4, -2, 1], [0, 1], [-2, 8, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, -1, 8, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, -1, 8, -4, -2, 1], [2, 1], [-1, 0, 4, -4, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow100.row
      (by norm_num [DegreeFiveSafeRow100.row])
      DegreeFiveSafeRow100.properties,
    DegreeFiveCertifiedCase.reducible
      [0, -1, 8, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -1, 8, -4, -2, 1], [0, 1], [-1, 8, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 0, 8, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 0, 8, -4, -2, 1], [-1, 1], [3, 3, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.critical
      DegreeFiveCritical11.row
      (by norm_num [DegreeFiveCritical11.row])
      (by
        intro K _ _ a hpoly hgen
        exact DegreeFiveCritical11.field_discriminant_eq_recorded_of_minpoly
          a (by simpa [DegreeFiveCritical11.T] using hpoly) hgen),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow101.row
      (by norm_num [DegreeFiveSafeRow101.row])
      DegreeFiveSafeRow101.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 0, 8, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 8, -4, -2, 1], [2, 1], [0, 0, 4, -4, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 1, 8, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 1, 8, -4, -2, 1], [-1, 1], [4, 3, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 1, 8, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 1, 8, -4, -2, 1], [-1, -1, 1], [3, -4, -1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 1, 8, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 1, 8, -4, -2, 1], [-2, 1], [1, 0, -4, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-5, 2, 8, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-5, 2, 8, -4, -2, 1], [-1, 1], [5, 3, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 2, 8, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 2, 8, -4, -2, 1], [-2, 1], [2, 0, -4, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-6, 3, 8, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-6, 3, 8, -4, -2, 1], [-2, 1], [3, 0, -4, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-8, 4, 8, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-8, 4, 8, -4, -2, 1], [-2, 1], [4, 0, -4, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -4, 9, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -4, 9, -4, -2, 1], [-1, 1], [0, 4, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, -3, 9, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, -3, 9, -4, -2, 1], [-1, 1], [1, 4, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -3, 9, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -3, 9, -4, -2, 1], [0, 1], [-3, 9, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, -2, 9, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, -2, 9, -4, -2, 1], [-1, 1], [2, 4, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow102.row
      (by norm_num [DegreeFiveSafeRow102.row])
      DegreeFiveSafeRow102.properties,
    DegreeFiveCertifiedCase.reducible
      [0, -2, 9, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -2, 9, -4, -2, 1], [-2, 1], [0, 1, -4, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, -1, 9, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, -1, 9, -4, -2, 1], [-1, 1], [3, 4, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, -1, 9, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, -1, 9, -4, -2, 1], [-2, 1], [1, 1, -4, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 0, 9, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 0, 9, -4, -2, 1], [-2, 1], [2, 1, -4, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, -6, 10, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, -6, 10, -4, -2, 1], [-1, 1], [-1, 5, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -5, 10, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -5, 10, -4, -2, 1], [0, 1], [-5, 10, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, -4, 10, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, -4, 10, -4, -2, 1], [-1, 1], [1, 5, -5, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -4, 10, -4, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -4, 10, -4, -2, 1], [-2, 1], [0, 2, -4, 0, 1], 1, 4⟩ (by decide))
  ]

set_option linter.unnecessarySeqFocus false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation identifies the generated Rolle rows with their
-- proof-bearing classification cases.
theorem degreeFiveCertifiedCasesChunk009_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈
          (degreeFiveStageFiveEntriesChunk009.flatMap fun entry =>
            entry.a0Candidates.toList.map fun a0 =>
              [a0, entry.a1, entry.a2, entry.a3, entry.a4, 1]) ↔
        coefficients ∈
          degreeFiveCertifiedCasesChunk009.{u}.map
            DegreeFiveCertifiedCase.coefficients := by
  intro coefficients
  simp only [degreeFiveCertifiedCasesChunk009, List.map_cons, List.map_nil,
    DegreeFiveCertifiedCase.coefficients]
  norm_num [degreeFiveStageFiveEntriesChunk009,
    DegreeFiveSafeRow099.row,
    DegreeFiveSafeRow100.row,
    DegreeFiveSafeRow101.row,
    DegreeFiveSafeRow102.row,
    DegreeFiveCritical11.row,
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
