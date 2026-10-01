import TraceEuclidean.DegreeFiveCertifiedCase
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk002
import TraceEuclidean.DegreeFiveSafeResultants.Row013
import TraceEuclidean.DegreeFiveSafeResultants.Row014
import TraceEuclidean.DegreeFiveSafeResultants.Row015
import TraceEuclidean.DegreeFiveSafeResultants.Row016
import TraceEuclidean.DegreeFiveSafeResultants.Row017
import TraceEuclidean.DegreeFiveSafeResultants.Row018
import TraceEuclidean.DegreeFiveSafeResultants.Row019
import TraceEuclidean.DegreeFiveSafeResultants.Row020
import TraceEuclidean.DegreeFiveSafeResultants.Row021
import TraceEuclidean.DegreeFiveSafeResultants.Row022
import TraceEuclidean.DegreeFiveSafeResultants.Row023
import TraceEuclidean.DegreeFiveSafeResultants.Row024
import TraceEuclidean.DegreeFiveSafeResultants.Row025
import TraceEuclidean.DegreeFiveSafeResultants.Row026
import TraceEuclidean.DegreeFiveSafeResultants.Row027
import TraceEuclidean.DegreeFiveCriticalMaximalOrder.Row03

/-! Proof-bearing classification of quintic frontier chunk 002. -/

namespace TraceEuclidean

universe u

def degreeFiveCertifiedCasesChunk002 :
    List DegreeFiveCertifiedCase.{u} :=
  [
    DegreeFiveCertifiedCase.reducible
      [2, 9, 5, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 9, 5, -5, -2, 1], [-2, 1], [-1, -5, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [3, 10, 5, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[3, 10, 5, -5, -2, 1], [1, 1], [3, 7, -2, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -1, 6, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -1, 6, -5, -2, 1], [0, 1], [-1, 6, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 6, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 6, -5, -2, 1], [-3, 1], [0, 0, -2, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 1, 6, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 1, 6, -5, -2, 1], [-1, 1], [1, 0, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 6, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 6, -5, -2, 1], [0, 1], [1, 6, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 2, 6, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 2, 6, -5, -2, 1], [-1, 1], [2, 0, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow013.row
      (by norm_num [DegreeFiveSafeRow013.row])
      DegreeFiveSafeRow013.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 2, 6, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 6, -5, -2, 1], [0, 1], [2, 6, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 3, 6, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 3, 6, -5, -2, 1], [-1, 1], [3, 0, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow014.row
      (by norm_num [DegreeFiveSafeRow014.row])
      DegreeFiveSafeRow014.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow015.row
      (by norm_num [DegreeFiveSafeRow015.row])
      DegreeFiveSafeRow015.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 3, 6, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 6, -5, -2, 1], [0, 1], [3, 6, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 4, 6, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 4, 6, -5, -2, 1], [-1, 1], [4, 0, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow016.row
      (by norm_num [DegreeFiveSafeRow016.row])
      DegreeFiveSafeRow016.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow017.row
      (by norm_num [DegreeFiveSafeRow017.row])
      DegreeFiveSafeRow017.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow018.row
      (by norm_num [DegreeFiveSafeRow018.row])
      DegreeFiveSafeRow018.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 4, 6, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, 6, -5, -2, 1], [0, 1], [4, 6, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-5, 5, 6, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-5, 5, 6, -5, -2, 1], [-1, 1], [5, 0, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 5, 6, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 5, 6, -5, -2, 1], [-1, 1, 1], [4, -1, -3, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 5, 6, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 5, 6, -5, -2, 1], [1, 1], [-3, 8, -2, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow019.row
      (by norm_num [DegreeFiveSafeRow019.row])
      DegreeFiveSafeRow019.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow020.row
      (by norm_num [DegreeFiveSafeRow020.row])
      DegreeFiveSafeRow020.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 5, 6, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 5, 6, -5, -2, 1], [0, 1], [5, 6, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 6, 6, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 6, 6, -5, -2, 1], [-2, 0, 1], [2, -3, -2, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.critical
      DegreeFiveCritical03.row
      (by norm_num [DegreeFiveCritical03.row])
      (by
        intro K _ _ a hpoly hgen
        exact DegreeFiveCritical03.field_discriminant_eq_recorded_of_minpoly
          a (by simpa [DegreeFiveCritical03.T] using hpoly) hgen),
    DegreeFiveCertifiedCase.reducible
      [-2, 6, 6, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 6, 6, -5, -2, 1], [1, 1], [-2, 8, -2, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow021.row
      (by norm_num [DegreeFiveSafeRow021.row])
      DegreeFiveSafeRow021.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 6, 6, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 6, 6, -5, -2, 1], [0, 1], [6, 6, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow022.row
      (by norm_num [DegreeFiveSafeRow022.row])
      DegreeFiveSafeRow022.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow023.row
      (by norm_num [DegreeFiveSafeRow023.row])
      DegreeFiveSafeRow023.properties,
    DegreeFiveCertifiedCase.reducible
      [-1, 7, 6, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 7, 6, -5, -2, 1], [1, 1], [-1, 8, -2, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 7, 6, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 7, 6, -5, -2, 1], [0, 1], [7, 6, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow024.row
      (by norm_num [DegreeFiveSafeRow024.row])
      DegreeFiveSafeRow024.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow025.row
      (by norm_num [DegreeFiveSafeRow025.row])
      DegreeFiveSafeRow025.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 8, 6, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 8, 6, -5, -2, 1], [-2, 1], [0, -4, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow026.row
      (by norm_num [DegreeFiveSafeRow026.row])
      DegreeFiveSafeRow026.properties,
    DegreeFiveCertifiedCase.reducible
      [2, 8, 6, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[2, 8, 6, -5, -2, 1], [-1, -2, 1], [-2, -4, 0, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 9, 6, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 9, 6, -5, -2, 1], [0, 1], [9, 6, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -2, 7, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -2, 7, -5, -2, 1], [0, 1], [-2, 7, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -1, 7, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -1, 7, -5, -2, 1], [-1, 1], [0, 1, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 0, 7, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 0, 7, -5, -2, 1], [-1, 1], [1, 1, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 7, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 7, -5, -2, 1], [0, 1], [0, 7, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 1, 7, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 1, 7, -5, -2, 1], [-1, 1], [2, 1, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow027.row
      (by norm_num [DegreeFiveSafeRow027.row])
      DegreeFiveSafeRow027.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 1, 7, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 7, -5, -2, 1], [0, 1], [1, 7, -5, -2, 1], 1, 4⟩ (by decide))
  ]

set_option linter.unnecessarySeqFocus false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation identifies the generated Rolle rows with their
-- proof-bearing classification cases.
theorem degreeFiveCertifiedCasesChunk002_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈
          (degreeFiveStageFiveEntriesChunk002.flatMap fun entry =>
            entry.a0Candidates.toList.map fun a0 =>
              [a0, entry.a1, entry.a2, entry.a3, entry.a4, 1]) ↔
        coefficients ∈
          degreeFiveCertifiedCasesChunk002.{u}.map
            DegreeFiveCertifiedCase.coefficients := by
  intro coefficients
  simp only [degreeFiveCertifiedCasesChunk002, List.map_cons, List.map_nil,
    DegreeFiveCertifiedCase.coefficients]
  norm_num [degreeFiveStageFiveEntriesChunk002,
    DegreeFiveSafeRow013.row,
    DegreeFiveSafeRow014.row,
    DegreeFiveSafeRow015.row,
    DegreeFiveSafeRow016.row,
    DegreeFiveSafeRow017.row,
    DegreeFiveSafeRow018.row,
    DegreeFiveSafeRow019.row,
    DegreeFiveSafeRow020.row,
    DegreeFiveSafeRow021.row,
    DegreeFiveSafeRow022.row,
    DegreeFiveSafeRow023.row,
    DegreeFiveSafeRow024.row,
    DegreeFiveSafeRow025.row,
    DegreeFiveSafeRow026.row,
    DegreeFiveSafeRow027.row,
    DegreeFiveCritical03.row,
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
