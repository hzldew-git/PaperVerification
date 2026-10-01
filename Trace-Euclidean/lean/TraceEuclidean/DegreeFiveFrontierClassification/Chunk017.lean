import TraceEuclidean.DegreeFiveCertifiedCase
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk017
import TraceEuclidean.DegreeFiveSafeResultants.Row139
import TraceEuclidean.DegreeFiveSafeResultants.Row140
import TraceEuclidean.DegreeFiveSafeResultants.Row141
import TraceEuclidean.DegreeFiveSafeResultants.Row142
import TraceEuclidean.DegreeFiveSafeResultants.Row143
import TraceEuclidean.DegreeFiveSafeResultants.Row144
import TraceEuclidean.DegreeFiveSafeResultants.Row145
import TraceEuclidean.DegreeFiveSafeResultants.Row146
import TraceEuclidean.DegreeFiveSafeResultants.Row147
import TraceEuclidean.DegreeFiveSafeResultants.Row148
import TraceEuclidean.DegreeFiveSafeResultants.Row149
import TraceEuclidean.DegreeFiveSafeResultants.Row150
import TraceEuclidean.DegreeFiveSafeResultants.Row151
import TraceEuclidean.DegreeFiveSafeResultants.Row152
import TraceEuclidean.DegreeFiveSafeResultants.Row153
import TraceEuclidean.DegreeFiveSafeResultants.Row154
import TraceEuclidean.DegreeFiveSafeResultants.Row155
import TraceEuclidean.DegreeFiveSafeResultants.Row156
import TraceEuclidean.DegreeFiveSafeResultants.Row157
import TraceEuclidean.DegreeFiveSafeResultants.Row158
import TraceEuclidean.DegreeFiveCriticalMaximalOrder.Row17

/-! Proof-bearing classification of quintic frontier chunk 017. -/

namespace TraceEuclidean

universe u

def degreeFiveCertifiedCasesChunk017 :
    List DegreeFiveCertifiedCase.{u} :=
  [
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow139.row
      (by norm_num [DegreeFiveSafeRow139.row])
      DegreeFiveSafeRow139.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 1, 5, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 5, -6, -1, 1], [-1, 1], [0, -1, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 2, 5, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 2, 5, -6, -1, 1], [-1, 1], [1, -1, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, 5, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 5, -6, -1, 1], [0, 1], [2, 5, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 3, 5, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 3, 5, -6, -1, 1], [-1, 1], [2, -1, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.critical
      DegreeFiveCritical17.row
      (by norm_num [DegreeFiveCritical17.row])
      (by
        intro K _ _ a hpoly hgen
        exact DegreeFiveCritical17.field_discriminant_eq_recorded_of_minpoly
          a (by simpa [DegreeFiveCritical17.T] using hpoly) hgen),
    DegreeFiveCertifiedCase.reducible
      [0, 3, 5, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 5, -6, -1, 1], [0, 1], [3, 5, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 4, 5, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 4, 5, -6, -1, 1], [-1, 1], [3, -1, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow140.row
      (by norm_num [DegreeFiveSafeRow140.row])
      DegreeFiveSafeRow140.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow141.row
      (by norm_num [DegreeFiveSafeRow141.row])
      DegreeFiveSafeRow141.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 4, 5, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, 5, -6, -1, 1], [0, 1], [4, 5, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 5, 5, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 5, 5, -6, -1, 1], [-1, 1], [4, -1, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow142.row
      (by norm_num [DegreeFiveSafeRow142.row])
      DegreeFiveSafeRow142.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow143.row
      (by norm_num [DegreeFiveSafeRow143.row])
      DegreeFiveSafeRow143.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow144.row
      (by norm_num [DegreeFiveSafeRow144.row])
      DegreeFiveSafeRow144.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 5, 5, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 5, 5, -6, -1, 1], [0, 1], [5, 5, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-5, 6, 5, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-5, 6, 5, -6, -1, 1], [-1, 1], [5, -1, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow145.row
      (by norm_num [DegreeFiveSafeRow145.row])
      DegreeFiveSafeRow145.properties,
    DegreeFiveCertifiedCase.reducible
      [-3, 6, 5, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 6, 5, -6, -1, 1], [1, 1], [-3, 9, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow146.row
      (by norm_num [DegreeFiveSafeRow146.row])
      DegreeFiveSafeRow146.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow147.row
      (by norm_num [DegreeFiveSafeRow147.row])
      DegreeFiveSafeRow147.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 6, 5, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 6, 5, -6, -1, 1], [-2, 1], [0, -3, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-6, 7, 5, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-6, 7, 5, -6, -1, 1], [2, 1], [-3, 5, 0, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow148.row
      (by norm_num [DegreeFiveSafeRow148.row])
      DegreeFiveSafeRow148.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow149.row
      (by norm_num [DegreeFiveSafeRow149.row])
      DegreeFiveSafeRow149.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow150.row
      (by norm_num [DegreeFiveSafeRow150.row])
      DegreeFiveSafeRow150.properties,
    DegreeFiveCertifiedCase.reducible
      [-2, 7, 5, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 7, 5, -6, -1, 1], [-2, 1], [1, -3, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-7, 8, 5, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-7, 8, 5, -6, -1, 1], [-1, 1], [7, -1, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-6, 8, 5, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-6, 8, 5, -6, -1, 1], [-2, 0, 1], [3, -4, -1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow151.row
      (by norm_num [DegreeFiveSafeRow151.row])
      DegreeFiveSafeRow151.properties,
    DegreeFiveCertifiedCase.reducible
      [-4, 8, 5, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 8, 5, -6, -1, 1], [-2, 1], [2, -3, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-6, 9, 5, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-6, 9, 5, -6, -1, 1], [-2, 1], [3, -3, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -1, 6, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -1, 6, -6, -1, 1], [0, 1], [-1, 6, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 6, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 6, -6, -1, 1], [-1, 1], [0, 0, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 1, 6, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 1, 6, -6, -1, 1], [-1, 1], [1, 0, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 1, 6, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 6, -6, -1, 1], [0, 1], [1, 6, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 2, 6, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 2, 6, -6, -1, 1], [-1, 1], [2, 0, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow152.row
      (by norm_num [DegreeFiveSafeRow152.row])
      DegreeFiveSafeRow152.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 2, 6, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 6, -6, -1, 1], [0, 1], [2, 6, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 3, 6, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 3, 6, -6, -1, 1], [-1, 1], [3, 0, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow153.row
      (by norm_num [DegreeFiveSafeRow153.row])
      DegreeFiveSafeRow153.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow154.row
      (by norm_num [DegreeFiveSafeRow154.row])
      DegreeFiveSafeRow154.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 3, 6, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 6, -6, -1, 1], [0, 1], [3, 6, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 4, 6, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 4, 6, -6, -1, 1], [-1, 1], [4, 0, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 4, 6, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 4, 6, -6, -1, 1], [-3, 1, 1], [1, -1, -2, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow155.row
      (by norm_num [DegreeFiveSafeRow155.row])
      DegreeFiveSafeRow155.properties,
    DegreeFiveCertifiedCase.reducible
      [-1, 4, 6, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 4, 6, -6, -1, 1], [-1, -1, 1], [1, -5, 0, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 4, 6, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, 6, -6, -1, 1], [-2, 1], [0, -2, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-5, 5, 6, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-5, 5, 6, -6, -1, 1], [1, 1], [-5, 10, -4, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow156.row
      (by norm_num [DegreeFiveSafeRow156.row])
      DegreeFiveSafeRow156.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow157.row
      (by norm_num [DegreeFiveSafeRow157.row])
      DegreeFiveSafeRow157.properties,
    DegreeFiveCertifiedCase.reducible
      [-2, 5, 6, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 5, 6, -6, -1, 1], [-2, 1], [1, -2, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-6, 6, 6, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-6, 6, 6, -6, -1, 1], [-1, 1], [6, 0, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow158.row
      (by norm_num [DegreeFiveSafeRow158.row])
      DegreeFiveSafeRow158.properties,
    DegreeFiveCertifiedCase.reducible
      [-4, 6, 6, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 6, 6, -6, -1, 1], [-2, 1], [2, -2, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-7, 7, 6, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-7, 7, 6, -6, -1, 1], [-1, 1], [7, 0, -6, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-6, 7, 6, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-6, 7, 6, -6, -1, 1], [-2, 1], [3, -2, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-8, 8, 6, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-8, 8, 6, -6, -1, 1], [-2, 1], [4, -2, -4, 1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-9, 9, 6, -6, -1, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-9, 9, 6, -6, -1, 1], [-1, 1], [9, 0, -6, 0, 1], 1, 4⟩ (by decide))
  ]

set_option linter.unnecessarySeqFocus false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation identifies the generated Rolle rows with their
-- proof-bearing classification cases.
theorem degreeFiveCertifiedCasesChunk017_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈
          (degreeFiveStageFiveEntriesChunk017.flatMap fun entry =>
            entry.a0Candidates.toList.map fun a0 =>
              [a0, entry.a1, entry.a2, entry.a3, entry.a4, 1]) ↔
        coefficients ∈
          degreeFiveCertifiedCasesChunk017.{u}.map
            DegreeFiveCertifiedCase.coefficients := by
  intro coefficients
  simp only [degreeFiveCertifiedCasesChunk017, List.map_cons, List.map_nil,
    DegreeFiveCertifiedCase.coefficients]
  norm_num [degreeFiveStageFiveEntriesChunk017,
    DegreeFiveSafeRow139.row,
    DegreeFiveSafeRow140.row,
    DegreeFiveSafeRow141.row,
    DegreeFiveSafeRow142.row,
    DegreeFiveSafeRow143.row,
    DegreeFiveSafeRow144.row,
    DegreeFiveSafeRow145.row,
    DegreeFiveSafeRow146.row,
    DegreeFiveSafeRow147.row,
    DegreeFiveSafeRow148.row,
    DegreeFiveSafeRow149.row,
    DegreeFiveSafeRow150.row,
    DegreeFiveSafeRow151.row,
    DegreeFiveSafeRow152.row,
    DegreeFiveSafeRow153.row,
    DegreeFiveSafeRow154.row,
    DegreeFiveSafeRow155.row,
    DegreeFiveSafeRow156.row,
    DegreeFiveSafeRow157.row,
    DegreeFiveSafeRow158.row,
    DegreeFiveCritical17.row,
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
