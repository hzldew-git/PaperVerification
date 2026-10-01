import TraceEuclidean.DegreeFiveCertifiedCase
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk004
import TraceEuclidean.DegreeFiveSafeResultants.Row061
import TraceEuclidean.DegreeFiveSafeResultants.Row062
import TraceEuclidean.DegreeFiveSafeResultants.Row063
import TraceEuclidean.DegreeFiveSafeResultants.Row064
import TraceEuclidean.DegreeFiveSafeResultants.Row065
import TraceEuclidean.DegreeFiveSafeResultants.Row066
import TraceEuclidean.DegreeFiveSafeResultants.Row067
import TraceEuclidean.DegreeFiveSafeResultants.Row068
import TraceEuclidean.DegreeFiveSafeResultants.Row069
import TraceEuclidean.DegreeFiveSafeResultants.Row070
import TraceEuclidean.DegreeFiveSafeResultants.Row071
import TraceEuclidean.DegreeFiveSafeResultants.Row072
import TraceEuclidean.DegreeFiveSafeResultants.Row073
import TraceEuclidean.DegreeFiveCriticalMaximalOrder.Row06

/-! Proof-bearing classification of quintic frontier chunk 004. -/

namespace TraceEuclidean

universe u

def degreeFiveCertifiedCasesChunk004 :
    List DegreeFiveCertifiedCase.{u} :=
  [
    DegreeFiveCertifiedCase.reducible
      [0, -3, 9, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -3, 9, -5, -2, 1], [-1, 1], [0, 3, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, -2, 9, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, -2, 9, -5, -2, 1], [-1, 1], [1, 3, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -2, 9, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -2, 9, -5, -2, 1], [0, 1], [-2, 9, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, -1, 9, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, -1, 9, -5, -2, 1], [-1, 1], [2, 3, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow061.row
      (by norm_num [DegreeFiveSafeRow061.row])
      DegreeFiveSafeRow061.properties,
    DegreeFiveCertifiedCase.reducible
      [0, -1, 9, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -1, 9, -5, -2, 1], [0, 1], [-1, 9, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 0, 9, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 0, 9, -5, -2, 1], [-1, 1], [3, 3, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow062.row
      (by norm_num [DegreeFiveSafeRow062.row])
      DegreeFiveSafeRow062.properties,
    DegreeFiveCertifiedCase.reducible
      [-1, 0, 9, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 0, 9, -5, -2, 1], [1, -3, 1], [-1, -3, 1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 0, 9, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 9, -5, -2, 1], [0, 1], [0, 9, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 1, 9, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 1, 9, -5, -2, 1], [-1, 1], [4, 3, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow063.row
      (by norm_num [DegreeFiveSafeRow063.row])
      DegreeFiveSafeRow063.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow064.row
      (by norm_num [DegreeFiveSafeRow064.row])
      DegreeFiveSafeRow064.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow065.row
      (by norm_num [DegreeFiveSafeRow065.row])
      DegreeFiveSafeRow065.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 1, 9, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 9, -5, -2, 1], [0, 1], [1, 9, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-5, 2, 9, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-5, 2, 9, -5, -2, 1], [-1, 1], [5, 3, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow066.row
      (by norm_num [DegreeFiveSafeRow066.row])
      DegreeFiveSafeRow066.properties,
    DegreeFiveCertifiedCase.reducible
      [-3, 2, 9, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 2, 9, -5, -2, 1], [-1, -1, 1], [3, -5, -1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow067.row
      (by norm_num [DegreeFiveSafeRow067.row])
      DegreeFiveSafeRow067.properties,
    DegreeFiveCertifiedCase.reducible
      [-1, 2, 9, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 2, 9, -5, -2, 1], [-1, -2, 1], [1, -4, 0, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 2, 9, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 9, -5, -2, 1], [-2, 1], [0, -1, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-6, 3, 9, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-6, 3, 9, -5, -2, 1], [-1, 1], [6, 3, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow068.row
      (by norm_num [DegreeFiveSafeRow068.row])
      DegreeFiveSafeRow068.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow069.row
      (by norm_num [DegreeFiveSafeRow069.row])
      DegreeFiveSafeRow069.properties,
    DegreeFiveCertifiedCase.critical
      DegreeFiveCritical06.row
      (by norm_num [DegreeFiveCritical06.row])
      (by
        intro K _ _ a hpoly hgen
        exact DegreeFiveCritical06.field_discriminant_eq_recorded_of_minpoly
          a (by simpa [DegreeFiveCritical06.T] using hpoly) hgen),
    DegreeFiveCertifiedCase.reducible
      [-2, 3, 9, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 3, 9, -5, -2, 1], [-2, 1], [1, -1, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-7, 4, 9, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-7, 4, 9, -5, -2, 1], [-1, 1], [7, 3, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow070.row
      (by norm_num [DegreeFiveSafeRow070.row])
      DegreeFiveSafeRow070.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow071.row
      (by norm_num [DegreeFiveSafeRow071.row])
      DegreeFiveSafeRow071.properties,
    DegreeFiveCertifiedCase.reducible
      [-4, 4, 9, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 4, 9, -5, -2, 1], [-2, 1], [2, -1, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-8, 5, 9, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-8, 5, 9, -5, -2, 1], [-1, 1], [8, 3, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow072.row
      (by norm_num [DegreeFiveSafeRow072.row])
      DegreeFiveSafeRow072.properties,
    DegreeFiveCertifiedCase.reducible
      [-6, 5, 9, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-6, 5, 9, -5, -2, 1], [-2, 1], [3, -1, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-10, 6, 9, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-10, 6, 9, -5, -2, 1], [-2, 0, 1], [5, -3, -2, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-9, 6, 9, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-9, 6, 9, -5, -2, 1], [-1, 1], [9, 3, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-8, 6, 9, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-8, 6, 9, -5, -2, 1], [-2, 1], [4, -1, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -4, 10, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -4, 10, -5, -2, 1], [-1, 1], [0, 4, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, -3, 10, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, -3, 10, -5, -2, 1], [-1, 1], [1, 4, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -3, 10, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -3, 10, -5, -2, 1], [0, 1], [-3, 10, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, -2, 10, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, -2, 10, -5, -2, 1], [-1, 1], [2, 4, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow073.row
      (by norm_num [DegreeFiveSafeRow073.row])
      DegreeFiveSafeRow073.properties,
    DegreeFiveCertifiedCase.reducible
      [0, -2, 10, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -2, 10, -5, -2, 1], [0, 1], [-2, 10, -5, -2, 1], 1, 4⟩ (by decide))
  ]

set_option linter.unnecessarySeqFocus false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation identifies the generated Rolle rows with their
-- proof-bearing classification cases.
theorem degreeFiveCertifiedCasesChunk004_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈
          (degreeFiveStageFiveEntriesChunk004.flatMap fun entry =>
            entry.a0Candidates.toList.map fun a0 =>
              [a0, entry.a1, entry.a2, entry.a3, entry.a4, 1]) ↔
        coefficients ∈
          degreeFiveCertifiedCasesChunk004.{u}.map
            DegreeFiveCertifiedCase.coefficients := by
  intro coefficients
  simp only [degreeFiveCertifiedCasesChunk004, List.map_cons, List.map_nil,
    DegreeFiveCertifiedCase.coefficients]
  norm_num [degreeFiveStageFiveEntriesChunk004,
    DegreeFiveSafeRow061.row,
    DegreeFiveSafeRow062.row,
    DegreeFiveSafeRow063.row,
    DegreeFiveSafeRow064.row,
    DegreeFiveSafeRow065.row,
    DegreeFiveSafeRow066.row,
    DegreeFiveSafeRow067.row,
    DegreeFiveSafeRow068.row,
    DegreeFiveSafeRow069.row,
    DegreeFiveSafeRow070.row,
    DegreeFiveSafeRow071.row,
    DegreeFiveSafeRow072.row,
    DegreeFiveSafeRow073.row,
    DegreeFiveCritical06.row,
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
