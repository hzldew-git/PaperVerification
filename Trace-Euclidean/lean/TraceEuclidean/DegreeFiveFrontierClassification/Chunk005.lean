import TraceEuclidean.DegreeFiveCertifiedCase
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk005
import TraceEuclidean.DegreeFiveSafeResultants.Row074
import TraceEuclidean.DegreeFiveSafeResultants.Row075
import TraceEuclidean.DegreeFiveSafeResultants.Row076
import TraceEuclidean.DegreeFiveSafeResultants.Row077
import TraceEuclidean.DegreeFiveSafeResultants.Row078
import TraceEuclidean.DegreeFiveSafeResultants.Row079
import TraceEuclidean.DegreeFiveSafeResultants.Row080
import TraceEuclidean.DegreeFiveSafeResultants.Row081
import TraceEuclidean.DegreeFiveSafeResultants.Row082
import TraceEuclidean.DegreeFiveSafeResultants.Row083
import TraceEuclidean.DegreeFiveSafeResultants.Row084
import TraceEuclidean.DegreeFiveSafeResultants.Row085

/-! Proof-bearing classification of quintic frontier chunk 005. -/

namespace TraceEuclidean

universe u

def degreeFiveCertifiedCasesChunk005 :
    List DegreeFiveCertifiedCase.{u} :=
  [
    DegreeFiveCertifiedCase.reducible
      [-3, -1, 10, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, -1, 10, -5, -2, 1], [-1, 1], [3, 4, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow074.row
      (by norm_num [DegreeFiveSafeRow074.row])
      DegreeFiveSafeRow074.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow075.row
      (by norm_num [DegreeFiveSafeRow075.row])
      DegreeFiveSafeRow075.properties,
    DegreeFiveCertifiedCase.reducible
      [0, -1, 10, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -1, 10, -5, -2, 1], [0, 1], [-1, 10, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 0, 10, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 0, 10, -5, -2, 1], [-1, 1], [4, 4, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow076.row
      (by norm_num [DegreeFiveSafeRow076.row])
      DegreeFiveSafeRow076.properties,
    DegreeFiveCertifiedCase.reducible
      [-2, 0, 10, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 0, 10, -5, -2, 1], [-1, -2, 1], [2, -4, 0, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow077.row
      (by norm_num [DegreeFiveSafeRow077.row])
      DegreeFiveSafeRow077.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 0, 10, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 10, -5, -2, 1], [-2, 1], [0, 0, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-5, 1, 10, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-5, 1, 10, -5, -2, 1], [-1, 1], [5, 4, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 1, 10, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 1, 10, -5, -2, 1], [-1, -1, 1], [4, -5, -1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow078.row
      (by norm_num [DegreeFiveSafeRow078.row])
      DegreeFiveSafeRow078.properties,
    DegreeFiveCertifiedCase.reducible
      [-2, 1, 10, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 1, 10, -5, -2, 1], [-2, 1], [1, 0, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-6, 2, 10, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-6, 2, 10, -5, -2, 1], [-1, 1], [6, 4, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow079.row
      (by norm_num [DegreeFiveSafeRow079.row])
      DegreeFiveSafeRow079.properties,
    DegreeFiveCertifiedCase.reducible
      [-4, 2, 10, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 2, 10, -5, -2, 1], [-2, 1], [2, 0, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-7, 3, 10, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-7, 3, 10, -5, -2, 1], [-1, 1], [7, 4, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-6, 3, 10, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-6, 3, 10, -5, -2, 1], [-2, 1], [3, 0, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow080.row
      (by norm_num [DegreeFiveSafeRow080.row])
      DegreeFiveSafeRow080.properties,
    DegreeFiveCertifiedCase.reducible
      [-8, 4, 10, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-8, 4, 10, -5, -2, 1], [-1, 1], [8, 4, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-10, 5, 10, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-10, 5, 10, -5, -2, 1], [-2, 1], [5, 0, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-12, 6, 10, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-12, 6, 10, -5, -2, 1], [-2, 1], [6, 0, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, -6, 11, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, -6, 11, -5, -2, 1], [-1, 1], [-1, 5, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -5, 11, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -5, 11, -5, -2, 1], [-1, 1], [0, 5, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, -4, 11, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, -4, 11, -5, -2, 1], [-1, 1], [1, 5, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -4, 11, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -4, 11, -5, -2, 1], [0, 1], [-4, 11, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, -3, 11, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, -3, 11, -5, -2, 1], [-1, 1], [2, 5, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow081.row
      (by norm_num [DegreeFiveSafeRow081.row])
      DegreeFiveSafeRow081.properties,
    DegreeFiveCertifiedCase.reducible
      [0, -3, 11, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -3, 11, -5, -2, 1], [0, 1], [-3, 11, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, -2, 11, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, -2, 11, -5, -2, 1], [-1, 1], [3, 5, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow082.row
      (by norm_num [DegreeFiveSafeRow082.row])
      DegreeFiveSafeRow082.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow083.row
      (by norm_num [DegreeFiveSafeRow083.row])
      DegreeFiveSafeRow083.properties,
    DegreeFiveCertifiedCase.reducible
      [0, -2, 11, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -2, 11, -5, -2, 1], [-2, 1], [0, 1, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, -1, 11, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, -1, 11, -5, -2, 1], [-1, 1], [4, 5, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow084.row
      (by norm_num [DegreeFiveSafeRow084.row])
      DegreeFiveSafeRow084.properties,
    DegreeFiveCertifiedCase.reducible
      [-2, -1, 11, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, -1, 11, -5, -2, 1], [-2, 1], [1, 1, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-5, 0, 11, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-5, 0, 11, -5, -2, 1], [-1, 1], [5, 5, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 0, 11, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 0, 11, -5, -2, 1], [-2, 1], [2, 1, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-6, 1, 11, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-6, 1, 11, -5, -2, 1], [-2, 1], [3, 1, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-8, 2, 11, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-8, 2, 11, -5, -2, 1], [-2, 1], [4, 1, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, -7, 12, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, -7, 12, -5, -2, 1], [-1, 1], [-1, 6, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -6, 12, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -6, 12, -5, -2, 1], [0, 1], [-6, 12, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, -5, 12, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, -5, 12, -5, -2, 1], [-1, 1], [1, 6, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -5, 12, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -5, 12, -5, -2, 1], [0, 1], [-5, 12, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, -4, 12, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, -4, 12, -5, -2, 1], [-1, 1], [2, 6, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow085.row
      (by norm_num [DegreeFiveSafeRow085.row])
      DegreeFiveSafeRow085.properties,
    DegreeFiveCertifiedCase.reducible
      [0, -4, 12, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -4, 12, -5, -2, 1], [0, 1], [-4, 12, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, -3, 12, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, -3, 12, -5, -2, 1], [-1, 1], [3, 6, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, -3, 12, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, -3, 12, -5, -2, 1], [-2, 1], [1, 2, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, -2, 12, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, -2, 12, -5, -2, 1], [-2, 1], [2, 2, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-6, -1, 12, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-6, -1, 12, -5, -2, 1], [-2, 1], [3, 2, -5, 0, 1], 1, 4⟩ (by decide))
  ]

set_option linter.unnecessarySeqFocus false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation identifies the generated Rolle rows with their
-- proof-bearing classification cases.
theorem degreeFiveCertifiedCasesChunk005_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈
          (degreeFiveStageFiveEntriesChunk005.flatMap fun entry =>
            entry.a0Candidates.toList.map fun a0 =>
              [a0, entry.a1, entry.a2, entry.a3, entry.a4, 1]) ↔
        coefficients ∈
          degreeFiveCertifiedCasesChunk005.{u}.map
            DegreeFiveCertifiedCase.coefficients := by
  intro coefficients
  simp only [degreeFiveCertifiedCasesChunk005, List.map_cons, List.map_nil,
    DegreeFiveCertifiedCase.coefficients]
  norm_num [degreeFiveStageFiveEntriesChunk005,
    DegreeFiveSafeRow074.row,
    DegreeFiveSafeRow075.row,
    DegreeFiveSafeRow076.row,
    DegreeFiveSafeRow077.row,
    DegreeFiveSafeRow078.row,
    DegreeFiveSafeRow079.row,
    DegreeFiveSafeRow080.row,
    DegreeFiveSafeRow081.row,
    DegreeFiveSafeRow082.row,
    DegreeFiveSafeRow083.row,
    DegreeFiveSafeRow084.row,
    DegreeFiveSafeRow085.row,
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
