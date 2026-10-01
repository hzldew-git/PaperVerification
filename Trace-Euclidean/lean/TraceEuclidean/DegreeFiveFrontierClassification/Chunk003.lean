import TraceEuclidean.DegreeFiveCertifiedCase
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk003
import TraceEuclidean.DegreeFiveSafeResultants.Row028
import TraceEuclidean.DegreeFiveSafeResultants.Row029
import TraceEuclidean.DegreeFiveSafeResultants.Row030
import TraceEuclidean.DegreeFiveSafeResultants.Row031
import TraceEuclidean.DegreeFiveSafeResultants.Row032
import TraceEuclidean.DegreeFiveSafeResultants.Row033
import TraceEuclidean.DegreeFiveSafeResultants.Row034
import TraceEuclidean.DegreeFiveSafeResultants.Row035
import TraceEuclidean.DegreeFiveSafeResultants.Row036
import TraceEuclidean.DegreeFiveSafeResultants.Row037
import TraceEuclidean.DegreeFiveSafeResultants.Row038
import TraceEuclidean.DegreeFiveSafeResultants.Row039
import TraceEuclidean.DegreeFiveSafeResultants.Row040
import TraceEuclidean.DegreeFiveSafeResultants.Row041
import TraceEuclidean.DegreeFiveSafeResultants.Row042
import TraceEuclidean.DegreeFiveSafeResultants.Row043
import TraceEuclidean.DegreeFiveSafeResultants.Row044
import TraceEuclidean.DegreeFiveSafeResultants.Row045
import TraceEuclidean.DegreeFiveSafeResultants.Row046
import TraceEuclidean.DegreeFiveSafeResultants.Row047
import TraceEuclidean.DegreeFiveSafeResultants.Row048
import TraceEuclidean.DegreeFiveSafeResultants.Row049
import TraceEuclidean.DegreeFiveSafeResultants.Row050
import TraceEuclidean.DegreeFiveSafeResultants.Row051
import TraceEuclidean.DegreeFiveSafeResultants.Row052
import TraceEuclidean.DegreeFiveSafeResultants.Row053
import TraceEuclidean.DegreeFiveSafeResultants.Row054
import TraceEuclidean.DegreeFiveSafeResultants.Row055
import TraceEuclidean.DegreeFiveSafeResultants.Row056
import TraceEuclidean.DegreeFiveSafeResultants.Row057
import TraceEuclidean.DegreeFiveSafeResultants.Row058
import TraceEuclidean.DegreeFiveSafeResultants.Row059
import TraceEuclidean.DegreeFiveSafeResultants.Row060
import TraceEuclidean.DegreeFiveCriticalMaximalOrder.Row04
import TraceEuclidean.DegreeFiveCriticalMaximalOrder.Row05

/-! Proof-bearing classification of quintic frontier chunk 003. -/

namespace TraceEuclidean

universe u

def degreeFiveCertifiedCasesChunk003 :
    List DegreeFiveCertifiedCase.{u} :=
  [
    DegreeFiveCertifiedCase.reducible
      [-3, 2, 7, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 2, 7, -5, -2, 1], [-1, 1], [3, 1, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow028.row
      (by norm_num [DegreeFiveSafeRow028.row])
      DegreeFiveSafeRow028.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow029.row
      (by norm_num [DegreeFiveSafeRow029.row])
      DegreeFiveSafeRow029.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 2, 7, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 7, -5, -2, 1], [0, 1], [2, 7, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 3, 7, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 3, 7, -5, -2, 1], [-1, 1], [4, 1, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow030.row
      (by norm_num [DegreeFiveSafeRow030.row])
      DegreeFiveSafeRow030.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow031.row
      (by norm_num [DegreeFiveSafeRow031.row])
      DegreeFiveSafeRow031.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow032.row
      (by norm_num [DegreeFiveSafeRow032.row])
      DegreeFiveSafeRow032.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 3, 7, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 7, -5, -2, 1], [0, 1], [3, 7, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-5, 4, 7, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-5, 4, 7, -5, -2, 1], [1, 1], [-5, 9, -2, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow033.row
      (by norm_num [DegreeFiveSafeRow033.row])
      DegreeFiveSafeRow033.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow034.row
      (by norm_num [DegreeFiveSafeRow034.row])
      DegreeFiveSafeRow034.properties,
    DegreeFiveCertifiedCase.reducible
      [-2, 4, 7, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 4, 7, -5, -2, 1], [-2, -2, 1], [1, -3, 0, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, 4, 7, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, 4, 7, -5, -2, 1], [-1, -1, 1], [1, -5, -1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, 4, 7, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, 7, -5, -2, 1], [0, 1], [4, 7, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-6, 5, 7, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-6, 5, 7, -5, -2, 1], [-1, 1], [6, 1, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow035.row
      (by norm_num [DegreeFiveSafeRow035.row])
      DegreeFiveSafeRow035.properties,
    DegreeFiveCertifiedCase.reducible
      [-4, 5, 7, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 5, 7, -5, -2, 1], [1, 1], [-4, 9, -2, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow036.row
      (by norm_num [DegreeFiveSafeRow036.row])
      DegreeFiveSafeRow036.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow037.row
      (by norm_num [DegreeFiveSafeRow037.row])
      DegreeFiveSafeRow037.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow038.row
      (by norm_num [DegreeFiveSafeRow038.row])
      DegreeFiveSafeRow038.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 5, 7, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 5, 7, -5, -2, 1], [0, 1], [5, 7, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-6, 6, 7, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-6, 6, 7, -5, -2, 1], [-2, 0, 1], [3, -3, -2, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-5, 6, 7, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-5, 6, 7, -5, -2, 1], [-1, 1, 1], [5, -1, -3, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow039.row
      (by norm_num [DegreeFiveSafeRow039.row])
      DegreeFiveSafeRow039.properties,
    DegreeFiveCertifiedCase.reducible
      [-3, 6, 7, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 6, 7, -5, -2, 1], [1, 1], [-3, 9, -2, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow040.row
      (by norm_num [DegreeFiveSafeRow040.row])
      DegreeFiveSafeRow040.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow041.row
      (by norm_num [DegreeFiveSafeRow041.row])
      DegreeFiveSafeRow041.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 6, 7, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 6, 7, -5, -2, 1], [-2, 1], [0, -3, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [1, 6, 7, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[1, 6, 7, -5, -2, 1], [-1, -2, 1], [-1, -4, 0, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 7, 7, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 7, 7, -5, -2, 1], [-4, -1, 1], [1, -2, -1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow042.row
      (by norm_num [DegreeFiveSafeRow042.row])
      DegreeFiveSafeRow042.properties,
    DegreeFiveCertifiedCase.reducible
      [-2, 7, 7, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 7, 7, -5, -2, 1], [-2, 1], [1, -3, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow043.row
      (by norm_num [DegreeFiveSafeRow043.row])
      DegreeFiveSafeRow043.properties,
    DegreeFiveCertifiedCase.reducible
      [-3, 8, 7, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 8, 7, -5, -2, 1], [-3, -1, 1], [1, -3, -1, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -2, 8, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -2, 8, -5, -2, 1], [-1, 1], [0, 2, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-1, -1, 8, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-1, -1, 8, -5, -2, 1], [-1, 1], [1, 2, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [0, -1, 8, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, -1, 8, -5, -2, 1], [0, 1], [-1, 8, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-2, 0, 8, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 0, 8, -5, -2, 1], [-1, 1], [2, 2, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow044.row
      (by norm_num [DegreeFiveSafeRow044.row])
      DegreeFiveSafeRow044.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 0, 8, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 0, 8, -5, -2, 1], [0, 1], [0, 8, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-3, 1, 8, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-3, 1, 8, -5, -2, 1], [-1, 1], [3, 2, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow045.row
      (by norm_num [DegreeFiveSafeRow045.row])
      DegreeFiveSafeRow045.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow046.row
      (by norm_num [DegreeFiveSafeRow046.row])
      DegreeFiveSafeRow046.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 1, 8, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 1, 8, -5, -2, 1], [0, 1], [1, 8, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-4, 2, 8, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 2, 8, -5, -2, 1], [2, 1], [-2, 2, 3, -4, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow047.row
      (by norm_num [DegreeFiveSafeRow047.row])
      DegreeFiveSafeRow047.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow048.row
      (by norm_num [DegreeFiveSafeRow048.row])
      DegreeFiveSafeRow048.properties,
    DegreeFiveCertifiedCase.critical
      DegreeFiveCritical04.row
      (by norm_num [DegreeFiveCritical04.row])
      (by
        intro K _ _ a hpoly hgen
        exact DegreeFiveCritical04.field_discriminant_eq_recorded_of_minpoly
          a (by simpa [DegreeFiveCritical04.T] using hpoly) hgen),
    DegreeFiveCertifiedCase.reducible
      [0, 2, 8, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 2, 8, -5, -2, 1], [0, 1], [2, 8, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-5, 3, 8, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-5, 3, 8, -5, -2, 1], [-1, 1], [5, 2, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow049.row
      (by norm_num [DegreeFiveSafeRow049.row])
      DegreeFiveSafeRow049.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow050.row
      (by norm_num [DegreeFiveSafeRow050.row])
      DegreeFiveSafeRow050.properties,
    DegreeFiveCertifiedCase.reducible
      [-2, 3, 8, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 3, 8, -5, -2, 1], [2, 1], [-1, 2, 3, -4, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow051.row
      (by norm_num [DegreeFiveSafeRow051.row])
      DegreeFiveSafeRow051.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 3, 8, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 3, 8, -5, -2, 1], [0, 1], [3, 8, -5, -2, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-6, 4, 8, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-6, 4, 8, -5, -2, 1], [-1, 1], [6, 2, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow052.row
      (by norm_num [DegreeFiveSafeRow052.row])
      DegreeFiveSafeRow052.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow053.row
      (by norm_num [DegreeFiveSafeRow053.row])
      DegreeFiveSafeRow053.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow054.row
      (by norm_num [DegreeFiveSafeRow054.row])
      DegreeFiveSafeRow054.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow055.row
      (by norm_num [DegreeFiveSafeRow055.row])
      DegreeFiveSafeRow055.properties,
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow056.row
      (by norm_num [DegreeFiveSafeRow056.row])
      DegreeFiveSafeRow056.properties,
    DegreeFiveCertifiedCase.reducible
      [0, 4, 8, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[0, 4, 8, -5, -2, 1], [-2, 1], [0, -2, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-7, 5, 8, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-7, 5, 8, -5, -2, 1], [-1, 1], [7, 2, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow057.row
      (by norm_num [DegreeFiveSafeRow057.row])
      DegreeFiveSafeRow057.properties,
    DegreeFiveCertifiedCase.reducible
      [-5, 5, 8, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-5, 5, 8, -5, -2, 1], [1, 1], [-5, 10, -2, -3, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.critical
      DegreeFiveCritical05.row
      (by norm_num [DegreeFiveCritical05.row])
      (by
        intro K _ _ a hpoly hgen
        exact DegreeFiveCritical05.field_discriminant_eq_recorded_of_minpoly
          a (by simpa [DegreeFiveCritical05.T] using hpoly) hgen),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow058.row
      (by norm_num [DegreeFiveSafeRow058.row])
      DegreeFiveSafeRow058.properties,
    DegreeFiveCertifiedCase.reducible
      [-2, 5, 8, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-2, 5, 8, -5, -2, 1], [-2, 1], [1, -2, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-8, 6, 8, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-8, 6, 8, -5, -2, 1], [-1, 1], [8, 2, -6, -1, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow059.row
      (by norm_num [DegreeFiveSafeRow059.row])
      DegreeFiveSafeRow059.properties,
    DegreeFiveCertifiedCase.reducible
      [-6, 6, 8, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-6, 6, 8, -5, -2, 1], [-3, 0, 1], [2, -2, -2, 1], 2, 3⟩ (by decide)),
    DegreeFiveCertifiedCase.safe
      DegreeFiveSafeRow060.row
      (by norm_num [DegreeFiveSafeRow060.row])
      DegreeFiveSafeRow060.properties,
    DegreeFiveCertifiedCase.reducible
      [-4, 6, 8, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-4, 6, 8, -5, -2, 1], [-2, 1], [2, -2, -5, 0, 1], 1, 4⟩ (by decide)),
    DegreeFiveCertifiedCase.reducible
      [-6, 7, 8, -5, -2, 1] (by
        exact not_irreducible_of_factorCertificate
          ⟨[-6, 7, 8, -5, -2, 1], [-2, 1], [3, -2, -5, 0, 1], 1, 4⟩ (by decide))
  ]

set_option linter.unnecessarySeqFocus false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation identifies the generated Rolle rows with their
-- proof-bearing classification cases.
theorem degreeFiveCertifiedCasesChunk003_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈
          (degreeFiveStageFiveEntriesChunk003.flatMap fun entry =>
            entry.a0Candidates.toList.map fun a0 =>
              [a0, entry.a1, entry.a2, entry.a3, entry.a4, 1]) ↔
        coefficients ∈
          degreeFiveCertifiedCasesChunk003.{u}.map
            DegreeFiveCertifiedCase.coefficients := by
  intro coefficients
  simp only [degreeFiveCertifiedCasesChunk003, List.map_cons, List.map_nil,
    DegreeFiveCertifiedCase.coefficients]
  norm_num [degreeFiveStageFiveEntriesChunk003,
    DegreeFiveSafeRow028.row,
    DegreeFiveSafeRow029.row,
    DegreeFiveSafeRow030.row,
    DegreeFiveSafeRow031.row,
    DegreeFiveSafeRow032.row,
    DegreeFiveSafeRow033.row,
    DegreeFiveSafeRow034.row,
    DegreeFiveSafeRow035.row,
    DegreeFiveSafeRow036.row,
    DegreeFiveSafeRow037.row,
    DegreeFiveSafeRow038.row,
    DegreeFiveSafeRow039.row,
    DegreeFiveSafeRow040.row,
    DegreeFiveSafeRow041.row,
    DegreeFiveSafeRow042.row,
    DegreeFiveSafeRow043.row,
    DegreeFiveSafeRow044.row,
    DegreeFiveSafeRow045.row,
    DegreeFiveSafeRow046.row,
    DegreeFiveSafeRow047.row,
    DegreeFiveSafeRow048.row,
    DegreeFiveSafeRow049.row,
    DegreeFiveSafeRow050.row,
    DegreeFiveSafeRow051.row,
    DegreeFiveSafeRow052.row,
    DegreeFiveSafeRow053.row,
    DegreeFiveSafeRow054.row,
    DegreeFiveSafeRow055.row,
    DegreeFiveSafeRow056.row,
    DegreeFiveSafeRow057.row,
    DegreeFiveSafeRow058.row,
    DegreeFiveSafeRow059.row,
    DegreeFiveSafeRow060.row,
    DegreeFiveCritical04.row,
    DegreeFiveCritical05.row,
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
