import TraceEuclidean.DegreeSevenRolleStageSevenPrefixBridge

/-! Rows200To299Chunk001 data for exact six-root Stage Seven certificates. -/

namespace TraceEuclidean

noncomputable section

open Polynomial

set_option maxRecDepth 100000

def degreeSevenStageSevenClassificationsRows200To299Chunk001 :
    List DegreeSevenStageSevenClassification :=
  [
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (27 : ℤ), (21 : ℤ), (5 : ℤ), (-1 : ℚ)⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (27 : ℤ), (22 : ℤ), (7 : ℤ), (16777216 : ℤ), (-17829673 : ℤ), (-17829670 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-7805337 : ℤ), (-7805334 : ℤ), (-5466265 : ℤ), (-5466262 : ℤ), (27514687 : ℤ), (27514690 : ℤ), (63505210 : ℤ), (63505213 : ℤ)⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (28 : ℤ), (24 : ℤ), (8 : ℤ), (-1 : ℚ)⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (29 : ℤ), (26 : ℤ), (9 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-15075101 : ℤ), (-15075098 : ℤ), (-11316697 : ℤ), (-11316694 : ℤ), (-5531302 : ℤ), (-5531299 : ℤ), (28668357 : ℤ), (28668360 : ℤ), (63173365 : ℤ), (63173368 : ℤ)⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (1 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-31594932 : ℤ), (-31594929 : ℤ), (-4520580 : ℤ), (-4520577 : ℤ), (-2 : ℤ), (2 : ℤ), (4827906 : ℤ), (4827909 : ℤ), (8332656 : ℤ), (8332659 : ℤ), (66096355 : ℤ), (66096358 : ℤ)⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩
  ]

def degreeSevenStageSevenScaledRows200To299Chunk001 :
    List DegreeSevenStageSevenScaledEntry :=
  DegreeSevenStageSevenClassification.scaledEntries
    degreeSevenStageSevenClassificationsRows200To299Chunk001

def degreeSevenStageSevenMultipleRootRows200To299Chunk001 :
    List DegreeSevenStageSevenMultipleRootWitness :=
  DegreeSevenStageSevenClassification.multipleRoots
    degreeSevenStageSevenClassificationsRows200To299Chunk001

def degreeSevenStageSevenScaledCriticalSignRows200To299Chunk001 :
    List DegreeSevenStageSevenScaledCriticalSignWitness :=
  DegreeSevenStageSevenClassification.criticalSigns
    degreeSevenStageSevenClassificationsRows200To299Chunk001

set_option maxHeartbeats 0 in
-- Kernel reduction checks every scaled parent and forbidden interval sign.
theorem degreeSevenStageSevenScaledCriticalSignRows200To299Chunk001_arithmeticValid :
    degreeSevenStageSevenScaledCriticalSignRows200To299Chunk001.Forall
      DegreeSevenStageSevenScaledCriticalSignWitness.ArithmeticValid := by
  decide

theorem degreeSevenStageSevenScaledCriticalSignRows200To299Chunk001_valid :
    degreeSevenStageSevenScaledCriticalSignRows200To299Chunk001.Forall
      (fun witness => witness.toWitness.Valid) := by
  exact degreeSevenStageSevenScaledCriticalSignRows200To299Chunk001_arithmeticValid.imp
    DegreeSevenStageSevenScaledCriticalSignWitness.valid_of_arithmeticValid

def degreeSevenStageSevenCriticalSignRows200To299Chunk001 :
    List DegreeSevenStageSevenCriticalSignWitness :=
  degreeSevenStageSevenScaledCriticalSignRows200To299Chunk001.map
    DegreeSevenStageSevenScaledCriticalSignWitness.toWitness

theorem degreeSevenStageSevenCriticalSignRows200To299Chunk001_valid :
    degreeSevenStageSevenCriticalSignRows200To299Chunk001.Forall
      DegreeSevenStageSevenCriticalSignWitness.Valid := by
  rw [degreeSevenStageSevenCriticalSignRows200To299Chunk001, List.forall_map_iff]
  change degreeSevenStageSevenScaledCriticalSignRows200To299Chunk001.Forall
    (fun witness => witness.toWitness.Valid)
  exact degreeSevenStageSevenScaledCriticalSignRows200To299Chunk001_valid


set_option maxHeartbeats 0 in
theorem degreeSevenStageSevenScaledRows200To299Chunk001_arithmeticValid :
    degreeSevenStageSevenScaledRows200To299Chunk001.Forall
      DegreeSevenStageSevenScaledEntry.ArithmeticValid := by
  decide

theorem degreeSevenStageSevenScaledRows200To299Chunk001_valid :
    degreeSevenStageSevenScaledRows200To299Chunk001.Forall
      (fun entry => entry.toEntry.Valid) := by
  exact degreeSevenStageSevenScaledRows200To299Chunk001_arithmeticValid.imp
    DegreeSevenStageSevenScaledEntry.valid_of_arithmeticValid

theorem degreeSevenStageSevenMultipleRootRows200To299Chunk001_valid :
    degreeSevenStageSevenMultipleRootRows200To299Chunk001.Forall
      DegreeSevenStageSevenMultipleRootWitness.Valid := by
  norm_num [degreeSevenStageSevenMultipleRootRows200To299Chunk001,
    degreeSevenStageSevenClassificationsRows200To299Chunk001,
    DegreeSevenStageSevenClassification.multipleRoots,
    DegreeSevenStageSevenMultipleRootWitness.Valid,
    DegreeSevenStageSevenMultipleRootWitness.coefficients,
    integerPolynomialRationalEval,
    DensePolynomial.derivative, DensePolynomial.add,
    DensePolynomial.eval]

theorem degreeSevenStageSevenClassificationsRows200To299Chunk001_valid :
    degreeSevenStageSevenClassificationsRows200To299Chunk001.Forall
      DegreeSevenStageSevenClassification.Valid := by
  apply DegreeSevenStageSevenClassification.forall_valid_of_projections
  · exact degreeSevenStageSevenScaledRows200To299Chunk001_valid
  · exact degreeSevenStageSevenMultipleRootRows200To299Chunk001_valid
  · exact degreeSevenStageSevenScaledCriticalSignRows200To299Chunk001_valid

/-- Every Hunter candidate matching a certified pilot row has its constant
coefficient in that row's exact final finite set. -/
theorem degreeSevenStageSevenRows200To299Chunk001_a0_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (entry : DegreeSevenStageSevenScaledEntry)
    (hentry : entry ∈ degreeSevenStageSevenScaledRows200To299Chunk001)
    (ha6 : entry.a6 = f.coeff 6)
    (ha5 : entry.a5 = f.coeff 5)
    (ha4 : entry.a4 = f.coeff 4)
    (ha3 : entry.a3 = f.coeff 3)
    (ha2 : entry.a2 = f.coeff 2)
    (ha1 : entry.a1 = f.coeff 1) :
    f.coeff 0 ∈ entry.toEntry.a0Candidates := by
  apply degreeSeven_minimumHunterCandidate_a0_mem_of_stageSeven
    h entry.toEntry
  · exact (List.forall_iff_forall_mem.mp
      degreeSevenStageSevenScaledRows200To299Chunk001_valid) entry hentry
  · exact ha6
  · exact ha5
  · exact ha4
  · exact ha3
  · exact ha2
  · exact ha1

end

end TraceEuclidean
