import TraceEuclidean.DegreeSevenRolleStageSevenPrefixBridge

/-! Rows200To299Chunk009 data for exact six-root Stage Seven certificates. -/

namespace TraceEuclidean

noncomputable section

open Polynomial

set_option maxRecDepth 100000

def degreeSevenStageSevenClassificationsRows200To299Chunk009 :
    List DegreeSevenStageSevenClassification :=
  [
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (34 : ℤ), (30 : ℤ), (10 : ℤ), (-1 : ℚ)⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (36 : ℤ), (35 : ℤ), (14 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-14589096 : ℤ), (-14589093 : ℤ), (-11933884 : ℤ), (-11933881 : ℤ), (-7545722 : ℤ), (-7545719 : ℤ), (33398356 : ℤ), (33398359 : ℤ), (60588967 : ℤ), (60588970 : ℤ)⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (9 : ℤ), (-2 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (9 : ℤ), (-1 : ℤ), (-1 : ℤ), (-1 : ℤ), (4294967296 : ℤ), (-6837322171 : ℤ), (-6837322168 : ℤ), (-448755825 : ℤ), (-448755822 : ℤ), (1019695110 : ℤ), (1019695113 : ℤ), (1604257289 : ℤ), (1604257292 : ℤ), (13865626939 : ℤ), (13865626942 : ℤ)⟩, (-1 : ℤ), (0 : ℤ), .fourth⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (9 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (9 : ℤ), (0 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-33170059 : ℤ), (-33170056 : ℤ), (-3550737 : ℤ), (-3550734 : ℤ), (-2 : ℤ), (2 : ℤ), (5261979 : ℤ), (5261982 : ℤ), (9398501 : ℤ), (9398504 : ℤ), (65201722 : ℤ), (65201725 : ℤ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (9 : ℤ), (1 : ℤ), (-3 : ℤ), (-3 : ℤ), (4294967296 : ℤ), (-6742757921 : ℤ), (-6742757918 : ℤ), (-972071495 : ℤ), (-972071492 : ℤ), (1278622362 : ℤ), (1278622365 : ℤ), (1800113157 : ℤ), (1800113160 : ℤ), (13839595238 : ℤ), (13839595241 : ℤ)⟩, (-3 : ℤ), (0 : ℤ), .fourth⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (9 : ℤ), (1 : ℤ), (-3 : ℤ), (-3 : ℤ), (4294967296 : ℤ), (-6742757921 : ℤ), (-6742757918 : ℤ), (-972071495 : ℤ), (-972071492 : ℤ), (1278622362 : ℤ), (1278622365 : ℤ), (1800113157 : ℤ), (1800113160 : ℤ), (13839595238 : ℤ), (13839595241 : ℤ)⟩, (-3 : ℤ), (1 : ℤ), .third⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (9 : ℤ), (1 : ℤ), (-2 : ℤ), (-2 : ℤ), (4294967296 : ℤ), (-6751275001 : ℤ), (-6751274998 : ℤ), (-827075389 : ℤ), (-827075386 : ℤ), (867673289 : ℤ), (867673292 : ℤ), (2076093398 : ℤ), (2076093401 : ℤ), (13838085044 : ℤ), (13838085047 : ℤ)⟩, (-2 : ℤ), (0 : ℤ), .fourth⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (9 : ℤ), (1 : ℤ), (-2 : ℤ), (-2 : ℤ), (4294967296 : ℤ), (-6751275001 : ℤ), (-6751274998 : ℤ), (-827075389 : ℤ), (-827075386 : ℤ), (867673289 : ℤ), (867673292 : ℤ), (2076093398 : ℤ), (2076093401 : ℤ), (13838085044 : ℤ), (13838085047 : ℤ)⟩, (-2 : ℤ), (1 : ℤ), .third⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (9 : ℤ), (1 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-32930157 : ℤ), (-32930154 : ℤ), (-4097439 : ℤ), (-4097436 : ℤ), (-2 : ℤ), (2 : ℤ), (3857289 : ℤ), (3857292 : ℤ), (11208279 : ℤ), (11208282 : ℤ), (65103432 : ℤ), (65103435 : ℤ)⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (9 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩
  ]

def degreeSevenStageSevenScaledRows200To299Chunk009 :
    List DegreeSevenStageSevenScaledEntry :=
  DegreeSevenStageSevenClassification.scaledEntries
    degreeSevenStageSevenClassificationsRows200To299Chunk009

def degreeSevenStageSevenMultipleRootRows200To299Chunk009 :
    List DegreeSevenStageSevenMultipleRootWitness :=
  DegreeSevenStageSevenClassification.multipleRoots
    degreeSevenStageSevenClassificationsRows200To299Chunk009

def degreeSevenStageSevenScaledCriticalSignRows200To299Chunk009 :
    List DegreeSevenStageSevenScaledCriticalSignWitness :=
  DegreeSevenStageSevenClassification.criticalSigns
    degreeSevenStageSevenClassificationsRows200To299Chunk009

set_option maxHeartbeats 0 in
-- Kernel reduction checks every scaled parent and forbidden interval sign.
theorem degreeSevenStageSevenScaledCriticalSignRows200To299Chunk009_arithmeticValid :
    degreeSevenStageSevenScaledCriticalSignRows200To299Chunk009.Forall
      DegreeSevenStageSevenScaledCriticalSignWitness.ArithmeticValid := by
  decide

theorem degreeSevenStageSevenScaledCriticalSignRows200To299Chunk009_valid :
    degreeSevenStageSevenScaledCriticalSignRows200To299Chunk009.Forall
      (fun witness => witness.toWitness.Valid) := by
  exact degreeSevenStageSevenScaledCriticalSignRows200To299Chunk009_arithmeticValid.imp
    DegreeSevenStageSevenScaledCriticalSignWitness.valid_of_arithmeticValid

def degreeSevenStageSevenCriticalSignRows200To299Chunk009 :
    List DegreeSevenStageSevenCriticalSignWitness :=
  degreeSevenStageSevenScaledCriticalSignRows200To299Chunk009.map
    DegreeSevenStageSevenScaledCriticalSignWitness.toWitness

theorem degreeSevenStageSevenCriticalSignRows200To299Chunk009_valid :
    degreeSevenStageSevenCriticalSignRows200To299Chunk009.Forall
      DegreeSevenStageSevenCriticalSignWitness.Valid := by
  rw [degreeSevenStageSevenCriticalSignRows200To299Chunk009, List.forall_map_iff]
  change degreeSevenStageSevenScaledCriticalSignRows200To299Chunk009.Forall
    (fun witness => witness.toWitness.Valid)
  exact degreeSevenStageSevenScaledCriticalSignRows200To299Chunk009_valid


set_option maxHeartbeats 0 in
theorem degreeSevenStageSevenScaledRows200To299Chunk009_arithmeticValid :
    degreeSevenStageSevenScaledRows200To299Chunk009.Forall
      DegreeSevenStageSevenScaledEntry.ArithmeticValid := by
  decide

theorem degreeSevenStageSevenScaledRows200To299Chunk009_valid :
    degreeSevenStageSevenScaledRows200To299Chunk009.Forall
      (fun entry => entry.toEntry.Valid) := by
  exact degreeSevenStageSevenScaledRows200To299Chunk009_arithmeticValid.imp
    DegreeSevenStageSevenScaledEntry.valid_of_arithmeticValid

theorem degreeSevenStageSevenMultipleRootRows200To299Chunk009_valid :
    degreeSevenStageSevenMultipleRootRows200To299Chunk009.Forall
      DegreeSevenStageSevenMultipleRootWitness.Valid := by
  norm_num [degreeSevenStageSevenMultipleRootRows200To299Chunk009,
    degreeSevenStageSevenClassificationsRows200To299Chunk009,
    DegreeSevenStageSevenClassification.multipleRoots,
    DegreeSevenStageSevenMultipleRootWitness.Valid,
    DegreeSevenStageSevenMultipleRootWitness.coefficients,
    integerPolynomialRationalEval,
    DensePolynomial.derivative, DensePolynomial.add,
    DensePolynomial.eval]

theorem degreeSevenStageSevenClassificationsRows200To299Chunk009_valid :
    degreeSevenStageSevenClassificationsRows200To299Chunk009.Forall
      DegreeSevenStageSevenClassification.Valid := by
  apply DegreeSevenStageSevenClassification.forall_valid_of_projections
  · exact degreeSevenStageSevenScaledRows200To299Chunk009_valid
  · exact degreeSevenStageSevenMultipleRootRows200To299Chunk009_valid
  · exact degreeSevenStageSevenScaledCriticalSignRows200To299Chunk009_valid

/-- Every Hunter candidate matching a certified pilot row has its constant
coefficient in that row's exact final finite set. -/
theorem degreeSevenStageSevenRows200To299Chunk009_a0_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (entry : DegreeSevenStageSevenScaledEntry)
    (hentry : entry ∈ degreeSevenStageSevenScaledRows200To299Chunk009)
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
      degreeSevenStageSevenScaledRows200To299Chunk009_valid) entry hentry
  · exact ha6
  · exact ha5
  · exact ha4
  · exact ha3
  · exact ha2
  · exact ha1

end

end TraceEuclidean
