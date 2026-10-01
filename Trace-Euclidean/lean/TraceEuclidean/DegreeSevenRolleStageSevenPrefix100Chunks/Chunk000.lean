import TraceEuclidean.DegreeSevenRolleStageSevenPrefixBridge

/-! Prefix100Chunk000 data for exact six-root Stage Seven certificates. -/

namespace TraceEuclidean

noncomputable section

open Polynomial

set_option maxRecDepth 100000

def degreeSevenStageSevenClassificationsPrefix100Chunk000 :
    List DegreeSevenStageSevenClassification :=
  [
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (-6 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (-5 : ℤ), (1 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-14966214 : ℤ), (-14966211 : ℤ), (-11448128 : ℤ), (-11448125 : ℤ), (-6427691 : ℤ), (-6427688 : ℤ), (-2 : ℤ), (2 : ℤ), (4847778 : ℤ), (4847781 : ℤ), (71135659 : ℤ), (71135662 : ℤ)⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (-4 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-4 : ℤ), (1 : ℤ), (1 : ℤ), (1 : ℤ), (4294967296 : ℤ), (-4147683683 : ℤ), (-4147683680 : ℤ), (-1393613328 : ℤ), (-1393613325 : ℤ), (-980273798 : ℤ), (-980273795 : ℤ), (824281163 : ℤ), (824281166 : ℤ), (14900790987 : ℤ), (14900790990 : ℤ)⟩, (1 : ℤ), (0 : ℤ), .second⟩
  ]

def degreeSevenStageSevenScaledPrefix100Chunk000 :
    List DegreeSevenStageSevenScaledEntry :=
  DegreeSevenStageSevenClassification.scaledEntries
    degreeSevenStageSevenClassificationsPrefix100Chunk000

def degreeSevenStageSevenMultipleRootPrefix100Chunk000 :
    List DegreeSevenStageSevenMultipleRootWitness :=
  DegreeSevenStageSevenClassification.multipleRoots
    degreeSevenStageSevenClassificationsPrefix100Chunk000

def degreeSevenStageSevenScaledCriticalSignPrefix100Chunk000 :
    List DegreeSevenStageSevenScaledCriticalSignWitness :=
  DegreeSevenStageSevenClassification.criticalSigns
    degreeSevenStageSevenClassificationsPrefix100Chunk000

set_option maxHeartbeats 0 in
-- Kernel reduction checks every scaled parent and forbidden interval sign.
theorem degreeSevenStageSevenScaledCriticalSignPrefix100Chunk000_arithmeticValid :
    degreeSevenStageSevenScaledCriticalSignPrefix100Chunk000.Forall
      DegreeSevenStageSevenScaledCriticalSignWitness.ArithmeticValid := by
  decide

theorem degreeSevenStageSevenScaledCriticalSignPrefix100Chunk000_valid :
    degreeSevenStageSevenScaledCriticalSignPrefix100Chunk000.Forall
      (fun witness => witness.toWitness.Valid) := by
  exact degreeSevenStageSevenScaledCriticalSignPrefix100Chunk000_arithmeticValid.imp
    DegreeSevenStageSevenScaledCriticalSignWitness.valid_of_arithmeticValid

def degreeSevenStageSevenCriticalSignPrefix100Chunk000 :
    List DegreeSevenStageSevenCriticalSignWitness :=
  degreeSevenStageSevenScaledCriticalSignPrefix100Chunk000.map
    DegreeSevenStageSevenScaledCriticalSignWitness.toWitness

theorem degreeSevenStageSevenCriticalSignPrefix100Chunk000_valid :
    degreeSevenStageSevenCriticalSignPrefix100Chunk000.Forall
      DegreeSevenStageSevenCriticalSignWitness.Valid := by
  rw [degreeSevenStageSevenCriticalSignPrefix100Chunk000, List.forall_map_iff]
  change degreeSevenStageSevenScaledCriticalSignPrefix100Chunk000.Forall
    (fun witness => witness.toWitness.Valid)
  exact degreeSevenStageSevenScaledCriticalSignPrefix100Chunk000_valid


theorem degreeSevenStageSevenScaledPrefix100Chunk000_arithmeticValid :
    degreeSevenStageSevenScaledPrefix100Chunk000.Forall
      DegreeSevenStageSevenScaledEntry.ArithmeticValid := by
  decide

theorem degreeSevenStageSevenScaledPrefix100Chunk000_valid :
    degreeSevenStageSevenScaledPrefix100Chunk000.Forall
      (fun entry => entry.toEntry.Valid) := by
  exact degreeSevenStageSevenScaledPrefix100Chunk000_arithmeticValid.imp
    DegreeSevenStageSevenScaledEntry.valid_of_arithmeticValid

set_option maxHeartbeats 0 in
-- Kernel reduction checks that the certified final interval is empty.
theorem degreeSevenStageSevenScaledPrefix100Chunk000_a0Candidates_empty :
    degreeSevenStageSevenScaledPrefix100Chunk000.Forall
      (fun entry => entry.toEntry.a0Candidates = ∅) := by
  norm_num [degreeSevenStageSevenScaledPrefix100Chunk000,
    degreeSevenStageSevenClassificationsPrefix100Chunk000,
    DegreeSevenStageSevenClassification.scaledEntries,
    DegreeSevenStageSevenEntry.a0Candidates,
    DegreeSevenStageSevenEntry.baseCoefficients,
    DegreeSevenStageSevenEntry.leftEndpoint,
    DegreeSevenStageSevenEntry.rightEndpoint,
    DegreeSevenStageSevenScaledEntry.toEntry,
    DegreeSevenStageSevenScaledEntry.interval,
    septicTranslationCandidates, integerIcc,
    septicTranslationLowerBound, septicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat]

theorem degreeSevenStageSevenMultipleRootPrefix100Chunk000_valid :
    degreeSevenStageSevenMultipleRootPrefix100Chunk000.Forall
      DegreeSevenStageSevenMultipleRootWitness.Valid := by
  norm_num [degreeSevenStageSevenMultipleRootPrefix100Chunk000,
    degreeSevenStageSevenClassificationsPrefix100Chunk000,
    DegreeSevenStageSevenClassification.multipleRoots,
    DegreeSevenStageSevenMultipleRootWitness.Valid,
    DegreeSevenStageSevenMultipleRootWitness.coefficients,
    integerPolynomialRationalEval,
    DensePolynomial.derivative, DensePolynomial.add,
    DensePolynomial.eval]

theorem degreeSevenStageSevenClassificationsPrefix100Chunk000_valid :
    degreeSevenStageSevenClassificationsPrefix100Chunk000.Forall
      DegreeSevenStageSevenClassification.Valid := by
  apply DegreeSevenStageSevenClassification.forall_valid_of_projections
  · exact degreeSevenStageSevenScaledPrefix100Chunk000_valid
  · exact degreeSevenStageSevenMultipleRootPrefix100Chunk000_valid
  · exact degreeSevenStageSevenScaledCriticalSignPrefix100Chunk000_valid

/-- Every Hunter candidate matching a certified pilot row has its constant
coefficient in that row's exact final finite set. -/
theorem degreeSevenStageSevenPrefix100Chunk000_a0_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (entry : DegreeSevenStageSevenScaledEntry)
    (hentry : entry ∈ degreeSevenStageSevenScaledPrefix100Chunk000)
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
      degreeSevenStageSevenScaledPrefix100Chunk000_valid) entry hentry
  · exact ha6
  · exact ha5
  · exact ha4
  · exact ha3
  · exact ha2
  · exact ha1

end

end TraceEuclidean
