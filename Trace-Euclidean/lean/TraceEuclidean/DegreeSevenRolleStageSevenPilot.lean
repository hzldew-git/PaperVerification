import TraceEuclidean.DegreeSevenRolleStageSevenRejectedScaled

/-! Pilot data for exact six-root Stage Seven certificates. -/

namespace TraceEuclidean

noncomputable section

open Polynomial

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPilot :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (-5 : ℤ), (1 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-14966214 : ℤ), (-14966211 : ℤ), (-11448128 : ℤ), (-11448125 : ℤ), (-6427691 : ℤ), (-6427688 : ℤ), (-2 : ℤ), (2 : ℤ), (4847778 : ℤ), (4847781 : ℤ), (71135659 : ℤ), (71135662 : ℤ)⟩
  ]

def degreeSevenStageSevenMultipleRootPilot :
    List DegreeSevenStageSevenMultipleRootWitness :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (-6 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (-4 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩
  ]

def degreeSevenStageSevenScaledCriticalSignPilot :
    List DegreeSevenStageSevenScaledCriticalSignWitness :=
  [
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (-4 : ℤ), (1 : ℤ), (1 : ℤ), (1 : ℤ), (4294967296 : ℤ), (-4147683683 : ℤ), (-4147683680 : ℤ), (-1393613328 : ℤ), (-1393613325 : ℤ), (-980273798 : ℤ), (-980273795 : ℤ), (824281163 : ℤ), (824281166 : ℤ), (14900790987 : ℤ), (14900790990 : ℤ)⟩, (1 : ℤ), (0 : ℤ), .second⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel reduction checks every scaled parent and forbidden interval sign.
theorem degreeSevenStageSevenScaledCriticalSignPilot_arithmeticValid :
    degreeSevenStageSevenScaledCriticalSignPilot.Forall
      DegreeSevenStageSevenScaledCriticalSignWitness.ArithmeticValid := by
  decide

theorem degreeSevenStageSevenScaledCriticalSignPilot_valid :
    degreeSevenStageSevenScaledCriticalSignPilot.Forall
      (fun witness => witness.toWitness.Valid) := by
  exact degreeSevenStageSevenScaledCriticalSignPilot_arithmeticValid.imp
    DegreeSevenStageSevenScaledCriticalSignWitness.valid_of_arithmeticValid

def degreeSevenStageSevenCriticalSignPilot :
    List DegreeSevenStageSevenCriticalSignWitness :=
  degreeSevenStageSevenScaledCriticalSignPilot.map
    DegreeSevenStageSevenScaledCriticalSignWitness.toWitness

theorem degreeSevenStageSevenCriticalSignPilot_valid :
    degreeSevenStageSevenCriticalSignPilot.Forall
      DegreeSevenStageSevenCriticalSignWitness.Valid := by
  rw [degreeSevenStageSevenCriticalSignPilot, List.forall_map_iff]
  change degreeSevenStageSevenScaledCriticalSignPilot.Forall
    (fun witness => witness.toWitness.Valid)
  exact degreeSevenStageSevenScaledCriticalSignPilot_valid


theorem degreeSevenStageSevenScaledPilot_arithmeticValid :
    degreeSevenStageSevenScaledPilot.Forall
      DegreeSevenStageSevenScaledEntry.ArithmeticValid := by
  decide

theorem degreeSevenStageSevenScaledPilot_valid :
    degreeSevenStageSevenScaledPilot.Forall
      (fun entry => entry.toEntry.Valid) := by
  exact degreeSevenStageSevenScaledPilot_arithmeticValid.imp
    DegreeSevenStageSevenScaledEntry.valid_of_arithmeticValid

set_option maxHeartbeats 0 in
-- Kernel reduction checks that the certified final interval is empty.
theorem degreeSevenStageSevenScaledPilot_a0Candidates_empty :
    degreeSevenStageSevenScaledPilot.Forall
      (fun entry => entry.toEntry.a0Candidates = ∅) := by
  norm_num [degreeSevenStageSevenScaledPilot,
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

theorem degreeSevenStageSevenMultipleRootPilot_valid :
    degreeSevenStageSevenMultipleRootPilot.Forall
      DegreeSevenStageSevenMultipleRootWitness.Valid := by
  norm_num [degreeSevenStageSevenMultipleRootPilot,
    DegreeSevenStageSevenMultipleRootWitness.Valid,
    DegreeSevenStageSevenMultipleRootWitness.coefficients,
    integerPolynomialRationalEval,
    DensePolynomial.derivative, DensePolynomial.add,
    DensePolynomial.eval]

/-- Every Hunter candidate matching a certified pilot row has its constant
coefficient in that row's exact final finite set. -/
theorem degreeSevenStageSevenPilot_a0_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (entry : DegreeSevenStageSevenScaledEntry)
    (hentry : entry ∈ degreeSevenStageSevenScaledPilot)
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
      degreeSevenStageSevenScaledPilot_valid) entry hentry
  · exact ha6
  · exact ha5
  · exact ha4
  · exact ha3
  · exact ha2
  · exact ha1

end

end TraceEuclidean
