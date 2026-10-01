import TraceEuclidean.DegreeSevenRolleStageSevenPrefixBridge

/-! Rows200To299Chunk005 data for exact six-root Stage Seven certificates. -/

namespace TraceEuclidean

noncomputable section

open Polynomial

set_option maxRecDepth 100000

def degreeSevenStageSevenClassificationsRows200To299Chunk005 :
    List DegreeSevenStageSevenClassification :=
  [
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (32 : ℤ), (29 : ℤ), (10 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-14298336 : ℤ), (-14298333 : ℤ), (-13211769 : ℤ), (-13211766 : ℤ), (-5284899 : ℤ), (-5284896 : ℤ), (30643145 : ℤ), (30643148 : ℤ), (62070481 : ℤ), (62070484 : ℤ)⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (1 : ℤ), (-2 : ℤ), (-2 : ℤ), (4294967296 : ℤ), (-6622778603 : ℤ), (-6622778600 : ℤ), (-865507950 : ℤ), (-865507947 : ℤ), (977416079 : ℤ), (977416082 : ℤ), (1783348452 : ℤ), (1783348455 : ℤ), (13931023362 : ℤ), (13931023365 : ℤ)⟩, (-2 : ℤ), (0 : ℤ), .fourth⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (1 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-32278195 : ℤ), (-32278192 : ℤ), (-4295675 : ℤ), (-4295672 : ℤ), (-2 : ℤ), (2 : ℤ), (4223434 : ℤ), (4223437 : ℤ), (9884979 : ℤ), (9884982 : ℤ), (65606863 : ℤ), (65606866 : ℤ)⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (2 : ℤ), (-3 : ℤ), (-3 : ℤ), (4294967296 : ℤ), (-6570023277 : ℤ), (-6570023274 : ℤ), (-1112064756 : ℤ), (-1112064753 : ℤ), (1098847773 : ℤ), (1098847776 : ℤ), (1868446704 : ℤ), (1868446707 : ℤ), (13918294897 : ℤ), (13918294900 : ℤ)⟩, (-3 : ℤ), (0 : ℤ), .fourth⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (2 : ℤ), (-3 : ℤ), (-3 : ℤ), (4294967296 : ℤ), (-6570023277 : ℤ), (-6570023274 : ℤ), (-1112064756 : ℤ), (-1112064753 : ℤ), (1098847773 : ℤ), (1098847776 : ℤ), (1868446704 : ℤ), (1868446707 : ℤ), (13918294897 : ℤ), (13918294900 : ℤ)⟩, (-3 : ℤ), (1 : ℤ), .third⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (2 : ℤ), (-2 : ℤ), (-2 : ℤ), (4294967296 : ℤ), (-6579596324 : ℤ), (-6579596321 : ℤ), (-969908959 : ℤ), (-969908956 : ℤ), (751965676 : ℤ), (751965679 : ℤ), (2084209674 : ℤ), (2084209677 : ℤ), (13916831275 : ℤ), (13916831278 : ℤ)⟩, (-2 : ℤ), (-1 : ℤ), .second⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (2 : ℤ), (-2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-31918611 : ℤ), (-31918608 : ℤ), (-6178881 : ℤ), (-6178878 : ℤ), (-2 : ℤ), (2 : ℤ), (6141824 : ℤ), (6141827 : ℤ), (9569420 : ℤ), (9569423 : ℤ), (65527653 : ℤ), (65527656 : ℤ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (2 : ℤ), (-2 : ℤ), (-2 : ℤ), (4294967296 : ℤ), (-6579596324 : ℤ), (-6579596321 : ℤ), (-969908959 : ℤ), (-969908956 : ℤ), (751965676 : ℤ), (751965679 : ℤ), (2084209674 : ℤ), (2084209677 : ℤ), (13916831275 : ℤ), (13916831278 : ℤ)⟩, (-2 : ℤ), (1 : ℤ), .third⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (2 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-32013598 : ℤ), (-32013595 : ℤ), (-4935765 : ℤ), (-4935762 : ℤ), (-2 : ℤ), (2 : ℤ), (3233615 : ℤ), (3233618 : ℤ), (11345872 : ℤ), (11345875 : ℤ), (65511282 : ℤ), (65511285 : ℤ)⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (2 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (3 : ℤ), (-4 : ℤ), (-4 : ℤ), (4294967296 : ℤ), (-6515208410 : ℤ), (-6515208407 : ℤ), (-1328425846 : ℤ), (-1328425843 : ℤ), (1177878369 : ℤ), (1177878372 : ℤ), (1963754706 : ℤ), (1963754709 : ℤ), (13905502522 : ℤ), (13905502525 : ℤ)⟩, (-4 : ℤ), (0 : ℤ), .fourth⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (3 : ℤ), (-4 : ℤ), (1 : ℤ), (16777216 : ℤ), (-31406332 : ℤ), (-31406329 : ℤ), (-9105125 : ℤ), (-9105122 : ℤ), (2948376 : ℤ), (2948379 : ℤ), (7022114 : ℤ), (7022117 : ℤ), (8220079 : ℤ), (8220082 : ℤ), (65462292 : ℤ), (65462295 : ℤ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (3 : ℤ), (-4 : ℤ), (-4 : ℤ), (4294967296 : ℤ), (-6515208410 : ℤ), (-6515208407 : ℤ), (-1328425846 : ℤ), (-1328425843 : ℤ), (1177878369 : ℤ), (1177878372 : ℤ), (1963754706 : ℤ), (1963754709 : ℤ), (13905502522 : ℤ), (13905502525 : ℤ)⟩, (-4 : ℤ), (2 : ℤ), .third⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (3 : ℤ), (-3 : ℤ), (-3 : ℤ), (4294967296 : ℤ), (-6525232327 : ℤ), (-6525232324 : ℤ), (-1214202606 : ℤ), (-1214202603 : ℤ), (876446441 : ℤ), (876446444 : ℤ), (2162459823 : ℤ), (2162459826 : ℤ), (13904030010 : ℤ), (13904030013 : ℤ)⟩, (-3 : ℤ), (-1 : ℤ), .fourth⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (3 : ℤ), (-3 : ℤ), (-3 : ℤ), (4294967296 : ℤ), (-6525232327 : ℤ), (-6525232324 : ℤ), (-1214202606 : ℤ), (-1214202603 : ℤ), (876446441 : ℤ), (876446444 : ℤ), (2162459823 : ℤ), (2162459826 : ℤ), (13904030010 : ℤ), (13904030013 : ℤ)⟩, (-3 : ℤ), (0 : ℤ), .fourth⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (3 : ℤ), (-3 : ℤ), (-3 : ℤ), (4294967296 : ℤ), (-6525232327 : ℤ), (-6525232324 : ℤ), (-1214202606 : ℤ), (-1214202603 : ℤ), (876446441 : ℤ), (876446444 : ℤ), (2162459823 : ℤ), (2162459826 : ℤ), (13904030010 : ℤ), (13904030013 : ℤ)⟩, (-3 : ℤ), (1 : ℤ), .third⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (3 : ℤ), (-2 : ℤ), (-2 : ℤ), (4294967296 : ℤ), (-6535159234 : ℤ), (-6535159231 : ℤ), (-1079715990 : ℤ), (-1079715987 : ℤ), (617309760 : ℤ), (617309763 : ℤ), (2298510510 : ℤ), (2298510513 : ℤ), (13902556294 : ℤ), (13902556297 : ℤ)⟩, (-2 : ℤ), (-1 : ℤ), .second⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (3 : ℤ), (-2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-31639697 : ℤ), (-31639694 : ℤ), (-6778334 : ℤ), (-6778331 : ℤ), (-2 : ℤ), (2 : ℤ), (4762421 : ℤ), (4762424 : ℤ), (11365586 : ℤ), (11365589 : ℤ), (65431429 : ℤ), (65431432 : ℤ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (3 : ℤ), (-2 : ℤ), (-2 : ℤ), (4294967296 : ℤ), (-6535159234 : ℤ), (-6535159231 : ℤ), (-1079715990 : ℤ), (-1079715987 : ℤ), (617309760 : ℤ), (617309763 : ℤ), (2298510510 : ℤ), (2298510513 : ℤ), (13902556294 : ℤ), (13902556297 : ℤ)⟩, (-2 : ℤ), (1 : ℤ), .third⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (3 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-31739214 : ℤ), (-31739211 : ℤ), (-5612288 : ℤ), (-5612285 : ℤ), (-2 : ℤ), (2 : ℤ), (2615181 : ℤ), (2615184 : ℤ), (12462832 : ℤ), (12462835 : ℤ), (65414895 : ℤ), (65414898 : ℤ)⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (3 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩
  ]

def degreeSevenStageSevenScaledRows200To299Chunk005 :
    List DegreeSevenStageSevenScaledEntry :=
  DegreeSevenStageSevenClassification.scaledEntries
    degreeSevenStageSevenClassificationsRows200To299Chunk005

def degreeSevenStageSevenMultipleRootRows200To299Chunk005 :
    List DegreeSevenStageSevenMultipleRootWitness :=
  DegreeSevenStageSevenClassification.multipleRoots
    degreeSevenStageSevenClassificationsRows200To299Chunk005

def degreeSevenStageSevenScaledCriticalSignRows200To299Chunk005 :
    List DegreeSevenStageSevenScaledCriticalSignWitness :=
  DegreeSevenStageSevenClassification.criticalSigns
    degreeSevenStageSevenClassificationsRows200To299Chunk005

set_option maxHeartbeats 0 in
-- Kernel reduction checks every scaled parent and forbidden interval sign.
theorem degreeSevenStageSevenScaledCriticalSignRows200To299Chunk005_arithmeticValid :
    degreeSevenStageSevenScaledCriticalSignRows200To299Chunk005.Forall
      DegreeSevenStageSevenScaledCriticalSignWitness.ArithmeticValid := by
  decide

theorem degreeSevenStageSevenScaledCriticalSignRows200To299Chunk005_valid :
    degreeSevenStageSevenScaledCriticalSignRows200To299Chunk005.Forall
      (fun witness => witness.toWitness.Valid) := by
  exact degreeSevenStageSevenScaledCriticalSignRows200To299Chunk005_arithmeticValid.imp
    DegreeSevenStageSevenScaledCriticalSignWitness.valid_of_arithmeticValid

def degreeSevenStageSevenCriticalSignRows200To299Chunk005 :
    List DegreeSevenStageSevenCriticalSignWitness :=
  degreeSevenStageSevenScaledCriticalSignRows200To299Chunk005.map
    DegreeSevenStageSevenScaledCriticalSignWitness.toWitness

theorem degreeSevenStageSevenCriticalSignRows200To299Chunk005_valid :
    degreeSevenStageSevenCriticalSignRows200To299Chunk005.Forall
      DegreeSevenStageSevenCriticalSignWitness.Valid := by
  rw [degreeSevenStageSevenCriticalSignRows200To299Chunk005, List.forall_map_iff]
  change degreeSevenStageSevenScaledCriticalSignRows200To299Chunk005.Forall
    (fun witness => witness.toWitness.Valid)
  exact degreeSevenStageSevenScaledCriticalSignRows200To299Chunk005_valid


set_option maxHeartbeats 0 in
theorem degreeSevenStageSevenScaledRows200To299Chunk005_arithmeticValid :
    degreeSevenStageSevenScaledRows200To299Chunk005.Forall
      DegreeSevenStageSevenScaledEntry.ArithmeticValid := by
  decide

theorem degreeSevenStageSevenScaledRows200To299Chunk005_valid :
    degreeSevenStageSevenScaledRows200To299Chunk005.Forall
      (fun entry => entry.toEntry.Valid) := by
  exact degreeSevenStageSevenScaledRows200To299Chunk005_arithmeticValid.imp
    DegreeSevenStageSevenScaledEntry.valid_of_arithmeticValid

theorem degreeSevenStageSevenMultipleRootRows200To299Chunk005_valid :
    degreeSevenStageSevenMultipleRootRows200To299Chunk005.Forall
      DegreeSevenStageSevenMultipleRootWitness.Valid := by
  norm_num [degreeSevenStageSevenMultipleRootRows200To299Chunk005,
    degreeSevenStageSevenClassificationsRows200To299Chunk005,
    DegreeSevenStageSevenClassification.multipleRoots,
    DegreeSevenStageSevenMultipleRootWitness.Valid,
    DegreeSevenStageSevenMultipleRootWitness.coefficients,
    integerPolynomialRationalEval,
    DensePolynomial.derivative, DensePolynomial.add,
    DensePolynomial.eval]

theorem degreeSevenStageSevenClassificationsRows200To299Chunk005_valid :
    degreeSevenStageSevenClassificationsRows200To299Chunk005.Forall
      DegreeSevenStageSevenClassification.Valid := by
  apply DegreeSevenStageSevenClassification.forall_valid_of_projections
  · exact degreeSevenStageSevenScaledRows200To299Chunk005_valid
  · exact degreeSevenStageSevenMultipleRootRows200To299Chunk005_valid
  · exact degreeSevenStageSevenScaledCriticalSignRows200To299Chunk005_valid

/-- Every Hunter candidate matching a certified pilot row has its constant
coefficient in that row's exact final finite set. -/
theorem degreeSevenStageSevenRows200To299Chunk005_a0_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (entry : DegreeSevenStageSevenScaledEntry)
    (hentry : entry ∈ degreeSevenStageSevenScaledRows200To299Chunk005)
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
      degreeSevenStageSevenScaledRows200To299Chunk005_valid) entry hentry
  · exact ha6
  · exact ha5
  · exact ha4
  · exact ha3
  · exact ha2
  · exact ha1

end

end TraceEuclidean
