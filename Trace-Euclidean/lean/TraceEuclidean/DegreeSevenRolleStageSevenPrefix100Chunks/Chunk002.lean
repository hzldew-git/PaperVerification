import TraceEuclidean.DegreeSevenRolleStageSevenPrefixBridge

/-! Prefix100Chunk002 data for exact six-root Stage Seven certificates. -/

namespace TraceEuclidean

noncomputable section

open Polynomial

set_option maxRecDepth 100000

def degreeSevenStageSevenClassificationsPrefix100Chunk002 :
    List DegreeSevenStageSevenClassification :=
  [
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (2 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (2 : ℤ), (1 : ℤ), (1 : ℤ), (4294967296 : ℤ), (-4722934890 : ℤ), (-4722934887 : ℤ), (-1149102270 : ℤ), (-1149102267 : ℤ), (-780893024 : ℤ), (-780893021 : ℤ), (1113898777 : ℤ), (1113898780 : ℤ), (14742532749 : ℤ), (14742532752 : ℤ)⟩, (1 : ℤ), (0 : ℤ), .second⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (3 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (3 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-21270375 : ℤ), (-21270372 : ℤ), (-8965022 : ℤ), (-8965019 : ℤ), (-3857314 : ℤ), (-3857311 : ℤ), (-2 : ℤ), (2 : ℤ), (7392776 : ℤ), (7392779 : ℤ), (69841341 : ℤ), (69841344 : ℤ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (4 : ℤ), (0 : ℤ), (0 : ℤ), (4294967296 : ℤ), (-4294967298 : ℤ), (-4294967294 : ℤ), (-2468805989 : ℤ), (-2468805986 : ℤ), (-2 : ℤ), (2 : ℤ), (1245658774 : ℤ), (1245658777 : ℤ), (14721615855 : ℤ), (14721615858 : ℤ)⟩, (0 : ℤ), (-1 : ℤ), .fourth⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (4 : ℤ), (0 : ℤ), (0 : ℤ), (-1 : ℚ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (4 : ℤ), (1 : ℤ), (1 : ℤ), (4294967296 : ℤ), (-4372878130 : ℤ), (-4372878127 : ℤ), (-2210723633 : ℤ), (-2210723630 : ℤ), (-346173569 : ℤ), (-346173566 : ℤ), (1412734224 : ℤ), (1412734227 : ℤ), (14720542449 : ℤ), (14720542452 : ℤ)⟩, (1 : ℤ), (-1 : ℤ), .second⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (4 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-19632019 : ℤ), (-19632016 : ℤ), (-12377422 : ℤ), (-12377419 : ℤ), (-2753645 : ℤ), (-2753642 : ℤ), (-2 : ℤ), (2 : ℤ), (8135115 : ℤ), (8135118 : ℤ), (69769377 : ℤ), (69769380 : ℤ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (4 : ℤ), (2 : ℤ), (2 : ℤ), (4294967296 : ℤ), (-4440828314 : ℤ), (-4440828311 : ℤ), (-1877155618 : ℤ), (-1877155615 : ℤ), (-737049077 : ℤ), (-737049074 : ℤ), (1539065890 : ℤ), (1539065893 : ℤ), (14719468461 : ℤ), (14719468464 : ℤ)⟩, (2 : ℤ), (-1 : ℤ), .second⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (4 : ℤ), (2 : ℤ), (2 : ℤ), (4294967296 : ℤ), (-4440828314 : ℤ), (-4440828311 : ℤ), (-1877155618 : ℤ), (-1877155615 : ℤ), (-737049077 : ℤ), (-737049074 : ℤ), (1539065890 : ℤ), (1539065893 : ℤ), (14719468461 : ℤ), (14719468464 : ℤ)⟩, (2 : ℤ), (0 : ℤ), .second⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (5 : ℤ), (0 : ℤ), (0 : ℤ), (4294967296 : ℤ), (-3959649504 : ℤ), (-3959649501 : ℤ), (-2958056762 : ℤ), (-2958056759 : ℤ), (-2 : ℤ), (2 : ℤ), (1410649110 : ℤ), (1410649113 : ℤ), (14710558498 : ℤ), (14710558501 : ℤ)⟩, (0 : ℤ), (-1 : ℤ), .first⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (5 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (5 : ℤ), (1 : ℤ), (1 : ℤ), (4294967296 : ℤ), (-4102554115 : ℤ), (-4102554112 : ℤ), (-2672998502 : ℤ), (-2672998499 : ℤ), (-278670009 : ℤ), (-278670006 : ℤ), (1548244092 : ℤ), (1548244095 : ℤ), (14709479877 : ℤ), (14709479880 : ℤ)⟩, (1 : ℤ), (-2 : ℤ), .second⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (5 : ℤ), (1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-15136690 : ℤ), (-15136687 : ℤ), (-6149661 : ℤ), (-6149658 : ℤ), (3795726 : ℤ), (3795729 : ℤ), (7710838 : ℤ), (7710841 : ℤ), (69698408 : ℤ), (69698411 : ℤ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (5 : ℤ), (1 : ℤ), (1 : ℤ), (4294967296 : ℤ), (-4102554115 : ℤ), (-4102554112 : ℤ), (-2672998502 : ℤ), (-2672998499 : ℤ), (-278670009 : ℤ), (-278670006 : ℤ), (1548244092 : ℤ), (1548244095 : ℤ), (14709479877 : ℤ), (14709479880 : ℤ)⟩, (1 : ℤ), (0 : ℤ), .first⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (5 : ℤ), (2 : ℤ), (2 : ℤ), (4294967296 : ℤ), (-4208460849 : ℤ), (-4208460846 : ℤ), (-2387003588 : ℤ), (-2387003585 : ℤ), (-567987658 : ℤ), (-567987655 : ℤ), (1658552772 : ℤ), (1658552775 : ℤ), (14708400665 : ℤ), (14708400668 : ℤ)⟩, (2 : ℤ), (-2 : ℤ), .second⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (5 : ℤ), (2 : ℤ), (2 : ℤ), (4294967296 : ℤ), (-4208460849 : ℤ), (-4208460846 : ℤ), (-2387003588 : ℤ), (-2387003585 : ℤ), (-567987658 : ℤ), (-567987655 : ℤ), (1658552772 : ℤ), (1658552775 : ℤ), (14708400665 : ℤ), (14708400668 : ℤ)⟩, (2 : ℤ), (-1 : ℤ), .second⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (5 : ℤ), (2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-18542636 : ℤ), (-18542633 : ℤ), (-12855126 : ℤ), (-12855123 : ℤ), (-4757578 : ℤ), (-4757575 : ℤ), (-2 : ℤ), (2 : ℤ), (9611393 : ℤ), (9611396 : ℤ), (69685352 : ℤ), (69685355 : ℤ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (6 : ℤ), (2 : ℤ), (2 : ℤ), (4294967296 : ℤ), (-3813319481 : ℤ), (-3813319478 : ℤ), (-2983963505 : ℤ), (-2983963502 : ℤ), (-469442317 : ℤ), (-469442314 : ℤ), (1772939398 : ℤ), (1772939401 : ℤ), (14697287246 : ℤ), (14697287249 : ℤ)⟩, (2 : ℤ), (-2 : ℤ), .second⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (6 : ℤ), (2 : ℤ), (2 : ℤ), (4294967296 : ℤ), (-3813319481 : ℤ), (-3813319478 : ℤ), (-2983963505 : ℤ), (-2983963502 : ℤ), (-469442317 : ℤ), (-469442314 : ℤ), (1772939398 : ℤ), (1772939401 : ℤ), (14697287246 : ℤ), (14697287249 : ℤ)⟩, (2 : ℤ), (-1 : ℤ), .first⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (6 : ℤ), (3 : ℤ), (3 : ℤ), (4294967296 : ℤ), (-3994538189 : ℤ), (-3994538186 : ℤ), (-2627246361 : ℤ), (-2627246358 : ℤ), (-728681739 : ℤ), (-728681736 : ℤ), (1857765473 : ℤ), (1857765476 : ℤ), (14696202157 : ℤ), (14696202160 : ℤ)⟩, (3 : ℤ), (-1 : ℤ), .second⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (6 : ℤ), (3 : ℤ), (0 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-14014086 : ℤ), (-14014083 : ℤ), (-6454616 : ℤ), (-6454613 : ℤ), (-2 : ℤ), (2 : ℤ), (10786582 : ℤ), (10786585 : ℤ), (69600742 : ℤ), (69600745 : ℤ)⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (7 : ℤ), (5 : ℤ), (1 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-12352659 : ℤ), (-12352656 : ℤ), (-7309361 : ℤ), (-7309358 : ℤ), (-2420904 : ℤ), (-2420901 : ℤ), (12499298 : ℤ), (12499301 : ℤ), (69502246 : ℤ), (69502249 : ℤ)⟩
  ]

def degreeSevenStageSevenScaledPrefix100Chunk002 :
    List DegreeSevenStageSevenScaledEntry :=
  DegreeSevenStageSevenClassification.scaledEntries
    degreeSevenStageSevenClassificationsPrefix100Chunk002

def degreeSevenStageSevenMultipleRootPrefix100Chunk002 :
    List DegreeSevenStageSevenMultipleRootWitness :=
  DegreeSevenStageSevenClassification.multipleRoots
    degreeSevenStageSevenClassificationsPrefix100Chunk002

def degreeSevenStageSevenScaledCriticalSignPrefix100Chunk002 :
    List DegreeSevenStageSevenScaledCriticalSignWitness :=
  DegreeSevenStageSevenClassification.criticalSigns
    degreeSevenStageSevenClassificationsPrefix100Chunk002

set_option maxHeartbeats 0 in
-- Kernel reduction checks every scaled parent and forbidden interval sign.
theorem degreeSevenStageSevenScaledCriticalSignPrefix100Chunk002_arithmeticValid :
    degreeSevenStageSevenScaledCriticalSignPrefix100Chunk002.Forall
      DegreeSevenStageSevenScaledCriticalSignWitness.ArithmeticValid := by
  decide

theorem degreeSevenStageSevenScaledCriticalSignPrefix100Chunk002_valid :
    degreeSevenStageSevenScaledCriticalSignPrefix100Chunk002.Forall
      (fun witness => witness.toWitness.Valid) := by
  exact degreeSevenStageSevenScaledCriticalSignPrefix100Chunk002_arithmeticValid.imp
    DegreeSevenStageSevenScaledCriticalSignWitness.valid_of_arithmeticValid

def degreeSevenStageSevenCriticalSignPrefix100Chunk002 :
    List DegreeSevenStageSevenCriticalSignWitness :=
  degreeSevenStageSevenScaledCriticalSignPrefix100Chunk002.map
    DegreeSevenStageSevenScaledCriticalSignWitness.toWitness

theorem degreeSevenStageSevenCriticalSignPrefix100Chunk002_valid :
    degreeSevenStageSevenCriticalSignPrefix100Chunk002.Forall
      DegreeSevenStageSevenCriticalSignWitness.Valid := by
  rw [degreeSevenStageSevenCriticalSignPrefix100Chunk002, List.forall_map_iff]
  change degreeSevenStageSevenScaledCriticalSignPrefix100Chunk002.Forall
    (fun witness => witness.toWitness.Valid)
  exact degreeSevenStageSevenScaledCriticalSignPrefix100Chunk002_valid


theorem degreeSevenStageSevenScaledPrefix100Chunk002_arithmeticValid :
    degreeSevenStageSevenScaledPrefix100Chunk002.Forall
      DegreeSevenStageSevenScaledEntry.ArithmeticValid := by
  decide

theorem degreeSevenStageSevenScaledPrefix100Chunk002_valid :
    degreeSevenStageSevenScaledPrefix100Chunk002.Forall
      (fun entry => entry.toEntry.Valid) := by
  exact degreeSevenStageSevenScaledPrefix100Chunk002_arithmeticValid.imp
    DegreeSevenStageSevenScaledEntry.valid_of_arithmeticValid

theorem degreeSevenStageSevenMultipleRootPrefix100Chunk002_valid :
    degreeSevenStageSevenMultipleRootPrefix100Chunk002.Forall
      DegreeSevenStageSevenMultipleRootWitness.Valid := by
  norm_num [degreeSevenStageSevenMultipleRootPrefix100Chunk002,
    degreeSevenStageSevenClassificationsPrefix100Chunk002,
    DegreeSevenStageSevenClassification.multipleRoots,
    DegreeSevenStageSevenMultipleRootWitness.Valid,
    DegreeSevenStageSevenMultipleRootWitness.coefficients,
    integerPolynomialRationalEval,
    DensePolynomial.derivative, DensePolynomial.add,
    DensePolynomial.eval]

theorem degreeSevenStageSevenClassificationsPrefix100Chunk002_valid :
    degreeSevenStageSevenClassificationsPrefix100Chunk002.Forall
      DegreeSevenStageSevenClassification.Valid := by
  apply DegreeSevenStageSevenClassification.forall_valid_of_projections
  · exact degreeSevenStageSevenScaledPrefix100Chunk002_valid
  · exact degreeSevenStageSevenMultipleRootPrefix100Chunk002_valid
  · exact degreeSevenStageSevenScaledCriticalSignPrefix100Chunk002_valid

/-- Every Hunter candidate matching a certified pilot row has its constant
coefficient in that row's exact final finite set. -/
theorem degreeSevenStageSevenPrefix100Chunk002_a0_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (entry : DegreeSevenStageSevenScaledEntry)
    (hentry : entry ∈ degreeSevenStageSevenScaledPrefix100Chunk002)
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
      degreeSevenStageSevenScaledPrefix100Chunk002_valid) entry hentry
  · exact ha6
  · exact ha5
  · exact ha4
  · exact ha3
  · exact ha2
  · exact ha1

end

end TraceEuclidean
