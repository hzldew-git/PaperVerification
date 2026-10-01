import TraceEuclidean.DegreeSevenRolleStageSevenPrefixBridge

/-! Rows100To199Chunk002 data for exact six-root Stage Seven certificates. -/

namespace TraceEuclidean

noncomputable section

open Polynomial

set_option maxRecDepth 100000

def degreeSevenStageSevenClassificationsRows100To199Chunk002 :
    List DegreeSevenStageSevenClassification :=
  [
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (2 : ℤ), (-1 : ℤ), (-1 : ℤ), (4294967296 : ℤ), (-5995792788 : ℤ), (-5995792785 : ℤ), (-1025933337 : ℤ), (-1025933334 : ℤ), (572664659 : ℤ), (572664662 : ℤ), (1384697365 : ℤ), (1384697368 : ℤ), (14267865442 : ℤ), (14267865445 : ℤ)⟩, (-1 : ℤ), (0 : ℤ), .fourth⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (2 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (3 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-28544891 : ℤ), (-28544888 : ℤ), (-7252338 : ℤ), (-7252335 : ℤ), (-2 : ℤ), (2 : ℤ), (3261665 : ℤ), (3261668 : ℤ), (8354609 : ℤ), (8354612 : ℤ), (67322360 : ℤ), (67322363 : ℤ)⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (3 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (4 : ℤ), (-3 : ℤ), (-3 : ℤ), (4294967296 : ℤ), (-5838022851 : ℤ), (-5838022848 : ℤ), (-1665255564 : ℤ), (-1665255561 : ℤ), (1144127357 : ℤ), (1144127360 : ℤ), (1317708905 : ℤ), (1317708908 : ℤ), (14244943495 : ℤ), (14244943498 : ℤ)⟩, (-3 : ℤ), (1 : ℤ), .third⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (4 : ℤ), (-2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-27950200 : ℤ), (-27950197 : ℤ), (-9371938 : ℤ), (-9371935 : ℤ), (-2 : ℤ), (2 : ℤ), (5883237 : ℤ), (5883240 : ℤ), (7328720 : ℤ), (7328723 : ℤ), (67251586 : ℤ), (67251589 : ℤ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (4 : ℤ), (-2 : ℤ), (-2 : ℤ), (4294967296 : ℤ), (-5854489194 : ℤ), (-5854489191 : ℤ), (-1530838649 : ℤ), (-1530838646 : ℤ), (639109045 : ℤ), (639109048 : ℤ), (1706063179 : ℤ), (1706063182 : ℤ), (14243656961 : ℤ), (14243656964 : ℤ)⟩, (-2 : ℤ), (1 : ℤ), .third⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (4 : ℤ), (-1 : ℤ), (-1 : ℤ), (4294967296 : ℤ), (-5870653515 : ℤ), (-5870653512 : ℤ), (-1370011103 : ℤ), (-1370011100 : ℤ), (323453939 : ℤ), (323453942 : ℤ), (1878342476 : ℤ), (1878342479 : ℤ), (14242369544 : ℤ), (14242369547 : ℤ)⟩, (-1 : ℤ), (-1 : ℤ), .second⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (4 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-28126278 : ℤ), (-28126275 : ℤ), (-8207445 : ℤ), (-8207442 : ℤ), (-2 : ℤ), (2 : ℤ), (2517146 : ℤ), (2517149 : ℤ), (9720565 : ℤ), (9720568 : ℤ), (67237417 : ℤ), (67237420 : ℤ)⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (4 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (5 : ℤ), (-3 : ℤ), (-3 : ℤ), (4294967296 : ℤ), (-5768306917 : ℤ), (-5768306914 : ℤ), (-1812538402 : ℤ), (-1812538399 : ℤ), (801408291 : ℤ), (801408294 : ℤ), (1750823730 : ℤ), (1750823733 : ℤ), (14232114640 : ℤ), (14232114643 : ℤ)⟩, (-3 : ℤ), (0 : ℤ), .fourth⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (5 : ℤ), (-3 : ℤ), (-3 : ℤ), (4294967296 : ℤ), (-5768306917 : ℤ), (-5768306914 : ℤ), (-1812538402 : ℤ), (-1812538399 : ℤ), (801408291 : ℤ), (801408294 : ℤ), (1750823730 : ℤ), (1750823733 : ℤ), (14232114640 : ℤ), (14232114643 : ℤ)⟩, (-3 : ℤ), (1 : ℤ), .third⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (5 : ℤ), (-2 : ℤ), (-2 : ℤ), (4294967296 : ℤ), (-5785930836 : ℤ), (-5785930833 : ℤ), (-1687345409 : ℤ), (-1687345406 : ℤ), (520250827 : ℤ), (520250830 : ℤ), (1925706323 : ℤ), (1925706326 : ℤ), (14230820437 : ℤ), (14230820440 : ℤ)⟩, (-2 : ℤ), (-1 : ℤ), .fourth⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (5 : ℤ), (-2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-27481901 : ℤ), (-27481898 : ℤ), (-10266874 : ℤ), (-10266871 : ℤ), (-2 : ℤ), (2 : ℤ), (4214865 : ℤ), (4214868 : ℤ), (9509159 : ℤ), (9509162 : ℤ), (67166156 : ℤ), (67166159 : ℤ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (5 : ℤ), (-2 : ℤ), (-2 : ℤ), (4294967296 : ℤ), (-5785930836 : ℤ), (-5785930833 : ℤ), (-1687345409 : ℤ), (-1687345406 : ℤ), (520250827 : ℤ), (520250830 : ℤ), (1925706323 : ℤ), (1925706326 : ℤ), (14230820437 : ℤ), (14230820440 : ℤ)⟩, (-2 : ℤ), (1 : ℤ), .third⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (5 : ℤ), (-1 : ℤ), (-1 : ℤ), (4294967296 : ℤ), (-5803200330 : ℤ), (-5803200327 : ℤ), (-1541957000 : ℤ), (-1541956997 : ℤ), (266247101 : ℤ), (266247104 : ℤ), (2052886230 : ℤ), (2052886233 : ℤ), (14229525340 : ℤ), (14229525343 : ℤ)⟩, (-1 : ℤ), (-2 : ℤ), .second⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (5 : ℤ), (-1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-27732732 : ℤ), (-27732729 : ℤ), (-7614827 : ℤ), (-7614824 : ℤ), (-4069166 : ℤ), (-4069163 : ℤ), (5673070 : ℤ), (5673073 : ℤ), (9731405 : ℤ), (9731408 : ℤ), (67153654 : ℤ), (67153657 : ℤ)⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (5 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-27675866 : ℤ), (-27675863 : ℤ), (-9181268 : ℤ), (-9181265 : ℤ), (-2 : ℤ), (2 : ℤ), (2064194 : ℤ), (2064197 : ℤ), (10782478 : ℤ), (10782481 : ℤ), (67151868 : ℤ), (67151871 : ℤ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (5 : ℤ), (0 : ℤ), (0 : ℤ), (4294967296 : ℤ), (-5820132558 : ℤ), (-5820132555 : ℤ), (-1361075527 : ℤ), (-1361075524 : ℤ), (-2 : ℤ), (2 : ℤ), (2156480082 : ℤ), (2156480085 : ℤ), (14228229346 : ℤ), (14228229349 : ℤ)⟩, (0 : ℤ), (-1 : ℤ), .second⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (5 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (5 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-28037981 : ℤ), (-28037978 : ℤ), (-5061659 : ℤ), (-5061656 : ℤ), (-3228977 : ℤ), (-3228974 : ℤ), (-2 : ℤ), (2 : ℤ), (12346800 : ℤ), (12346803 : ℤ), (67123221 : ℤ), (67123224 : ℤ)⟩
  ]

def degreeSevenStageSevenScaledRows100To199Chunk002 :
    List DegreeSevenStageSevenScaledEntry :=
  DegreeSevenStageSevenClassification.scaledEntries
    degreeSevenStageSevenClassificationsRows100To199Chunk002

def degreeSevenStageSevenMultipleRootRows100To199Chunk002 :
    List DegreeSevenStageSevenMultipleRootWitness :=
  DegreeSevenStageSevenClassification.multipleRoots
    degreeSevenStageSevenClassificationsRows100To199Chunk002

def degreeSevenStageSevenScaledCriticalSignRows100To199Chunk002 :
    List DegreeSevenStageSevenScaledCriticalSignWitness :=
  DegreeSevenStageSevenClassification.criticalSigns
    degreeSevenStageSevenClassificationsRows100To199Chunk002

set_option maxHeartbeats 0 in
-- Kernel reduction checks every scaled parent and forbidden interval sign.
theorem degreeSevenStageSevenScaledCriticalSignRows100To199Chunk002_arithmeticValid :
    degreeSevenStageSevenScaledCriticalSignRows100To199Chunk002.Forall
      DegreeSevenStageSevenScaledCriticalSignWitness.ArithmeticValid := by
  decide

theorem degreeSevenStageSevenScaledCriticalSignRows100To199Chunk002_valid :
    degreeSevenStageSevenScaledCriticalSignRows100To199Chunk002.Forall
      (fun witness => witness.toWitness.Valid) := by
  exact degreeSevenStageSevenScaledCriticalSignRows100To199Chunk002_arithmeticValid.imp
    DegreeSevenStageSevenScaledCriticalSignWitness.valid_of_arithmeticValid

def degreeSevenStageSevenCriticalSignRows100To199Chunk002 :
    List DegreeSevenStageSevenCriticalSignWitness :=
  degreeSevenStageSevenScaledCriticalSignRows100To199Chunk002.map
    DegreeSevenStageSevenScaledCriticalSignWitness.toWitness

theorem degreeSevenStageSevenCriticalSignRows100To199Chunk002_valid :
    degreeSevenStageSevenCriticalSignRows100To199Chunk002.Forall
      DegreeSevenStageSevenCriticalSignWitness.Valid := by
  rw [degreeSevenStageSevenCriticalSignRows100To199Chunk002, List.forall_map_iff]
  change degreeSevenStageSevenScaledCriticalSignRows100To199Chunk002.Forall
    (fun witness => witness.toWitness.Valid)
  exact degreeSevenStageSevenScaledCriticalSignRows100To199Chunk002_valid


theorem degreeSevenStageSevenScaledRows100To199Chunk002_arithmeticValid :
    degreeSevenStageSevenScaledRows100To199Chunk002.Forall
      DegreeSevenStageSevenScaledEntry.ArithmeticValid := by
  decide

theorem degreeSevenStageSevenScaledRows100To199Chunk002_valid :
    degreeSevenStageSevenScaledRows100To199Chunk002.Forall
      (fun entry => entry.toEntry.Valid) := by
  exact degreeSevenStageSevenScaledRows100To199Chunk002_arithmeticValid.imp
    DegreeSevenStageSevenScaledEntry.valid_of_arithmeticValid

theorem degreeSevenStageSevenMultipleRootRows100To199Chunk002_valid :
    degreeSevenStageSevenMultipleRootRows100To199Chunk002.Forall
      DegreeSevenStageSevenMultipleRootWitness.Valid := by
  norm_num [degreeSevenStageSevenMultipleRootRows100To199Chunk002,
    degreeSevenStageSevenClassificationsRows100To199Chunk002,
    DegreeSevenStageSevenClassification.multipleRoots,
    DegreeSevenStageSevenMultipleRootWitness.Valid,
    DegreeSevenStageSevenMultipleRootWitness.coefficients,
    integerPolynomialRationalEval,
    DensePolynomial.derivative, DensePolynomial.add,
    DensePolynomial.eval]

theorem degreeSevenStageSevenClassificationsRows100To199Chunk002_valid :
    degreeSevenStageSevenClassificationsRows100To199Chunk002.Forall
      DegreeSevenStageSevenClassification.Valid := by
  apply DegreeSevenStageSevenClassification.forall_valid_of_projections
  · exact degreeSevenStageSevenScaledRows100To199Chunk002_valid
  · exact degreeSevenStageSevenMultipleRootRows100To199Chunk002_valid
  · exact degreeSevenStageSevenScaledCriticalSignRows100To199Chunk002_valid

/-- Every Hunter candidate matching a certified pilot row has its constant
coefficient in that row's exact final finite set. -/
theorem degreeSevenStageSevenRows100To199Chunk002_a0_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (entry : DegreeSevenStageSevenScaledEntry)
    (hentry : entry ∈ degreeSevenStageSevenScaledRows100To199Chunk002)
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
      degreeSevenStageSevenScaledRows100To199Chunk002_valid) entry hentry
  · exact ha6
  · exact ha5
  · exact ha4
  · exact ha3
  · exact ha2
  · exact ha1

end

end TraceEuclidean
