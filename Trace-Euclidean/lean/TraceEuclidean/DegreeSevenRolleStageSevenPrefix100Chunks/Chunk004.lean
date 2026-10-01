import TraceEuclidean.DegreeSevenRolleStageSevenPrefixBridge

/-! Prefix100Chunk004 data for exact six-root Stage Seven certificates. -/

namespace TraceEuclidean

noncomputable section

open Polynomial

set_option maxRecDepth 100000

def degreeSevenStageSevenClassificationsPrefix100Chunk004 :
    List DegreeSevenStageSevenClassification :=
  [
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (7 : ℤ), (1 : ℤ), (1 : ℤ), (4294967296 : ℤ), (-4064318310 : ℤ), (-4064318307 : ℤ), (-3034734041 : ℤ), (-3034734038 : ℤ), (-203678057 : ℤ), (-203678054 : ℤ), (1896160462 : ℤ), (1896160465 : ℤ), (14610071286 : ℤ), (14610071289 : ℤ)⟩, (1 : ℤ), (-2 : ℤ), .first⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (7 : ℤ), (2 : ℤ), (2 : ℤ), (4294967296 : ℤ), (-4195440532 : ℤ), (-4195440529 : ℤ), (-2776197316 : ℤ), (-2776197313 : ℤ), (-413256291 : ℤ), (-413256288 : ℤ), (1979445947 : ℤ), (1979445950 : ℤ), (14608949532 : ℤ), (14608949535 : ℤ)⟩, (2 : ℤ), (-2 : ℤ), .second⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (7 : ℤ), (2 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-15966420 : ℤ), (-15966417 : ℤ), (-6494528 : ℤ), (-6494525 : ℤ), (2453784 : ℤ), (2453787 : ℤ), (10795459 : ℤ), (10795462 : ℤ), (69130325 : ℤ), (69130328 : ℤ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (7 : ℤ), (3 : ℤ), (3 : ℤ), (4294967296 : ℤ), (-4294967298 : ℤ), (-4294967294 : ℤ), (-2520384018 : ℤ), (-2520384015 : ℤ), (-642855975 : ℤ), (-642855972 : ℤ), (2053881499 : ℤ), (2053881502 : ℤ), (14607827133 : ℤ), (14607827136 : ℤ)⟩, (3 : ℤ), (-1 : ℤ), .second⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (7 : ℤ), (3 : ℤ), (0 : ℤ), (16777216 : ℤ), (-18814627 : ℤ), (-18814624 : ℤ), (-13392871 : ℤ), (-13392868 : ℤ), (-5551552 : ℤ), (-5551549 : ℤ), (-2 : ℤ), (2 : ℤ), (11783832 : ℤ), (11783835 : ℤ), (69116624 : ℤ), (69116627 : ℤ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (7 : ℤ), (4 : ℤ), (4 : ℤ), (4294967296 : ℤ), (-4377175016 : ℤ), (-4377175013 : ℤ), (-2225393806 : ℤ), (-2225393803 : ℤ), (-922207853 : ℤ), (-922207850 : ℤ), (2121573929 : ℤ), (2121573932 : ℤ), (14606704087 : ℤ), (14606704090 : ℤ)⟩, (4 : ℤ), (0 : ℤ), .second⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (7 : ℤ), (4 : ℤ), (4 : ℤ), (4294967296 : ℤ), (-4377175016 : ℤ), (-4377175013 : ℤ), (-2225393806 : ℤ), (-2225393803 : ℤ), (-922207853 : ℤ), (-922207850 : ℤ), (2121573929 : ℤ), (2121573932 : ℤ), (14606704087 : ℤ), (14606704090 : ℤ)⟩, (4 : ℤ), (1 : ℤ), .third⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (7 : ℤ), (5 : ℤ), (5 : ℤ), (4294967296 : ℤ), (-4448112462 : ℤ), (-4448112459 : ℤ), (-1663930939 : ℤ), (-1663930936 : ℤ), (-1473953623 : ℤ), (-1473953620 : ℤ), (2183917971 : ℤ), (2183917974 : ℤ), (14605580393 : ℤ), (14605580396 : ℤ)⟩, (5 : ℤ), (1 : ℤ), .second⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (7 : ℤ), (5 : ℤ), (5 : ℤ), (4294967296 : ℤ), (-4448112462 : ℤ), (-4448112459 : ℤ), (-1663930939 : ℤ), (-1663930936 : ℤ), (-1473953623 : ℤ), (-1473953620 : ℤ), (2183917971 : ℤ), (2183917974 : ℤ), (14605580393 : ℤ), (14605580396 : ℤ)⟩, (5 : ℤ), (2 : ℤ), .third⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (8 : ℤ), (3 : ℤ), (3 : ℤ), (4294967296 : ℤ), (-3919384708 : ℤ), (-3919384705 : ℤ), (-3076191600 : ℤ), (-3076191597 : ℤ), (-550881585 : ℤ), (-550881582 : ℤ), (2153612512 : ℤ), (2153612515 : ℤ), (14596346722 : ℤ), (14596346725 : ℤ)⟩, (3 : ℤ), (-3 : ℤ), .second⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (8 : ℤ), (3 : ℤ), (3 : ℤ), (4294967296 : ℤ), (-3919384708 : ℤ), (-3919384705 : ℤ), (-3076191600 : ℤ), (-3076191597 : ℤ), (-550881585 : ℤ), (-550881582 : ℤ), (2153612512 : ℤ), (2153612515 : ℤ), (14596346722 : ℤ), (14596346725 : ℤ)⟩, (3 : ℤ), (-2 : ℤ), .second⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (8 : ℤ), (3 : ℤ), (3 : ℤ), (4294967296 : ℤ), (-3919384708 : ℤ), (-3919384705 : ℤ), (-3076191600 : ℤ), (-3076191597 : ℤ), (-550881585 : ℤ), (-550881582 : ℤ), (2153612512 : ℤ), (2153612515 : ℤ), (14596346722 : ℤ), (14596346725 : ℤ)⟩, (3 : ℤ), (-1 : ℤ), .first⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (8 : ℤ), (4 : ℤ), (4 : ℤ), (4294967296 : ℤ), (-4086502773 : ℤ), (-4086502770 : ℤ), (-2757679803 : ℤ), (-2757679800 : ℤ), (-763711386 : ℤ), (-763711383 : ℤ), (2216177382 : ℤ), (2216177385 : ℤ), (14595217921 : ℤ), (14595217924 : ℤ)⟩, (4 : ℤ), (-1 : ℤ), .second⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (8 : ℤ), (4 : ℤ), (0 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-14971535 : ℤ), (-14971532 : ℤ), (-6877560 : ℤ), (-6877557 : ℤ), (-2 : ℤ), (2 : ℤ), (12739207 : ℤ), (12739210 : ℤ), (69028510 : ℤ), (69028513 : ℤ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (8 : ℤ), (5 : ℤ), (5 : ℤ), (4294967296 : ℤ), (-4202585076 : ℤ), (-4202585073 : ℤ), (-2439758923 : ℤ), (-2439758920 : ℤ), (-1022511012 : ℤ), (-1022511009 : ℤ), (2274267887 : ℤ), (2274267890 : ℤ), (14594088465 : ℤ), (14594088468 : ℤ)⟩, (5 : ℤ), (0 : ℤ), .second⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (8 : ℤ), (5 : ℤ), (1 : ℤ), (16777216 : ℤ), (-18577036 : ℤ), (-18577033 : ℤ), (-12462833 : ℤ), (-12462830 : ℤ), (-5508503 : ℤ), (-5508500 : ℤ), (-2705138 : ℤ), (-2705135 : ℤ), (13380245 : ℤ), (13380248 : ℤ), (69014669 : ℤ), (69014672 : ℤ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (8 : ℤ), (6 : ℤ), (6 : ℤ), (4294967296 : ℤ), (-4294967298 : ℤ), (-4294967294 : ℤ), (-1973073343 : ℤ), (-1973073340 : ℤ), (-1450051412 : ℤ), (-1450051409 : ℤ), (2328635041 : ℤ), (2328635044 : ℤ), (14592958353 : ℤ), (14592958356 : ℤ)⟩, (6 : ℤ), (1 : ℤ), .second⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (8 : ℤ), (6 : ℤ), (6 : ℤ), (4294967296 : ℤ), (-4294967298 : ℤ), (-4294967294 : ℤ), (-1973073343 : ℤ), (-1973073340 : ℤ), (-1450051412 : ℤ), (-1450051409 : ℤ), (2328635041 : ℤ), (2328635044 : ℤ), (14592958353 : ℤ), (14592958356 : ℤ)⟩, (6 : ℤ), (2 : ℤ), .third⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (9 : ℤ), (6 : ℤ), (6 : ℤ), (4294967296 : ℤ), (-3965763112 : ℤ), (-3965763109 : ℤ), (-2729144488 : ℤ), (-2729144485 : ℤ), (-1096365946 : ℤ), (-1096365943 : ℤ), (2413364328 : ℤ), (2413364331 : ℤ), (14581410559 : ℤ), (14581410562 : ℤ)⟩, (6 : ℤ), (0 : ℤ), .second⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (9 : ℤ), (6 : ℤ), (1 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-13606318 : ℤ), (-13606315 : ℤ), (-7688668 : ℤ), (-7688665 : ℤ), (-1861233 : ℤ), (-1861230 : ℤ), (14149064 : ℤ), (14149067 : ℤ), (68925776 : ℤ), (68925779 : ℤ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (9 : ℤ), (7 : ℤ), (7 : ℤ), (4294967296 : ℤ), (-4103972744 : ℤ), (-4103972741 : ℤ), (-2290874735 : ℤ), (-2290874732 : ℤ), (-1443660746 : ℤ), (-1443660743 : ℤ), (2461735621 : ℤ), (2461735624 : ℤ), (14580273945 : ℤ), (14580273948 : ℤ)⟩, (7 : ℤ), (1 : ℤ), .second⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (9 : ℤ), (7 : ℤ), (7 : ℤ), (4294967296 : ℤ), (-4103972744 : ℤ), (-4103972741 : ℤ), (-2290874735 : ℤ), (-2290874732 : ℤ), (-1443660746 : ℤ), (-1443660743 : ℤ), (2461735621 : ℤ), (2461735624 : ℤ), (14580273945 : ℤ), (14580273948 : ℤ)⟩, (7 : ℤ), (2 : ℤ), .third⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (2 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (3 : ℤ), (-1 : ℤ), (-1 : ℤ), (4294967296 : ℤ), (-5098702156 : ℤ), (-5098702153 : ℤ), (-1761345364 : ℤ), (-1761345361 : ℤ), (605463014 : ℤ), (605463017 : ℤ), (877857238 : ℤ), (877857241 : ℤ), (14580228609 : ℤ), (14580228612 : ℤ)⟩, (-1 : ℤ), (0 : ℤ), .fourth⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (3 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (3 : ℤ), (1 : ℤ), (1 : ℤ), (4294967296 : ℤ), (-5158367054 : ℤ), (-5158367051 : ℤ), (-1107922496 : ℤ), (-1107922493 : ℤ), (-571031455 : ℤ), (-571031452 : ℤ), (1462855392 : ℤ), (1462855395 : ℤ), (14577966954 : ℤ), (14577966957 : ℤ)⟩, (1 : ℤ), (0 : ℤ), .second⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (4 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-23004265 : ℤ), (-23004262 : ℤ), (-12107066 : ℤ), (-12107063 : ℤ), (-2 : ℤ), (2 : ℤ), (3318759 : ℤ), (3318762 : ℤ), (5956646 : ℤ), (5956649 : ℤ), (68977332 : ℤ), (68977335 : ℤ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (4 : ℤ), (0 : ℤ), (0 : ℤ), (4294967296 : ℤ), (-5016254648 : ℤ), (-5016254645 : ℤ), (-1814382806 : ℤ), (-1814382803 : ℤ), (-2 : ℤ), (2 : ℤ), (1466581358 : ℤ), (1466581361 : ℤ), (14567557438 : ℤ), (14567557441 : ℤ)⟩, (0 : ℤ), (-1 : ℤ), .second⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (4 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (4 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-23862876 : ℤ), (-23862873 : ℤ), (-7898556 : ℤ), (-7898553 : ℤ), (-3195263 : ℤ), (-3195260 : ℤ), (-2 : ℤ), (2 : ℤ), (9145414 : ℤ), (9145417 : ℤ), (68952686 : ℤ), (68952689 : ℤ)⟩
  ]

def degreeSevenStageSevenScaledPrefix100Chunk004 :
    List DegreeSevenStageSevenScaledEntry :=
  DegreeSevenStageSevenClassification.scaledEntries
    degreeSevenStageSevenClassificationsPrefix100Chunk004

def degreeSevenStageSevenMultipleRootPrefix100Chunk004 :
    List DegreeSevenStageSevenMultipleRootWitness :=
  DegreeSevenStageSevenClassification.multipleRoots
    degreeSevenStageSevenClassificationsPrefix100Chunk004

def degreeSevenStageSevenScaledCriticalSignPrefix100Chunk004 :
    List DegreeSevenStageSevenScaledCriticalSignWitness :=
  DegreeSevenStageSevenClassification.criticalSigns
    degreeSevenStageSevenClassificationsPrefix100Chunk004

set_option maxHeartbeats 0 in
-- Kernel reduction checks every scaled parent and forbidden interval sign.
theorem degreeSevenStageSevenScaledCriticalSignPrefix100Chunk004_arithmeticValid :
    degreeSevenStageSevenScaledCriticalSignPrefix100Chunk004.Forall
      DegreeSevenStageSevenScaledCriticalSignWitness.ArithmeticValid := by
  decide

theorem degreeSevenStageSevenScaledCriticalSignPrefix100Chunk004_valid :
    degreeSevenStageSevenScaledCriticalSignPrefix100Chunk004.Forall
      (fun witness => witness.toWitness.Valid) := by
  exact degreeSevenStageSevenScaledCriticalSignPrefix100Chunk004_arithmeticValid.imp
    DegreeSevenStageSevenScaledCriticalSignWitness.valid_of_arithmeticValid

def degreeSevenStageSevenCriticalSignPrefix100Chunk004 :
    List DegreeSevenStageSevenCriticalSignWitness :=
  degreeSevenStageSevenScaledCriticalSignPrefix100Chunk004.map
    DegreeSevenStageSevenScaledCriticalSignWitness.toWitness

theorem degreeSevenStageSevenCriticalSignPrefix100Chunk004_valid :
    degreeSevenStageSevenCriticalSignPrefix100Chunk004.Forall
      DegreeSevenStageSevenCriticalSignWitness.Valid := by
  rw [degreeSevenStageSevenCriticalSignPrefix100Chunk004, List.forall_map_iff]
  change degreeSevenStageSevenScaledCriticalSignPrefix100Chunk004.Forall
    (fun witness => witness.toWitness.Valid)
  exact degreeSevenStageSevenScaledCriticalSignPrefix100Chunk004_valid


theorem degreeSevenStageSevenScaledPrefix100Chunk004_arithmeticValid :
    degreeSevenStageSevenScaledPrefix100Chunk004.Forall
      DegreeSevenStageSevenScaledEntry.ArithmeticValid := by
  decide

theorem degreeSevenStageSevenScaledPrefix100Chunk004_valid :
    degreeSevenStageSevenScaledPrefix100Chunk004.Forall
      (fun entry => entry.toEntry.Valid) := by
  exact degreeSevenStageSevenScaledPrefix100Chunk004_arithmeticValid.imp
    DegreeSevenStageSevenScaledEntry.valid_of_arithmeticValid

theorem degreeSevenStageSevenMultipleRootPrefix100Chunk004_valid :
    degreeSevenStageSevenMultipleRootPrefix100Chunk004.Forall
      DegreeSevenStageSevenMultipleRootWitness.Valid := by
  norm_num [degreeSevenStageSevenMultipleRootPrefix100Chunk004,
    degreeSevenStageSevenClassificationsPrefix100Chunk004,
    DegreeSevenStageSevenClassification.multipleRoots,
    DegreeSevenStageSevenMultipleRootWitness.Valid,
    DegreeSevenStageSevenMultipleRootWitness.coefficients,
    integerPolynomialRationalEval,
    DensePolynomial.derivative, DensePolynomial.add,
    DensePolynomial.eval]

theorem degreeSevenStageSevenClassificationsPrefix100Chunk004_valid :
    degreeSevenStageSevenClassificationsPrefix100Chunk004.Forall
      DegreeSevenStageSevenClassification.Valid := by
  apply DegreeSevenStageSevenClassification.forall_valid_of_projections
  · exact degreeSevenStageSevenScaledPrefix100Chunk004_valid
  · exact degreeSevenStageSevenMultipleRootPrefix100Chunk004_valid
  · exact degreeSevenStageSevenScaledCriticalSignPrefix100Chunk004_valid

/-- Every Hunter candidate matching a certified pilot row has its constant
coefficient in that row's exact final finite set. -/
theorem degreeSevenStageSevenPrefix100Chunk004_a0_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (entry : DegreeSevenStageSevenScaledEntry)
    (hentry : entry ∈ degreeSevenStageSevenScaledPrefix100Chunk004)
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
      degreeSevenStageSevenScaledPrefix100Chunk004_valid) entry hentry
  · exact ha6
  · exact ha5
  · exact ha4
  · exact ha3
  · exact ha2
  · exact ha1

end

end TraceEuclidean
