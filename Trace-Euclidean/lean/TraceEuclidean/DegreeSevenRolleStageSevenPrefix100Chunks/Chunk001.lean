import TraceEuclidean.DegreeSevenRolleStageSevenPrefixBridge

/-! Prefix100Chunk001 data for exact six-root Stage Seven certificates. -/

namespace TraceEuclidean

noncomputable section

open Polynomial

set_option maxRecDepth 100000

def degreeSevenStageSevenClassificationsPrefix100Chunk001 :
    List DegreeSevenStageSevenClassification :=
  [
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (-4 : ℤ), (2 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-12115498 : ℤ), (-12115495 : ℤ), (-4513188 : ℤ), (-4513185 : ℤ), (-2 : ℤ), (2 : ℤ), (5856291 : ℤ), (5856294 : ℤ), (70691018 : ℤ), (70691021 : ℤ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-4 : ℤ), (3 : ℤ), (2 : ℤ), (2 : ℤ), (4294967296 : ℤ), (-3513664950 : ℤ), (-3513664947 : ℤ), (-2617649088 : ℤ), (-2617649085 : ℤ), (-805974046 : ℤ), (-805974043 : ℤ), (1261968966 : ℤ), (1261968969 : ℤ), (14878820460 : ℤ), (14878820463 : ℤ)⟩, (2 : ℤ), (-1 : ℤ), .second⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-4 : ℤ), (3 : ℤ), (2 : ℤ), (2 : ℤ), (4294967296 : ℤ), (-3513664950 : ℤ), (-3513664947 : ℤ), (-2617649088 : ℤ), (-2617649085 : ℤ), (-805974046 : ℤ), (-805974043 : ℤ), (1261968966 : ℤ), (1261968969 : ℤ), (14878820460 : ℤ), (14878820463 : ℤ)⟩, (2 : ℤ), (0 : ℤ), .first⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-4 : ℤ), (3 : ℤ), (3 : ℤ), (3 : ℤ), (4294967296 : ℤ), (-3740445920 : ℤ), (-3740445917 : ℤ), (-1845294105 : ℤ), (-1845294102 : ℤ), (-1470862743 : ℤ), (-1470862740 : ℤ), (1382296494 : ℤ), (1382296497 : ℤ), (14877807615 : ℤ), (14877807618 : ℤ)⟩, (3 : ℤ), (0 : ℤ), .second⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-4 : ℤ), (3 : ℤ), (3 : ℤ), (3 : ℤ), (4294967296 : ℤ), (-3740445920 : ℤ), (-3740445917 : ℤ), (-1845294105 : ℤ), (-1845294102 : ℤ), (-1470862743 : ℤ), (-1470862740 : ℤ), (1382296494 : ℤ), (1382296497 : ℤ), (14877807615 : ℤ), (14877807618 : ℤ)⟩, (3 : ℤ), (1 : ℤ), .third⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (-3 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (-3 : ℤ), (2 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-3 : ℤ), (2 : ℤ), (1 : ℤ), (1 : ℤ), (4294967296 : ℤ), (-4365573485 : ℤ), (-4365573482 : ℤ), (-1658278267 : ℤ), (-1658278264 : ℤ), (-626056433 : ℤ), (-626056430 : ℤ), (1036348308 : ℤ), (1036348311 : ℤ), (14817061217 : ℤ), (14817061220 : ℤ)⟩, (1 : ℤ), (0 : ℤ), .second⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (-3 : ℤ), (3 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (-3 : ℤ), (3 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-18316088 : ℤ), (-18316085 : ℤ), (-12296434 : ℤ), (-12296431 : ℤ), (-3446957 : ℤ), (-3446954 : ℤ), (-2 : ℤ), (2 : ℤ), (6965065 : ℤ), (6965068 : ℤ), (70235819 : ℤ), (70235822 : ℤ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-3 : ℤ), (3 : ℤ), (2 : ℤ), (2 : ℤ), (4294967296 : ℤ), (-4218305846 : ℤ), (-4218305843 : ℤ), (-1779603296 : ℤ), (-1779603293 : ℤ), (-938424038 : ℤ), (-938424035 : ℤ), (1334543281 : ℤ), (1334543284 : ℤ), (14805291240 : ℤ), (14805291243 : ℤ)⟩, (2 : ℤ), (0 : ℤ), .second⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-3 : ℤ), (4 : ℤ), (1 : ℤ), (1 : ℤ), (4294967296 : ℤ), (-3725166543 : ℤ), (-3725166540 : ℤ), (-2857982900 : ℤ), (-2857982897 : ℤ), (-333540064 : ℤ), (-333540061 : ℤ), (1324632234 : ℤ), (1324632237 : ℤ), (14795558614 : ℤ), (14795558617 : ℤ)⟩, (1 : ℤ), (-1 : ℤ), .first⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-3 : ℤ), (4 : ℤ), (1 : ℤ), (1 : ℤ), (4294967296 : ℤ), (-3725166543 : ℤ), (-3725166540 : ℤ), (-2857982900 : ℤ), (-2857982897 : ℤ), (-333540064 : ℤ), (-333540061 : ℤ), (1324632234 : ℤ), (1324632237 : ℤ), (14795558614 : ℤ), (14795558617 : ℤ)⟩, (1 : ℤ), (0 : ℤ), .first⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-3 : ℤ), (4 : ℤ), (2 : ℤ), (2 : ℤ), (4294967296 : ℤ), (-3913188040 : ℤ), (-3913188037 : ℤ), (-2461867755 : ℤ), (-2461867752 : ℤ), (-671122091 : ℤ), (-671122088 : ℤ), (1455165318 : ℤ), (1455165321 : ℤ), (14794513909 : ℤ), (14794513912 : ℤ)⟩, (2 : ℤ), (-1 : ℤ), .second⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (-3 : ℤ), (4 : ℤ), (2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-13046051 : ℤ), (-13046048 : ℤ), (-5767070 : ℤ), (-5767067 : ℤ), (-2 : ℤ), (2 : ℤ), (8577334 : ℤ), (8577337 : ℤ), (70154409 : ℤ), (70154412 : ℤ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-3 : ℤ), (4 : ℤ), (3 : ℤ), (3 : ℤ), (4294967296 : ℤ), (-4039709255 : ℤ), (-4039709252 : ℤ), (-1986345393 : ℤ), (-1986345390 : ℤ), (-1125973894 : ℤ), (-1125973891 : ℤ), (1562061227 : ℤ), (1562061230 : ℤ), (14793468656 : ℤ), (14793468659 : ℤ)⟩, (3 : ℤ), (0 : ℤ), .second⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-3 : ℤ), (4 : ℤ), (3 : ℤ), (3 : ℤ), (4294967296 : ℤ), (-4039709255 : ℤ), (-4039709252 : ℤ), (-1986345393 : ℤ), (-1986345390 : ℤ), (-1125973894 : ℤ), (-1125973891 : ℤ), (1562061227 : ℤ), (1562061230 : ℤ), (14793468656 : ℤ), (14793468659 : ℤ)⟩, (3 : ℤ), (1 : ℤ), .third⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-3 : ℤ), (5 : ℤ), (3 : ℤ), (3 : ℤ), (4294967296 : ℤ), (-3558236628 : ℤ), (-3558236625 : ℤ), (-2855694634 : ℤ), (-2855694631 : ℤ), (-833276931 : ℤ), (-833276928 : ℤ), (1668065922 : ℤ), (1668065925 : ℤ), (14782643611 : ℤ), (14782643614 : ℤ)⟩, (3 : ℤ), (-1 : ℤ), .second⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-3 : ℤ), (5 : ℤ), (3 : ℤ), (3 : ℤ), (4294967296 : ℤ), (-3558236628 : ℤ), (-3558236625 : ℤ), (-2855694634 : ℤ), (-2855694631 : ℤ), (-833276931 : ℤ), (-833276928 : ℤ), (1668065922 : ℤ), (1668065925 : ℤ), (14782643611 : ℤ), (14782643614 : ℤ)⟩, (3 : ℤ), (0 : ℤ), .first⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-3 : ℤ), (5 : ℤ), (4 : ℤ), (4 : ℤ), (4294967296 : ℤ), (-3801945287 : ℤ), (-3801945284 : ℤ), (-2299281476 : ℤ), (-2299281473 : ℤ), (-1229334780 : ℤ), (-1229334777 : ℤ), (1752470012 : ℤ), (1752470015 : ℤ), (14781592872 : ℤ), (14781592875 : ℤ)⟩, (4 : ℤ), (0 : ℤ), .second⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (-3 : ℤ), (5 : ℤ), (4 : ℤ), (1 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-11056366 : ℤ), (-11056363 : ℤ), (-6193519 : ℤ), (-6193516 : ℤ), (-3671572 : ℤ), (-3671569 : ℤ), (10780304 : ℤ), (10780307 : ℤ), (70059774 : ℤ), (70059777 : ℤ)⟩
  ]

def degreeSevenStageSevenScaledPrefix100Chunk001 :
    List DegreeSevenStageSevenScaledEntry :=
  DegreeSevenStageSevenClassification.scaledEntries
    degreeSevenStageSevenClassificationsPrefix100Chunk001

def degreeSevenStageSevenMultipleRootPrefix100Chunk001 :
    List DegreeSevenStageSevenMultipleRootWitness :=
  DegreeSevenStageSevenClassification.multipleRoots
    degreeSevenStageSevenClassificationsPrefix100Chunk001

def degreeSevenStageSevenScaledCriticalSignPrefix100Chunk001 :
    List DegreeSevenStageSevenScaledCriticalSignWitness :=
  DegreeSevenStageSevenClassification.criticalSigns
    degreeSevenStageSevenClassificationsPrefix100Chunk001

set_option maxHeartbeats 0 in
-- Kernel reduction checks every scaled parent and forbidden interval sign.
theorem degreeSevenStageSevenScaledCriticalSignPrefix100Chunk001_arithmeticValid :
    degreeSevenStageSevenScaledCriticalSignPrefix100Chunk001.Forall
      DegreeSevenStageSevenScaledCriticalSignWitness.ArithmeticValid := by
  decide

theorem degreeSevenStageSevenScaledCriticalSignPrefix100Chunk001_valid :
    degreeSevenStageSevenScaledCriticalSignPrefix100Chunk001.Forall
      (fun witness => witness.toWitness.Valid) := by
  exact degreeSevenStageSevenScaledCriticalSignPrefix100Chunk001_arithmeticValid.imp
    DegreeSevenStageSevenScaledCriticalSignWitness.valid_of_arithmeticValid

def degreeSevenStageSevenCriticalSignPrefix100Chunk001 :
    List DegreeSevenStageSevenCriticalSignWitness :=
  degreeSevenStageSevenScaledCriticalSignPrefix100Chunk001.map
    DegreeSevenStageSevenScaledCriticalSignWitness.toWitness

theorem degreeSevenStageSevenCriticalSignPrefix100Chunk001_valid :
    degreeSevenStageSevenCriticalSignPrefix100Chunk001.Forall
      DegreeSevenStageSevenCriticalSignWitness.Valid := by
  rw [degreeSevenStageSevenCriticalSignPrefix100Chunk001, List.forall_map_iff]
  change degreeSevenStageSevenScaledCriticalSignPrefix100Chunk001.Forall
    (fun witness => witness.toWitness.Valid)
  exact degreeSevenStageSevenScaledCriticalSignPrefix100Chunk001_valid


theorem degreeSevenStageSevenScaledPrefix100Chunk001_arithmeticValid :
    degreeSevenStageSevenScaledPrefix100Chunk001.Forall
      DegreeSevenStageSevenScaledEntry.ArithmeticValid := by
  decide

theorem degreeSevenStageSevenScaledPrefix100Chunk001_valid :
    degreeSevenStageSevenScaledPrefix100Chunk001.Forall
      (fun entry => entry.toEntry.Valid) := by
  exact degreeSevenStageSevenScaledPrefix100Chunk001_arithmeticValid.imp
    DegreeSevenStageSevenScaledEntry.valid_of_arithmeticValid

theorem degreeSevenStageSevenMultipleRootPrefix100Chunk001_valid :
    degreeSevenStageSevenMultipleRootPrefix100Chunk001.Forall
      DegreeSevenStageSevenMultipleRootWitness.Valid := by
  norm_num [degreeSevenStageSevenMultipleRootPrefix100Chunk001,
    degreeSevenStageSevenClassificationsPrefix100Chunk001,
    DegreeSevenStageSevenClassification.multipleRoots,
    DegreeSevenStageSevenMultipleRootWitness.Valid,
    DegreeSevenStageSevenMultipleRootWitness.coefficients,
    integerPolynomialRationalEval,
    DensePolynomial.derivative, DensePolynomial.add,
    DensePolynomial.eval]

theorem degreeSevenStageSevenClassificationsPrefix100Chunk001_valid :
    degreeSevenStageSevenClassificationsPrefix100Chunk001.Forall
      DegreeSevenStageSevenClassification.Valid := by
  apply DegreeSevenStageSevenClassification.forall_valid_of_projections
  · exact degreeSevenStageSevenScaledPrefix100Chunk001_valid
  · exact degreeSevenStageSevenMultipleRootPrefix100Chunk001_valid
  · exact degreeSevenStageSevenScaledCriticalSignPrefix100Chunk001_valid

/-- Every Hunter candidate matching a certified pilot row has its constant
coefficient in that row's exact final finite set. -/
theorem degreeSevenStageSevenPrefix100Chunk001_a0_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (entry : DegreeSevenStageSevenScaledEntry)
    (hentry : entry ∈ degreeSevenStageSevenScaledPrefix100Chunk001)
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
      degreeSevenStageSevenScaledPrefix100Chunk001_valid) entry hentry
  · exact ha6
  · exact ha5
  · exact ha4
  · exact ha3
  · exact ha2
  · exact ha1

end

end TraceEuclidean
