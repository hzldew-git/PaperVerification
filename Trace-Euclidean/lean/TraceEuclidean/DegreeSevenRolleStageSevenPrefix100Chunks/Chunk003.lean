import TraceEuclidean.DegreeSevenRolleStageSevenPrefixBridge

/-! Prefix100Chunk003 data for exact six-root Stage Seven certificates. -/

namespace TraceEuclidean

noncomputable section

open Polynomial

set_option maxRecDepth 100000

def degreeSevenStageSevenClassificationsPrefix100Chunk003 :
    List DegreeSevenStageSevenClassification :=
  [
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (2 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (3 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (3 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-23133420 : ℤ), (-23133417 : ℤ), (-6074202 : ℤ), (-6074199 : ℤ), (-4951205 : ℤ), (-4951202 : ℤ), (-2 : ℤ), (2 : ℤ), (7861182 : ℤ), (7861185 : ℤ), (69439050 : ℤ), (69439053 : ℤ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (4 : ℤ), (-1 : ℤ), (-1 : ℤ), (4294967296 : ℤ), (-4656505476 : ℤ), (-4656505473 : ℤ), (-2290725061 : ℤ), (-2290725058 : ℤ), (405339176 : ℤ), (405339179 : ℤ), (1098999938 : ℤ), (1098999941 : ℤ), (14646392764 : ℤ), (14646392767 : ℤ)⟩, (-1 : ℤ), (0 : ℤ), .fourth⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (4 : ℤ), (0 : ℤ), (0 : ℤ), (4294967296 : ℤ), (-4706659204 : ℤ), (-4706659201 : ℤ), (-2086873143 : ℤ), (-2086873140 : ℤ), (-2 : ℤ), (2 : ℤ), (1351744603 : ℤ), (1351744606 : ℤ), (14645289086 : ℤ), (14645289089 : ℤ)⟩, (0 : ℤ), (-1 : ℤ), .fourth⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (4 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (4 : ℤ), (1 : ℤ), (1 : ℤ), (4294967296 : ℤ), (-4753034682 : ℤ), (-4753034679 : ℤ), (-1835462099 : ℤ), (-1835462096 : ℤ), (-361037358 : ℤ), (-361037355 : ℤ), (1508850693 : ℤ), (1508850696 : ℤ), (14644184786 : ℤ), (14644184789 : ℤ)⟩, (1 : ℤ), (-1 : ℤ), .second⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (4 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-22142941 : ℤ), (-22142938 : ℤ), (-9764884 : ℤ), (-9764881 : ℤ), (-2937125 : ℤ), (-2937122 : ℤ), (-2 : ℤ), (2 : ℤ), (8621150 : ℤ), (8621153 : ℤ), (69365205 : ℤ), (69365208 : ℤ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (4 : ℤ), (2 : ℤ), (2 : ℤ), (4294967296 : ℤ), (-4796271434 : ℤ), (-4796271431 : ℤ), (-1413502347 : ℤ), (-1413502344 : ℤ), (-860050835 : ℤ), (-860050832 : ℤ), (1630246093 : ℤ), (1630246096 : ℤ), (14643079865 : ℤ), (14643079868 : ℤ)⟩, (2 : ℤ), (0 : ℤ), .second⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (4 : ℤ), (2 : ℤ), (2 : ℤ), (4294967296 : ℤ), (-4796271434 : ℤ), (-4796271431 : ℤ), (-1413502347 : ℤ), (-1413502344 : ℤ), (-860050835 : ℤ), (-860050832 : ℤ), (1630246093 : ℤ), (1630246096 : ℤ), (14643079865 : ℤ), (14643079868 : ℤ)⟩, (2 : ℤ), (1 : ℤ), .third⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (5 : ℤ), (-1 : ℤ), (-1 : ℤ), (4294967296 : ℤ), (-4463561866 : ℤ), (-4463561863 : ℤ), (-2612106452 : ℤ), (-2612106449 : ℤ), (304457989 : ℤ), (304457992 : ℤ), (1339630642 : ℤ), (1339630645 : ℤ), (14635081028 : ℤ), (14635081031 : ℤ)⟩, (-1 : ℤ), (0 : ℤ), .first⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (5 : ℤ), (0 : ℤ), (0 : ℤ), (4294967296 : ℤ), (-4530269424 : ℤ), (-4530269421 : ℤ), (-2417043979 : ℤ), (-2417043976 : ℤ), (-2 : ℤ), (2 : ℤ), (1516842928 : ℤ), (1516842931 : ℤ), (14633971817 : ℤ), (14633971820 : ℤ)⟩, (0 : ℤ), (-1 : ℤ), .fourth⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (5 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (5 : ℤ), (1 : ℤ), (1 : ℤ), (4294967296 : ℤ), (-4589721189 : ℤ), (-4589721186 : ℤ), (-2200085163 : ℤ), (-2200085160 : ℤ), (-286062561 : ℤ), (-286062558 : ℤ), (1646508277 : ℤ), (1646508280 : ℤ), (14632861977 : ℤ), (14632861980 : ℤ)⟩, (1 : ℤ), (-2 : ℤ), .second⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (5 : ℤ), (1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-21124276 : ℤ), (-21124273 : ℤ), (-9857430 : ℤ), (-9857427 : ℤ), (-7201294 : ℤ), (-7201291 : ℤ), (3664022 : ℤ), (3664025 : ℤ), (8368000 : ℤ), (8368003 : ℤ), (69292382 : ℤ), (69292385 : ℤ)⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (5 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-20790447 : ℤ), (-20790444 : ℤ), (-12422950 : ℤ), (-12422947 : ℤ), (-2272856 : ℤ), (-2272853 : ℤ), (-2 : ℤ), (2 : ℤ), (9336732 : ℤ), (9336735 : ℤ), (69290927 : ℤ), (69290930 : ℤ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (5 : ℤ), (2 : ℤ), (2 : ℤ), (4294967296 : ℤ), (-4643626158 : ℤ), (-4643626155 : ℤ), (-1931639163 : ℤ), (-1931639160 : ℤ), (-605245668 : ℤ), (-605245665 : ℤ), (1752260823 : ℤ), (1752260826 : ℤ), (14631751508 : ℤ), (14631751511 : ℤ)⟩, (2 : ℤ), (-1 : ℤ), .second⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (5 : ℤ), (2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-21558435 : ℤ), (-21558432 : ℤ), (-9152421 : ℤ), (-9152418 : ℤ), (-5510412 : ℤ), (-5510409 : ℤ), (-2 : ℤ), (2 : ℤ), (10083780 : ℤ), (10083783 : ℤ), (69278894 : ℤ), (69278897 : ℤ)⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (6 : ℤ), (0 : ℤ), (-2 : ℤ), (-1 : ℚ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (6 : ℤ), (0 : ℤ), (0 : ℤ), (4294967296 : ℤ), (-4294967298 : ℤ), (-4294967294 : ℤ), (-2789194913 : ℤ), (-2789194910 : ℤ), (-2 : ℤ), (2 : ℤ), (1665057128 : ℤ), (1665057131 : ℤ), (14622606425 : ℤ), (14622606428 : ℤ)⟩, (0 : ℤ), (-1 : ℤ), .first⟩,
    .multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (6 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℚ)⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (6 : ℤ), (1 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-19740198 : ℤ), (-19740195 : ℤ), (-10791161 : ℤ), (-10791158 : ℤ), (-9300144 : ℤ), (-9300141 : ℤ), (5967164 : ℤ), (5967167 : ℤ), (7786598 : ℤ), (7786601 : ℤ), (69219144 : ℤ), (69219147 : ℤ)⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (6 : ℤ), (1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-19078480 : ℤ), (-19078477 : ℤ), (-14036096 : ℤ), (-14036093 : ℤ), (-5565334 : ℤ), (-5565331 : ℤ), (3330342 : ℤ), (3330345 : ℤ), (9273295 : ℤ), (9273298 : ℤ), (69217677 : ℤ), (69217680 : ℤ)⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (6 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-17436516 : ℤ), (-17436513 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-1873322 : ℤ), (-1873319 : ℤ), (-2 : ℤ), (2 : ℤ), (10012252 : ℤ), (10012255 : ℤ), (69216210 : ℤ), (69216213 : ℤ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (6 : ℤ), (2 : ℤ), (2 : ℤ), (4294967296 : ℤ), (-4455521951 : ℤ), (-4455521948 : ℤ), (-2341471115 : ℤ), (-2341471112 : ℤ), (-488391812 : ℤ), (-488391809 : ℤ), (1868511317 : ℤ), (1868511320 : ℤ), (14620374903 : ℤ), (14620374906 : ℤ)⟩, (2 : ℤ), (-1 : ℤ), .second⟩,
    .scaled ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (6 : ℤ), (2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-19932832 : ℤ), (-19932829 : ℤ), (-12776811 : ℤ), (-12776808 : ℤ), (-4034623 : ℤ), (-4034620 : ℤ), (-2 : ℤ), (2 : ℤ), (10681578 : ℤ), (10681581 : ℤ), (69204092 : ℤ), (69204095 : ℤ)⟩,
    .criticalSign ⟨⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (6 : ℤ), (3 : ℤ), (3 : ℤ), (4294967296 : ℤ), (-4520305785 : ℤ), (-4520305782 : ℤ), (-2059260669 : ℤ), (-2059260666 : ℤ), (-786621970 : ℤ), (-786621967 : ℤ), (1950431579 : ℤ), (1950431582 : ℤ), (14619258185 : ℤ), (14619258188 : ℤ)⟩, (3 : ℤ), (0 : ℤ), .second⟩
  ]

def degreeSevenStageSevenScaledPrefix100Chunk003 :
    List DegreeSevenStageSevenScaledEntry :=
  DegreeSevenStageSevenClassification.scaledEntries
    degreeSevenStageSevenClassificationsPrefix100Chunk003

def degreeSevenStageSevenMultipleRootPrefix100Chunk003 :
    List DegreeSevenStageSevenMultipleRootWitness :=
  DegreeSevenStageSevenClassification.multipleRoots
    degreeSevenStageSevenClassificationsPrefix100Chunk003

def degreeSevenStageSevenScaledCriticalSignPrefix100Chunk003 :
    List DegreeSevenStageSevenScaledCriticalSignWitness :=
  DegreeSevenStageSevenClassification.criticalSigns
    degreeSevenStageSevenClassificationsPrefix100Chunk003

set_option maxHeartbeats 0 in
-- Kernel reduction checks every scaled parent and forbidden interval sign.
theorem degreeSevenStageSevenScaledCriticalSignPrefix100Chunk003_arithmeticValid :
    degreeSevenStageSevenScaledCriticalSignPrefix100Chunk003.Forall
      DegreeSevenStageSevenScaledCriticalSignWitness.ArithmeticValid := by
  decide

theorem degreeSevenStageSevenScaledCriticalSignPrefix100Chunk003_valid :
    degreeSevenStageSevenScaledCriticalSignPrefix100Chunk003.Forall
      (fun witness => witness.toWitness.Valid) := by
  exact degreeSevenStageSevenScaledCriticalSignPrefix100Chunk003_arithmeticValid.imp
    DegreeSevenStageSevenScaledCriticalSignWitness.valid_of_arithmeticValid

def degreeSevenStageSevenCriticalSignPrefix100Chunk003 :
    List DegreeSevenStageSevenCriticalSignWitness :=
  degreeSevenStageSevenScaledCriticalSignPrefix100Chunk003.map
    DegreeSevenStageSevenScaledCriticalSignWitness.toWitness

theorem degreeSevenStageSevenCriticalSignPrefix100Chunk003_valid :
    degreeSevenStageSevenCriticalSignPrefix100Chunk003.Forall
      DegreeSevenStageSevenCriticalSignWitness.Valid := by
  rw [degreeSevenStageSevenCriticalSignPrefix100Chunk003, List.forall_map_iff]
  change degreeSevenStageSevenScaledCriticalSignPrefix100Chunk003.Forall
    (fun witness => witness.toWitness.Valid)
  exact degreeSevenStageSevenScaledCriticalSignPrefix100Chunk003_valid


theorem degreeSevenStageSevenScaledPrefix100Chunk003_arithmeticValid :
    degreeSevenStageSevenScaledPrefix100Chunk003.Forall
      DegreeSevenStageSevenScaledEntry.ArithmeticValid := by
  decide

theorem degreeSevenStageSevenScaledPrefix100Chunk003_valid :
    degreeSevenStageSevenScaledPrefix100Chunk003.Forall
      (fun entry => entry.toEntry.Valid) := by
  exact degreeSevenStageSevenScaledPrefix100Chunk003_arithmeticValid.imp
    DegreeSevenStageSevenScaledEntry.valid_of_arithmeticValid

theorem degreeSevenStageSevenMultipleRootPrefix100Chunk003_valid :
    degreeSevenStageSevenMultipleRootPrefix100Chunk003.Forall
      DegreeSevenStageSevenMultipleRootWitness.Valid := by
  norm_num [degreeSevenStageSevenMultipleRootPrefix100Chunk003,
    degreeSevenStageSevenClassificationsPrefix100Chunk003,
    DegreeSevenStageSevenClassification.multipleRoots,
    DegreeSevenStageSevenMultipleRootWitness.Valid,
    DegreeSevenStageSevenMultipleRootWitness.coefficients,
    integerPolynomialRationalEval,
    DensePolynomial.derivative, DensePolynomial.add,
    DensePolynomial.eval]

theorem degreeSevenStageSevenClassificationsPrefix100Chunk003_valid :
    degreeSevenStageSevenClassificationsPrefix100Chunk003.Forall
      DegreeSevenStageSevenClassification.Valid := by
  apply DegreeSevenStageSevenClassification.forall_valid_of_projections
  · exact degreeSevenStageSevenScaledPrefix100Chunk003_valid
  · exact degreeSevenStageSevenMultipleRootPrefix100Chunk003_valid
  · exact degreeSevenStageSevenScaledCriticalSignPrefix100Chunk003_valid

/-- Every Hunter candidate matching a certified pilot row has its constant
coefficient in that row's exact final finite set. -/
theorem degreeSevenStageSevenPrefix100Chunk003_a0_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (entry : DegreeSevenStageSevenScaledEntry)
    (hentry : entry ∈ degreeSevenStageSevenScaledPrefix100Chunk003)
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
      degreeSevenStageSevenScaledPrefix100Chunk003_valid) entry hentry
  · exact ha6
  · exact ha5
  · exact ha4
  · exact ha3
  · exact ha2
  · exact ha1

end

end TraceEuclidean
