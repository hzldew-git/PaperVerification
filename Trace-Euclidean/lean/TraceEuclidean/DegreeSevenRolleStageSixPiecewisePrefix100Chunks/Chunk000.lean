import TraceEuclidean.DegreeSevenRolleStageSixPiecewise
import TraceEuclidean.DegreeSevenRolleStageSixScaledCandidates

/-! Prefix100Chunk000 data for piecewise Stage Six parameter refinement. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def degreeSevenStageSixPiecewisePrefix100Chunk000 :
    List DegreeSevenStageSixPiecewiseCoverage :=
  [
    ⟨⟨⟨(-3 : ℤ), (-9 : ℤ), (-7 : ℤ), (-2 : ℤ), (-2486 : ℤ), (-1359 : ℤ), (-424 : ℤ), (11285 : ℤ)⟩, ⟨(0 : ℤ), ⟨(-1 : ℤ), .first⟩, none⟩, ⟨(-1 : ℤ), ⟨(0 : ℤ), .second⟩, none⟩, none⟩,
      []⟩,
    ⟨⟨⟨(-3 : ℤ), (-9 : ℤ), (-6 : ℤ), (-1 : ℤ), (-2779 : ℤ), (-1232 : ℤ), (-211 : ℤ), (11237 : ℤ)⟩, ⟨(0 : ℤ), ⟨(-1 : ℤ), .third⟩, none⟩, ⟨(0 : ℤ), ⟨(1 : ℤ), .second⟩, none⟩, some ⟨(-3 : ℤ), (-9 : ℤ), (-6 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), (-52900 : ℤ), (-52897 : ℤ), (-29077 : ℤ), (-29074 : ℤ), (-7455 : ℤ), (-7452 : ℤ), (-2 : ℤ), (2 : ℤ), (229861 : ℤ), (229864 : ℤ)⟩⟩,
      [⟨(-3 : ℤ), (-9 : ℤ), (-6 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), (16777216 : ℤ), (-13541914 : ℤ), (-13541911 : ℤ), (-7443441 : ℤ), (-7443438 : ℤ), (-1908186 : ℤ), (-1908183 : ℤ), (-2 : ℤ), (2 : ℤ), (58844713 : ℤ), (58844716 : ℤ)⟩]⟩,
    ⟨⟨⟨(-3 : ℤ), (-9 : ℤ), (-6 : ℤ), (0 : ℤ), (-2602 : ℤ), (-1615 : ℤ), (-1 : ℤ), (11233 : ℤ)⟩, ⟨(1 : ℤ), ⟨(-1 : ℤ), .first⟩, some (.multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (-6 : ℤ), (0 : ℤ), (0 : ℤ), ((0 : ℤ) : ℚ)⟩)⟩, ⟨(1 : ℤ), ⟨(2 : ℤ), .second⟩, none⟩, some ⟨(-3 : ℤ), (-9 : ℤ), (-6 : ℤ), (0 : ℤ), (1 : ℤ), (1 : ℤ), (-44046 : ℤ), (-44043 : ℤ), (-38727 : ℤ), (-38724 : ℤ), (-15795 : ℤ), (-15792 : ℤ), (9302 : ℤ), (9305 : ℤ), (229694 : ℤ), (229697 : ℤ)⟩⟩,
      [⟨(-3 : ℤ), (-9 : ℤ), (-6 : ℤ), (0 : ℤ), (1 : ℤ), (1 : ℤ), (16777216 : ℤ), (-11275487 : ℤ), (-11275484 : ℤ), (-9913853 : ℤ), (-9913850 : ℤ), (-4043255 : ℤ), (-4043252 : ℤ), (2381652 : ℤ), (2381655 : ℤ), (58802112 : ℤ), (58802115 : ℤ)⟩]⟩,
    ⟨⟨⟨(-3 : ℤ), (-9 : ℤ), (-5 : ℤ), (-1 : ℤ), (-3095 : ℤ), (-785 : ℤ), (-298 : ℤ), (11193 : ℤ)⟩, ⟨(0 : ℤ), ⟨(-1 : ℤ), .third⟩, none⟩, ⟨(-1 : ℤ), ⟨(0 : ℤ), .second⟩, none⟩, none⟩,
      []⟩,
    ⟨⟨⟨(-3 : ℤ), (-9 : ℤ), (-5 : ℤ), (0 : ℤ), (-3000 : ℤ), (-1172 : ℤ), (-1 : ℤ), (11189 : ℤ)⟩, ⟨(1 : ℤ), ⟨(-1 : ℤ), .third⟩, some (.multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (-5 : ℤ), (0 : ℤ), (0 : ℤ), ((0 : ℤ) : ℚ)⟩)⟩, ⟨(0 : ℤ), ⟨(1 : ℤ), .second⟩, none⟩, none⟩,
      []⟩,
    ⟨⟨⟨(-3 : ℤ), (-9 : ℤ), (-5 : ℤ), (1 : ℤ), (-2884 : ℤ), (-1455 : ℤ), (170 : ℤ), (11185 : ℤ)⟩, ⟨(1 : ℤ), ⟨(0 : ℤ), .first⟩, none⟩, ⟨(1 : ℤ), ⟨(2 : ℤ), .second⟩, none⟩, some ⟨(-3 : ℤ), (-9 : ℤ), (-5 : ℤ), (1 : ℤ), (1 : ℤ), (1 : ℤ), (-53185 : ℤ), (-53182 : ℤ), (-35249 : ℤ), (-35246 : ℤ), (-11397 : ℤ), (-11394 : ℤ), (11794 : ℤ), (11797 : ℤ), (228463 : ℤ), (228466 : ℤ)⟩⟩,
      [⟨(-3 : ℤ), (-9 : ℤ), (-5 : ℤ), (1 : ℤ), (1 : ℤ), (1 : ℤ), (16777216 : ℤ), (-13614954 : ℤ), (-13614951 : ℤ), (-9023272 : ℤ), (-9023269 : ℤ), (-2917228 : ℤ), (-2917225 : ℤ), (3019752 : ℤ), (3019755 : ℤ), (58486872 : ℤ), (58486875 : ℤ)⟩]⟩,
    ⟨⟨⟨(-3 : ℤ), (-9 : ℤ), (-5 : ℤ), (2 : ℤ), (-2727 : ℤ), (-1740 : ℤ), (302 : ℤ), (11181 : ℤ)⟩, ⟨(3 : ℤ), ⟨(2 : ℤ), .first⟩, none⟩, ⟨(2 : ℤ), ⟨(3 : ℤ), .second⟩, none⟩, none⟩,
      []⟩,
    ⟨⟨⟨(-3 : ℤ), (-9 : ℤ), (-5 : ℤ), (3 : ℤ), (-2387 : ℤ), (-2187 : ℤ), (413 : ℤ), (11177 : ℤ)⟩, ⟨(5 : ℤ), ⟨(4 : ℤ), .first⟩, none⟩, ⟨(4 : ℤ), ⟨(5 : ℤ), .second⟩, none⟩, none⟩,
      []⟩,
    ⟨⟨⟨(-3 : ℤ), (-9 : ℤ), (-4 : ℤ), (0 : ℤ), (-3260 : ℤ), (-866 : ℤ), (-1 : ℤ), (11144 : ℤ)⟩, ⟨(1 : ℤ), ⟨(-1 : ℤ), .third⟩, some (.multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (-4 : ℤ), (0 : ℤ), (0 : ℤ), ((0 : ℤ) : ℚ)⟩)⟩, ⟨(0 : ℤ), ⟨(1 : ℤ), .second⟩, none⟩, none⟩,
      []⟩,
    ⟨⟨⟨(-3 : ℤ), (-9 : ℤ), (-4 : ℤ), (1 : ℤ), (-3184 : ℤ), (-1138 : ℤ), (198 : ℤ), (11140 : ℤ)⟩, ⟨(0 : ℤ), ⟨(-1 : ℤ), .third⟩, none⟩, ⟨(1 : ℤ), ⟨(2 : ℤ), .second⟩, none⟩, some ⟨(-3 : ℤ), (-9 : ℤ), (-4 : ℤ), (1 : ℤ), (0 : ℤ), (1 : ℤ), (-63290 : ℤ), (-61885 : ℤ), (-31088 : ℤ), (-21263 : ℤ), (-14959 : ℤ), (2 : ℤ), (6023 : ℤ), (12579 : ℤ), (227367 : ℤ), (227385 : ℤ)⟩⟩,
      [⟨(-3 : ℤ), (-9 : ℤ), (-4 : ℤ), (1 : ℤ), (0 : ℤ), (1 : ℤ), (16777216 : ℤ), (-16201891 : ℤ), (-15842971 : ℤ), (-7958160 : ℤ), (-5443801 : ℤ), (-3829196 : ℤ), (2 : ℤ), (1542174 : ℤ), (3219850 : ℤ), (58206213 : ℤ), (58210133 : ℤ)⟩]⟩
  ]

@[simp] theorem degreeSevenStageSixPiecewisePrefix100Chunk000A1LowerBound000 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (-6 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), (16777216 : ℤ), (-13541914 : ℤ), (-13541911 : ℤ), (-7443441 : ℤ), (-7443438 : ℤ), (-1908186 : ℤ), (-1908183 : ℤ), (-2 : ℤ), (2 : ℤ), (58844713 : ℤ), (58844716 : ℤ)⟩
    family.scaledA1LowerBound (0 : ℤ) = (0 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewisePrefix100Chunk000A1UpperBound000 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (-6 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), (16777216 : ℤ), (-13541914 : ℤ), (-13541911 : ℤ), (-7443441 : ℤ), (-7443438 : ℤ), (-1908186 : ℤ), (-1908183 : ℤ), (-2 : ℤ), (2 : ℤ), (58844713 : ℤ), (58844716 : ℤ)⟩
    family.scaledA1UpperBound (0 : ℤ) = (0 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewisePrefix100Chunk000A1LowerBound001 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (-6 : ℤ), (0 : ℤ), (1 : ℤ), (1 : ℤ), (16777216 : ℤ), (-11275487 : ℤ), (-11275484 : ℤ), (-9913853 : ℤ), (-9913850 : ℤ), (-4043255 : ℤ), (-4043252 : ℤ), (2381652 : ℤ), (2381655 : ℤ), (58802112 : ℤ), (58802115 : ℤ)⟩
    family.scaledA1LowerBound (1 : ℤ) = (1 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewisePrefix100Chunk000A1UpperBound001 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (-6 : ℤ), (0 : ℤ), (1 : ℤ), (1 : ℤ), (16777216 : ℤ), (-11275487 : ℤ), (-11275484 : ℤ), (-9913853 : ℤ), (-9913850 : ℤ), (-4043255 : ℤ), (-4043252 : ℤ), (2381652 : ℤ), (2381655 : ℤ), (58802112 : ℤ), (58802115 : ℤ)⟩
    family.scaledA1UpperBound (1 : ℤ) = (0 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewisePrefix100Chunk000A1LowerBound002 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (-5 : ℤ), (1 : ℤ), (1 : ℤ), (1 : ℤ), (16777216 : ℤ), (-13614954 : ℤ), (-13614951 : ℤ), (-9023272 : ℤ), (-9023269 : ℤ), (-2917228 : ℤ), (-2917225 : ℤ), (3019752 : ℤ), (3019755 : ℤ), (58486872 : ℤ), (58486875 : ℤ)⟩
    family.scaledA1LowerBound (1 : ℤ) = (0 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewisePrefix100Chunk000A1UpperBound002 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (-5 : ℤ), (1 : ℤ), (1 : ℤ), (1 : ℤ), (16777216 : ℤ), (-13614954 : ℤ), (-13614951 : ℤ), (-9023272 : ℤ), (-9023269 : ℤ), (-2917228 : ℤ), (-2917225 : ℤ), (3019752 : ℤ), (3019755 : ℤ), (58486872 : ℤ), (58486875 : ℤ)⟩
    family.scaledA1UpperBound (1 : ℤ) = (0 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewisePrefix100Chunk000A1LowerBound003 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (-4 : ℤ), (1 : ℤ), (0 : ℤ), (1 : ℤ), (16777216 : ℤ), (-16201891 : ℤ), (-15842971 : ℤ), (-7958160 : ℤ), (-5443801 : ℤ), (-3829196 : ℤ), (2 : ℤ), (1542174 : ℤ), (3219850 : ℤ), (58206213 : ℤ), (58210133 : ℤ)⟩
    family.scaledA1LowerBound (0 : ℤ) = (0 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewisePrefix100Chunk000A1UpperBound003 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (-4 : ℤ), (1 : ℤ), (0 : ℤ), (1 : ℤ), (16777216 : ℤ), (-16201891 : ℤ), (-15842971 : ℤ), (-7958160 : ℤ), (-5443801 : ℤ), (-3829196 : ℤ), (2 : ℤ), (1542174 : ℤ), (3219850 : ℤ), (58206213 : ℤ), (58210133 : ℤ)⟩
    family.scaledA1UpperBound (0 : ℤ) = (0 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewisePrefix100Chunk000A1LowerBound004 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (-4 : ℤ), (1 : ℤ), (0 : ℤ), (1 : ℤ), (16777216 : ℤ), (-16201891 : ℤ), (-15842971 : ℤ), (-7958160 : ℤ), (-5443801 : ℤ), (-3829196 : ℤ), (2 : ℤ), (1542174 : ℤ), (3219850 : ℤ), (58206213 : ℤ), (58210133 : ℤ)⟩
    family.scaledA1LowerBound (1 : ℤ) = (0 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewisePrefix100Chunk000A1UpperBound004 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (-4 : ℤ), (1 : ℤ), (0 : ℤ), (1 : ℤ), (16777216 : ℤ), (-16201891 : ℤ), (-15842971 : ℤ), (-7958160 : ℤ), (-5443801 : ℤ), (-3829196 : ℤ), (2 : ℤ), (1542174 : ℤ), (3219850 : ℤ), (58206213 : ℤ), (58210133 : ℤ)⟩
    family.scaledA1UpperBound (1 : ℤ) = (0 : ℤ) := by
  rfl

def degreeSevenStageSixPiecewisePrefix100Chunk000CoarseCoverages :
    List DegreeSevenStageSixStrongCompactCoverage :=
  degreeSevenStageSixPiecewisePrefix100Chunk000.map
    DegreeSevenStageSixPiecewiseCoverage.coverage

def degreeSevenStageSixPiecewisePrefix100Chunk000Edges :
    List DegreeSevenStageSixMultipleRootWitness :=
  degreeSevenStageSixPiecewisePrefix100Chunk000CoarseCoverages.flatMap
    DegreeSevenStageSixStrongCompactCoverage.edgeRejections

theorem degreeSevenStageSixPiecewisePrefix100Chunk000Skeletons_valid :
    degreeSevenStageSixPiecewisePrefix100Chunk000CoarseCoverages.Forall
      DegreeSevenStageSixStrongCompactCoverage.SkeletonValid := by
  decide

theorem degreeSevenStageSixPiecewisePrefix100Chunk000Edges_valid :
    degreeSevenStageSixPiecewisePrefix100Chunk000Edges.Forall
      DegreeSevenStageSixMultipleRootWitness.Valid := by
  norm_num [degreeSevenStageSixPiecewisePrefix100Chunk000Edges,
    degreeSevenStageSixPiecewisePrefix100Chunk000CoarseCoverages,
    degreeSevenStageSixPiecewisePrefix100Chunk000,
    DegreeSevenStageSixStrongCompactCoverage.edgeRejections,
    DegreeSevenStageSixCompactLowerBoundary.edgeRejections,
    DegreeSevenStageSixCompactUpperBoundary.edgeRejections,
    DegreeSevenStageSixCompactRejection.exactWitnesses,
    DegreeSevenStageSixMultipleRootWitness.Valid,
    DegreeSevenStageSixMultipleRootWitness.coefficients,
    integerPolynomialRationalEval,
    DensePolynomial.derivative,
    DensePolynomial.add,
    DensePolynomial.eval]

theorem degreeSevenStageSixPiecewisePrefix100Chunk000CoarseCoverages_valid :
    degreeSevenStageSixPiecewisePrefix100Chunk000CoarseCoverages.Forall
      DegreeSevenStageSixStrongCompactCoverage.Valid := by
  apply List.Forall.imp
    DegreeSevenStageSixStrongCompactCoverage.valid_of_arithmeticValid
  apply
    DegreeSevenStageSixStrongCompactCoverage.list_forall_arithmeticValid_of_skeletons_and_edges
  · exact degreeSevenStageSixPiecewisePrefix100Chunk000Skeletons_valid
  · exact degreeSevenStageSixPiecewisePrefix100Chunk000Edges_valid

theorem degreeSevenStageSixPiecewisePrefix100Chunk000Pieces_valid :
    degreeSevenStageSixPiecewisePrefix100Chunk000.Forall
      DegreeSevenStageSixPiecewiseCoverage.PiecesValid := by
  decide

theorem degreeSevenStageSixPiecewisePrefix100Chunk000_valid :
    degreeSevenStageSixPiecewisePrefix100Chunk000.Forall
      DegreeSevenStageSixPiecewiseCoverage.Valid := by
  apply DegreeSevenStageSixPiecewiseCoverage.list_forall_valid_of_parts
  · exact degreeSevenStageSixPiecewisePrefix100Chunk000CoarseCoverages_valid
  · exact degreeSevenStageSixPiecewisePrefix100Chunk000Pieces_valid

end

end TraceEuclidean
