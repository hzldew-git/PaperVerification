import TraceEuclidean.DegreeSevenRolleStageSixPiecewise
import TraceEuclidean.DegreeSevenRolleStageSixScaledCandidates

/-! Rows200To299Chunk001 data for piecewise Stage Six parameter refinement. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def degreeSevenStageSixPiecewiseRows200To299Chunk001 :
    List DegreeSevenStageSixPiecewiseCoverage :=
  [
    ⟨⟨⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (27 : ℤ), (-3738 : ℤ), (-2233 : ℤ), (2476 : ℤ), (10511 : ℤ)⟩, ⟨(21 : ℤ), ⟨(19 : ℤ), .first⟩, some (.criticalSign ⟨(20 : ℤ), .first, ⟨(4096 : ℤ), (-3737 : ℤ), (-3736 : ℤ), (-2232 : ℤ), (-2231 : ℤ), (2477 : ℤ), (2478 : ℤ), (10512 : ℤ), (10513 : ℤ)⟩⟩)⟩, ⟨(23 : ℤ), ⟨(24 : ℤ), .second⟩, none⟩, some ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (27 : ℤ), (21 : ℤ), (23 : ℤ), (-69286 : ℤ), (-65534 : ℤ), (-52399 : ℤ), (-43626 : ℤ), (-28691 : ℤ), (-23212 : ℤ), (72553 : ℤ), (73062 : ℤ), (208975 : ℤ), (209028 : ℤ)⟩⟩,
      [⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (27 : ℤ), (21 : ℤ), (21 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-13413860 : ℤ), (-13413857 : ℤ), (-5942629 : ℤ), (-5942626 : ℤ), (18573988 : ℤ), (18573991 : ℤ), (53510888 : ℤ), (53510891 : ℤ)⟩,
        ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (27 : ℤ), (22 : ℤ), (22 : ℤ), (16777216 : ℤ), (-17334335 : ℤ), (-17334332 : ℤ), (-12318991 : ℤ), (-12318988 : ℤ), (-6538946 : ℤ), (-6538943 : ℤ), (18639034 : ℤ), (18639037 : ℤ), (53504407 : ℤ), (53504410 : ℤ)⟩,
        ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (27 : ℤ), (23 : ℤ), (23 : ℤ), (16777216 : ℤ), (-17736923 : ℤ), (-17736920 : ℤ), (-11168748 : ℤ), (-11168745 : ℤ), (-7344563 : ℤ), (-7344560 : ℤ), (18703484 : ℤ), (18703487 : ℤ), (53497919 : ℤ), (53497922 : ℤ)⟩]⟩,
    ⟨⟨⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (28 : ℤ), (-3674 : ℤ), (-2325 : ℤ), (2510 : ℤ), (10505 : ℤ)⟩, ⟨(23 : ℤ), ⟨(22 : ℤ), .first⟩, none⟩, ⟨(25 : ℤ), ⟨(26 : ℤ), .second⟩, none⟩, some ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (28 : ℤ), (23 : ℤ), (25 : ℤ), (-67547 : ℤ), (-61975 : ℤ), (-55066 : ℤ), (-43607 : ℤ), (-31478 : ℤ), (-25152 : ℤ), (73894 : ℤ), (74385 : ℤ), (208680 : ℤ), (208734 : ℤ)⟩⟩,
      [⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (28 : ℤ), (23 : ℤ), (23 : ℤ), (16777216 : ℤ), (-15865899 : ℤ), (-15865896 : ℤ), (-14096424 : ℤ), (-14096421 : ℤ), (-6439395 : ℤ), (-6439392 : ℤ), (18917277 : ℤ), (18917280 : ℤ), (53435611 : ℤ), (53435614 : ℤ)⟩,
        ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (28 : ℤ), (24 : ℤ), (24 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-12586779 : ℤ), (-12586776 : ℤ), (-7093878 : ℤ), (-7093875 : ℤ), (18979980 : ℤ), (18979983 : ℤ), (53429064 : ℤ), (53429067 : ℤ)⟩,
        ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (28 : ℤ), (25 : ℤ), (25 : ℤ), (16777216 : ℤ), (-17291535 : ℤ), (-17291532 : ℤ), (-11163855 : ℤ), (-11163852 : ℤ), (-8058096 : ℤ), (-8058093 : ℤ), (19042145 : ℤ), (19042148 : ℤ), (53422511 : ℤ), (53422514 : ℤ)⟩]⟩,
    ⟨⟨⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (29 : ℤ), (-3601 : ℤ), (-2426 : ℤ), (2543 : ℤ), (10500 : ℤ)⟩, ⟨(26 : ℤ), ⟨(25 : ℤ), .first⟩, none⟩, ⟨(27 : ℤ), ⟨(28 : ℤ), .second⟩, none⟩, some ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (29 : ℤ), (26 : ℤ), (27 : ℤ), (-65538 : ℤ), (-62683 : ℤ), (-50890 : ℤ), (-43571 : ℤ), (-34518 : ℤ), (-29842 : ℤ), (75439 : ℤ), (75677 : ℤ), (208383 : ℤ), (208412 : ℤ)⟩⟩,
      [⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (29 : ℤ), (26 : ℤ), (26 : ℤ), (16777216 : ℤ), (-16047316 : ℤ), (-16047313 : ℤ), (-13027448 : ℤ), (-13027445 : ℤ), (-7639900 : ℤ), (-7639897 : ℤ), (19312793 : ℤ), (19312796 : ℤ), (53353040 : ℤ), (53353043 : ℤ)⟩,
        ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (29 : ℤ), (27 : ℤ), (27 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-11154640 : ℤ), (-11154637 : ℤ), (-8836273 : ℤ), (-8836270 : ℤ), (19372880 : ℤ), (19372883 : ℤ), (53346419 : ℤ), (53346422 : ℤ)⟩]⟩,
    ⟨⟨⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (30 : ℤ), (-3514 : ℤ), (-2540 : ℤ), (2576 : ℤ), (10494 : ℤ)⟩, ⟨(29 : ℤ), ⟨(27 : ℤ), .first⟩, some (.criticalSign ⟨(28 : ℤ), .first, ⟨(4096 : ℤ), (-3513 : ℤ), (-3512 : ℤ), (-2539 : ℤ), (-2538 : ℤ), (2577 : ℤ), (2578 : ℤ), (10495 : ℤ), (10496 : ℤ)⟩⟩)⟩, ⟨(29 : ℤ), ⟨(30 : ℤ), .second⟩, none⟩, some ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (30 : ℤ), (29 : ℤ), (29 : ℤ), (-63106 : ℤ), (-63103 : ℤ), (-43480 : ℤ), (-43477 : ℤ), (-38008 : ℤ), (-38005 : ℤ), (76938 : ℤ), (76941 : ℤ), (208083 : ℤ), (208086 : ℤ)⟩⟩,
      [⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (30 : ℤ), (29 : ℤ), (29 : ℤ), (16777216 : ℤ), (-16154658 : ℤ), (-16154655 : ℤ), (-11130524 : ℤ), (-11130521 : ℤ), (-9729676 : ℤ), (-9729673 : ℤ), (19696399 : ℤ), (19696402 : ℤ), (53269629 : ℤ), (53269632 : ℤ)⟩]⟩,
    ⟨⟨⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (31 : ℤ), (-3402 : ℤ), (-2680 : ℤ), (2608 : ℤ), (10489 : ℤ)⟩, ⟨(31 : ℤ), ⟨(30 : ℤ), .first⟩, none⟩, ⟨(30 : ℤ), ⟨(32 : ℤ), .second⟩, some (.criticalSign ⟨(31 : ℤ), .second, ⟨(16384 : ℤ), (-13601 : ℤ), (-13600 : ℤ), (-10713 : ℤ), (-10712 : ℤ), (10439 : ℤ), (10440 : ℤ), (41960 : ℤ), (41961 : ℤ)⟩⟩)⟩, none⟩,
      []⟩,
    ⟨⟨⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (32 : ℤ), (-3212 : ℤ), (-2895 : ℤ), (2640 : ℤ), (10483 : ℤ)⟩, ⟨(33 : ℤ), ⟨(32 : ℤ), .first⟩, none⟩, ⟨(33 : ℤ), ⟨(34 : ℤ), .second⟩, none⟩, some ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (32 : ℤ), (33 : ℤ), (33 : ℤ), (-52883 : ℤ), (-52880 : ℤ), (-49426 : ℤ), (-49423 : ℤ), (-44128 : ℤ), (-44125 : ℤ), (79390 : ℤ), (79393 : ℤ), (207475 : ℤ), (207478 : ℤ)⟩⟩,
      [⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (32 : ℤ), (33 : ℤ), (33 : ℤ), (16777216 : ℤ), (-13537683 : ℤ), (-13537680 : ℤ), (-12652750 : ℤ), (-12652747 : ℤ), (-11296486 : ℤ), (-11296483 : ℤ), (20324202 : ℤ), (20324205 : ℤ), (53113887 : ℤ), (53113890 : ℤ)⟩]⟩,
    ⟨⟨⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (-2 : ℤ), (-4726 : ℤ), (538 : ℤ), (593 : ℤ), (10611 : ℤ)⟩, ⟨(1 : ℤ), ⟨(0 : ℤ), .third⟩, none⟩, ⟨(0 : ℤ), ⟨(1 : ℤ), .second⟩, none⟩, none⟩,
      []⟩,
    ⟨⟨⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (-1 : ℤ), (-4707 : ℤ), (168 : ℤ), (950 : ℤ), (10606 : ℤ)⟩, ⟨(0 : ℤ), ⟨(-1 : ℤ), .third⟩, none⟩, ⟨(0 : ℤ), ⟨(1 : ℤ), .second⟩, none⟩, some ⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), (-100639 : ℤ), (-100636 : ℤ), (-2 : ℤ), (2 : ℤ), (5845 : ℤ), (5848 : ℤ), (20895 : ℤ), (20898 : ℤ), (214328 : ℤ), (214331 : ℤ)⟩⟩,
      [⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), (16777216 : ℤ), (-25763314 : ℤ), (-25763311 : ℤ), (-2 : ℤ), (2 : ℤ), (1496732 : ℤ), (1496735 : ℤ), (5349512 : ℤ), (5349515 : ℤ), (54868241 : ℤ), (54868244 : ℤ)⟩]⟩,
    ⟨⟨⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (0 : ℤ), (-4688 : ℤ), (-1 : ℤ), (1105 : ℤ), (10600 : ℤ)⟩, ⟨(-1 : ℤ), ⟨(-2 : ℤ), .third⟩, none⟩, ⟨(-1 : ℤ), ⟨(1 : ℤ), .second⟩, some (.multipleRoot ⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (0 : ℤ), (0 : ℤ), ((0 : ℤ) : ℚ)⟩)⟩, some ⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (0 : ℤ), (-1 : ℤ), (-1 : ℤ), (-99838 : ℤ), (-99835 : ℤ), (-8968 : ℤ), (-8965 : ℤ), (14785 : ℤ), (14788 : ℤ), (20308 : ℤ), (20311 : ℤ), (214141 : ℤ), (214144 : ℤ)⟩⟩,
      [⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (0 : ℤ), (-1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-25558195 : ℤ), (-25558192 : ℤ), (-2295499 : ℤ), (-2295496 : ℤ), (3785270 : ℤ), (3785273 : ℤ), (5199164 : ℤ), (5199167 : ℤ), (54820429 : ℤ), (54820432 : ℤ)⟩]⟩,
    ⟨⟨⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (1 : ℤ), (-4669 : ℤ), (-134 : ℤ), (1223 : ℤ), (10595 : ℤ)⟩, ⟨(-1 : ℤ), ⟨(-2 : ℤ), .third⟩, none⟩, ⟨(0 : ℤ), ⟨(1 : ℤ), .second⟩, none⟩, some ⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (1 : ℤ), (-1 : ℤ), (0 : ℤ), (-99310 : ℤ), (-99156 : ℤ), (-10751 : ℤ), (-4138 : ℤ), (-2 : ℤ), (9321 : ℤ), (27087 : ℤ), (29972 : ℤ), (213910 : ℤ), (213935 : ℤ)⟩⟩,
      [⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (1 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-25422976 : ℤ), (-25384280 : ℤ), (-2751882 : ℤ), (-1059624 : ℤ), (-2 : ℤ), (2385889 : ℤ), (6934536 : ℤ), (7672345 : ℤ), (54761431 : ℤ), (54766916 : ℤ)⟩]⟩
  ]

@[simp] theorem degreeSevenStageSixPiecewiseRows200To299Chunk001A1LowerBound000 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (27 : ℤ), (21 : ℤ), (21 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-13413860 : ℤ), (-13413857 : ℤ), (-5942629 : ℤ), (-5942626 : ℤ), (18573988 : ℤ), (18573991 : ℤ), (53510888 : ℤ), (53510891 : ℤ)⟩
    family.scaledA1LowerBound (21 : ℤ) = (5 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewiseRows200To299Chunk001A1UpperBound000 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (27 : ℤ), (21 : ℤ), (21 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-13413860 : ℤ), (-13413857 : ℤ), (-5942629 : ℤ), (-5942626 : ℤ), (18573988 : ℤ), (18573991 : ℤ), (53510888 : ℤ), (53510891 : ℤ)⟩
    family.scaledA1UpperBound (21 : ℤ) = (5 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewiseRows200To299Chunk001A1LowerBound001 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (27 : ℤ), (22 : ℤ), (22 : ℤ), (16777216 : ℤ), (-17334335 : ℤ), (-17334332 : ℤ), (-12318991 : ℤ), (-12318988 : ℤ), (-6538946 : ℤ), (-6538943 : ℤ), (18639034 : ℤ), (18639037 : ℤ), (53504407 : ℤ), (53504410 : ℤ)⟩
    family.scaledA1LowerBound (22 : ℤ) = (7 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewiseRows200To299Chunk001A1UpperBound001 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (27 : ℤ), (22 : ℤ), (22 : ℤ), (16777216 : ℤ), (-17334335 : ℤ), (-17334332 : ℤ), (-12318991 : ℤ), (-12318988 : ℤ), (-6538946 : ℤ), (-6538943 : ℤ), (18639034 : ℤ), (18639037 : ℤ), (53504407 : ℤ), (53504410 : ℤ)⟩
    family.scaledA1UpperBound (22 : ℤ) = (7 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewiseRows200To299Chunk001A1LowerBound002 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (27 : ℤ), (23 : ℤ), (23 : ℤ), (16777216 : ℤ), (-17736923 : ℤ), (-17736920 : ℤ), (-11168748 : ℤ), (-11168745 : ℤ), (-7344563 : ℤ), (-7344560 : ℤ), (18703484 : ℤ), (18703487 : ℤ), (53497919 : ℤ), (53497922 : ℤ)⟩
    family.scaledA1LowerBound (23 : ℤ) = (8 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewiseRows200To299Chunk001A1UpperBound002 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (27 : ℤ), (23 : ℤ), (23 : ℤ), (16777216 : ℤ), (-17736923 : ℤ), (-17736920 : ℤ), (-11168748 : ℤ), (-11168745 : ℤ), (-7344563 : ℤ), (-7344560 : ℤ), (18703484 : ℤ), (18703487 : ℤ), (53497919 : ℤ), (53497922 : ℤ)⟩
    family.scaledA1UpperBound (23 : ℤ) = (7 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewiseRows200To299Chunk001A1LowerBound003 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (28 : ℤ), (23 : ℤ), (23 : ℤ), (16777216 : ℤ), (-15865899 : ℤ), (-15865896 : ℤ), (-14096424 : ℤ), (-14096421 : ℤ), (-6439395 : ℤ), (-6439392 : ℤ), (18917277 : ℤ), (18917280 : ℤ), (53435611 : ℤ), (53435614 : ℤ)⟩
    family.scaledA1LowerBound (23 : ℤ) = (7 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewiseRows200To299Chunk001A1UpperBound003 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (28 : ℤ), (23 : ℤ), (23 : ℤ), (16777216 : ℤ), (-15865899 : ℤ), (-15865896 : ℤ), (-14096424 : ℤ), (-14096421 : ℤ), (-6439395 : ℤ), (-6439392 : ℤ), (18917277 : ℤ), (18917280 : ℤ), (53435611 : ℤ), (53435614 : ℤ)⟩
    family.scaledA1UpperBound (23 : ℤ) = (6 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewiseRows200To299Chunk001A1LowerBound004 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (28 : ℤ), (24 : ℤ), (24 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-12586779 : ℤ), (-12586776 : ℤ), (-7093878 : ℤ), (-7093875 : ℤ), (18979980 : ℤ), (18979983 : ℤ), (53429064 : ℤ), (53429067 : ℤ)⟩
    family.scaledA1LowerBound (24 : ℤ) = (8 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewiseRows200To299Chunk001A1UpperBound004 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (28 : ℤ), (24 : ℤ), (24 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-12586779 : ℤ), (-12586776 : ℤ), (-7093878 : ℤ), (-7093875 : ℤ), (18979980 : ℤ), (18979983 : ℤ), (53429064 : ℤ), (53429067 : ℤ)⟩
    family.scaledA1UpperBound (24 : ℤ) = (8 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewiseRows200To299Chunk001A1LowerBound005 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (28 : ℤ), (25 : ℤ), (25 : ℤ), (16777216 : ℤ), (-17291535 : ℤ), (-17291532 : ℤ), (-11163855 : ℤ), (-11163852 : ℤ), (-8058096 : ℤ), (-8058093 : ℤ), (19042145 : ℤ), (19042148 : ℤ), (53422511 : ℤ), (53422514 : ℤ)⟩
    family.scaledA1LowerBound (25 : ℤ) = (10 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewiseRows200To299Chunk001A1UpperBound005 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (28 : ℤ), (25 : ℤ), (25 : ℤ), (16777216 : ℤ), (-17291535 : ℤ), (-17291532 : ℤ), (-11163855 : ℤ), (-11163852 : ℤ), (-8058096 : ℤ), (-8058093 : ℤ), (19042145 : ℤ), (19042148 : ℤ), (53422511 : ℤ), (53422514 : ℤ)⟩
    family.scaledA1UpperBound (25 : ℤ) = (9 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewiseRows200To299Chunk001A1LowerBound006 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (29 : ℤ), (26 : ℤ), (26 : ℤ), (16777216 : ℤ), (-16047316 : ℤ), (-16047313 : ℤ), (-13027448 : ℤ), (-13027445 : ℤ), (-7639900 : ℤ), (-7639897 : ℤ), (19312793 : ℤ), (19312796 : ℤ), (53353040 : ℤ), (53353043 : ℤ)⟩
    family.scaledA1LowerBound (26 : ℤ) = (9 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewiseRows200To299Chunk001A1UpperBound006 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (29 : ℤ), (26 : ℤ), (26 : ℤ), (16777216 : ℤ), (-16047316 : ℤ), (-16047313 : ℤ), (-13027448 : ℤ), (-13027445 : ℤ), (-7639900 : ℤ), (-7639897 : ℤ), (19312793 : ℤ), (19312796 : ℤ), (53353040 : ℤ), (53353043 : ℤ)⟩
    family.scaledA1UpperBound (26 : ℤ) = (9 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewiseRows200To299Chunk001A1LowerBound007 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (29 : ℤ), (27 : ℤ), (27 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-11154640 : ℤ), (-11154637 : ℤ), (-8836273 : ℤ), (-8836270 : ℤ), (19372880 : ℤ), (19372883 : ℤ), (53346419 : ℤ), (53346422 : ℤ)⟩
    family.scaledA1LowerBound (27 : ℤ) = (11 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewiseRows200To299Chunk001A1UpperBound007 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (29 : ℤ), (27 : ℤ), (27 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-11154640 : ℤ), (-11154637 : ℤ), (-8836273 : ℤ), (-8836270 : ℤ), (19372880 : ℤ), (19372883 : ℤ), (53346419 : ℤ), (53346422 : ℤ)⟩
    family.scaledA1UpperBound (27 : ℤ) = (10 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewiseRows200To299Chunk001A1LowerBound008 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (30 : ℤ), (29 : ℤ), (29 : ℤ), (16777216 : ℤ), (-16154658 : ℤ), (-16154655 : ℤ), (-11130524 : ℤ), (-11130521 : ℤ), (-9729676 : ℤ), (-9729673 : ℤ), (19696399 : ℤ), (19696402 : ℤ), (53269629 : ℤ), (53269632 : ℤ)⟩
    family.scaledA1LowerBound (29 : ℤ) = (12 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewiseRows200To299Chunk001A1UpperBound008 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (30 : ℤ), (29 : ℤ), (29 : ℤ), (16777216 : ℤ), (-16154658 : ℤ), (-16154655 : ℤ), (-11130524 : ℤ), (-11130521 : ℤ), (-9729676 : ℤ), (-9729673 : ℤ), (19696399 : ℤ), (19696402 : ℤ), (53269629 : ℤ), (53269632 : ℤ)⟩
    family.scaledA1UpperBound (29 : ℤ) = (11 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewiseRows200To299Chunk001A1LowerBound009 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (32 : ℤ), (33 : ℤ), (33 : ℤ), (16777216 : ℤ), (-13537683 : ℤ), (-13537680 : ℤ), (-12652750 : ℤ), (-12652747 : ℤ), (-11296486 : ℤ), (-11296483 : ℤ), (20324202 : ℤ), (20324205 : ℤ), (53113887 : ℤ), (53113890 : ℤ)⟩
    family.scaledA1LowerBound (33 : ℤ) = (15 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewiseRows200To299Chunk001A1UpperBound009 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (32 : ℤ), (33 : ℤ), (33 : ℤ), (16777216 : ℤ), (-13537683 : ℤ), (-13537680 : ℤ), (-12652750 : ℤ), (-12652747 : ℤ), (-11296486 : ℤ), (-11296483 : ℤ), (20324202 : ℤ), (20324205 : ℤ), (53113887 : ℤ), (53113890 : ℤ)⟩
    family.scaledA1UpperBound (33 : ℤ) = (14 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewiseRows200To299Chunk001A1LowerBound010 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), (16777216 : ℤ), (-25763314 : ℤ), (-25763311 : ℤ), (-2 : ℤ), (2 : ℤ), (1496732 : ℤ), (1496735 : ℤ), (5349512 : ℤ), (5349515 : ℤ), (54868241 : ℤ), (54868244 : ℤ)⟩
    family.scaledA1LowerBound (0 : ℤ) = (0 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewiseRows200To299Chunk001A1UpperBound010 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), (16777216 : ℤ), (-25763314 : ℤ), (-25763311 : ℤ), (-2 : ℤ), (2 : ℤ), (1496732 : ℤ), (1496735 : ℤ), (5349512 : ℤ), (5349515 : ℤ), (54868241 : ℤ), (54868244 : ℤ)⟩
    family.scaledA1UpperBound (0 : ℤ) = (0 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewiseRows200To299Chunk001A1LowerBound011 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (0 : ℤ), (-1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-25558195 : ℤ), (-25558192 : ℤ), (-2295499 : ℤ), (-2295496 : ℤ), (3785270 : ℤ), (3785273 : ℤ), (5199164 : ℤ), (5199167 : ℤ), (54820429 : ℤ), (54820432 : ℤ)⟩
    family.scaledA1LowerBound (-1 : ℤ) = (1 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewiseRows200To299Chunk001A1UpperBound011 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (0 : ℤ), (-1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-25558195 : ℤ), (-25558192 : ℤ), (-2295499 : ℤ), (-2295496 : ℤ), (3785270 : ℤ), (3785273 : ℤ), (5199164 : ℤ), (5199167 : ℤ), (54820429 : ℤ), (54820432 : ℤ)⟩
    family.scaledA1UpperBound (-1 : ℤ) = (0 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewiseRows200To299Chunk001A1LowerBound012 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (1 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-25422976 : ℤ), (-25384280 : ℤ), (-2751882 : ℤ), (-1059624 : ℤ), (-2 : ℤ), (2385889 : ℤ), (6934536 : ℤ), (7672345 : ℤ), (54761431 : ℤ), (54766916 : ℤ)⟩
    family.scaledA1LowerBound (-1 : ℤ) = (0 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewiseRows200To299Chunk001A1UpperBound012 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (1 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-25422976 : ℤ), (-25384280 : ℤ), (-2751882 : ℤ), (-1059624 : ℤ), (-2 : ℤ), (2385889 : ℤ), (6934536 : ℤ), (7672345 : ℤ), (54761431 : ℤ), (54766916 : ℤ)⟩
    family.scaledA1UpperBound (-1 : ℤ) = (0 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewiseRows200To299Chunk001A1LowerBound013 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (1 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-25422976 : ℤ), (-25384280 : ℤ), (-2751882 : ℤ), (-1059624 : ℤ), (-2 : ℤ), (2385889 : ℤ), (6934536 : ℤ), (7672345 : ℤ), (54761431 : ℤ), (54766916 : ℤ)⟩
    family.scaledA1LowerBound (0 : ℤ) = (0 : ℤ) := by
  rfl

@[simp] theorem degreeSevenStageSixPiecewiseRows200To299Chunk001A1UpperBound013 :
    let family : DegreeSevenStageSixScaledFamily :=
      ⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (1 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-25422976 : ℤ), (-25384280 : ℤ), (-2751882 : ℤ), (-1059624 : ℤ), (-2 : ℤ), (2385889 : ℤ), (6934536 : ℤ), (7672345 : ℤ), (54761431 : ℤ), (54766916 : ℤ)⟩
    family.scaledA1UpperBound (0 : ℤ) = (0 : ℤ) := by
  rfl

def degreeSevenStageSixPiecewiseRows200To299Chunk001CoarseCoverages :
    List DegreeSevenStageSixStrongCompactCoverage :=
  degreeSevenStageSixPiecewiseRows200To299Chunk001.map
    DegreeSevenStageSixPiecewiseCoverage.coverage

def degreeSevenStageSixPiecewiseRows200To299Chunk001Edges :
    List DegreeSevenStageSixMultipleRootWitness :=
  degreeSevenStageSixPiecewiseRows200To299Chunk001CoarseCoverages.flatMap
    DegreeSevenStageSixStrongCompactCoverage.edgeRejections

theorem degreeSevenStageSixPiecewiseRows200To299Chunk001Skeletons_valid :
    degreeSevenStageSixPiecewiseRows200To299Chunk001CoarseCoverages.Forall
      DegreeSevenStageSixStrongCompactCoverage.SkeletonValid := by
  decide

theorem degreeSevenStageSixPiecewiseRows200To299Chunk001Edges_valid :
    degreeSevenStageSixPiecewiseRows200To299Chunk001Edges.Forall
      DegreeSevenStageSixMultipleRootWitness.Valid := by
  norm_num [degreeSevenStageSixPiecewiseRows200To299Chunk001Edges,
    degreeSevenStageSixPiecewiseRows200To299Chunk001CoarseCoverages,
    degreeSevenStageSixPiecewiseRows200To299Chunk001,
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

theorem degreeSevenStageSixPiecewiseRows200To299Chunk001CoarseCoverages_valid :
    degreeSevenStageSixPiecewiseRows200To299Chunk001CoarseCoverages.Forall
      DegreeSevenStageSixStrongCompactCoverage.Valid := by
  apply List.Forall.imp
    DegreeSevenStageSixStrongCompactCoverage.valid_of_arithmeticValid
  apply
    DegreeSevenStageSixStrongCompactCoverage.list_forall_arithmeticValid_of_skeletons_and_edges
  · exact degreeSevenStageSixPiecewiseRows200To299Chunk001Skeletons_valid
  · exact degreeSevenStageSixPiecewiseRows200To299Chunk001Edges_valid

theorem degreeSevenStageSixPiecewiseRows200To299Chunk001Pieces_valid :
    degreeSevenStageSixPiecewiseRows200To299Chunk001.Forall
      DegreeSevenStageSixPiecewiseCoverage.PiecesValid := by
  decide

theorem degreeSevenStageSixPiecewiseRows200To299Chunk001_valid :
    degreeSevenStageSixPiecewiseRows200To299Chunk001.Forall
      DegreeSevenStageSixPiecewiseCoverage.Valid := by
  apply DegreeSevenStageSixPiecewiseCoverage.list_forall_valid_of_parts
  · exact degreeSevenStageSixPiecewiseRows200To299Chunk001CoarseCoverages_valid
  · exact degreeSevenStageSixPiecewiseRows200To299Chunk001Pieces_valid

end

end TraceEuclidean
