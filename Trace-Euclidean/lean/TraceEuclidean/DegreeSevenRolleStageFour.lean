import TraceEuclidean.DegreeSevenRolleStageThree
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk000
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk001
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk002
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk003
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk004
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk005
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk006
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk007
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk008
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk009
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk010
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk011
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk012
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk013
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk014
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk015
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk016
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk017
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk018
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk019
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk020
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk021
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk022
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk023
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk024
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk025
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk026
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk027
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk028
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk029
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk030
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk031
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk032
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk033
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk034
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk035
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk036
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk037
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk038
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk039
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk040
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk041
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk042
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk043
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk044
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk045
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk046
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk047
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk048
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk049
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk050
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk051
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk052
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk053
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk054
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk055
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk056
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk057
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk058
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk059
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk060
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk061
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk062
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk063
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk064
import TraceEuclidean.DegreeSevenRolleStageFourCertificates.Chunk065

/-! Complete generated fourth-stage frontier for the septic Rolle search. -/

namespace TraceEuclidean

noncomputable section

/-- One quadratic parent row together with the simple and multiple-root
values in its exact next-coefficient interval. -/
structure DegreeSevenStageFourCoverage where
  parent : DegreeSevenStageThreeEntry
  surviving : List ℤ
  rejected : List ℤ
deriving DecidableEq, Repr

namespace DegreeSevenStageFourCoverage

def Valid (coverage : DegreeSevenStageFourCoverage) : Prop :=
  coverage.parent.a4Candidates =
    coverage.surviving.toFinset ∪ coverage.rejected.toFinset

end DegreeSevenStageFourCoverage

def degreeSevenStageFourCoverage000 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-3 : ℤ), (-9 : ℤ), ⟨(-40 : ℚ) / 113, (-23 : ℚ) / 65⟩, ⟨(132 : ℚ) / 109, (109 : ℚ) / 90⟩⟩, [(-8 : ℤ), (-7 : ℤ), (-6 : ℤ), (-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ), (18 : ℤ), (19 : ℤ), (20 : ℤ), (21 : ℤ), (22 : ℤ), (23 : ℤ), (24 : ℤ), (25 : ℤ), (26 : ℤ), (27 : ℤ), (28 : ℤ), (29 : ℤ), (30 : ℤ), (31 : ℤ), (32 : ℤ), (33 : ℤ), (34 : ℤ), (35 : ℤ), (36 : ℤ), (37 : ℤ), (38 : ℤ), (39 : ℤ), (40 : ℤ), (41 : ℤ), (42 : ℤ), (43 : ℤ), (44 : ℤ), (45 : ℤ), (46 : ℤ), (47 : ℤ), (48 : ℤ), (49 : ℤ), (50 : ℤ), (51 : ℤ), (52 : ℤ), (53 : ℤ), (54 : ℤ), (55 : ℤ), (56 : ℤ), (57 : ℤ), (58 : ℤ)], []⟩

def degreeSevenStageFourCoverage001 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-3 : ℤ), (-8 : ℤ), ⟨(-31 : ℚ) / 96, (-41 : ℚ) / 127⟩, ⟨(105 : ℚ) / 89, (59 : ℚ) / 50⟩⟩, [(-7 : ℤ), (-6 : ℤ), (-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ), (18 : ℤ), (19 : ℤ), (20 : ℤ), (21 : ℤ), (22 : ℤ), (23 : ℤ), (24 : ℤ), (25 : ℤ), (26 : ℤ), (27 : ℤ), (28 : ℤ), (29 : ℤ), (30 : ℤ), (31 : ℤ), (32 : ℤ), (33 : ℤ), (34 : ℤ), (35 : ℤ), (36 : ℤ), (37 : ℤ), (38 : ℤ), (39 : ℤ), (40 : ℤ), (41 : ℤ), (42 : ℤ), (43 : ℤ), (44 : ℤ), (45 : ℤ), (46 : ℤ), (47 : ℤ), (48 : ℤ), (49 : ℤ), (50 : ℤ), (51 : ℤ), (52 : ℤ)], []⟩

def degreeSevenStageFourCoverage002 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-3 : ℤ), (-7 : ℤ), ⟨(-52 : ℚ) / 179, (-9 : ℚ) / 31⟩, ⟨(70 : ℚ) / 61, (101 : ℚ) / 88⟩⟩, [(-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ), (18 : ℤ), (19 : ℤ), (20 : ℤ), (21 : ℤ), (22 : ℤ), (23 : ℤ), (24 : ℤ), (25 : ℤ), (26 : ℤ), (27 : ℤ), (28 : ℤ), (29 : ℤ), (30 : ℤ), (31 : ℤ), (32 : ℤ), (33 : ℤ), (34 : ℤ), (35 : ℤ), (36 : ℤ), (37 : ℤ), (38 : ℤ), (39 : ℤ), (40 : ℤ), (41 : ℤ), (42 : ℤ), (43 : ℤ), (44 : ℤ), (45 : ℤ), (46 : ℤ)], []⟩

def degreeSevenStageFourCoverage003 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-3 : ℤ), (-6 : ℤ), ⟨(-39 : ℚ) / 152, (-10 : ℚ) / 39⟩, ⟨(49 : ℚ) / 44, (186 : ℚ) / 167⟩⟩, [(-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ), (18 : ℤ), (19 : ℤ), (20 : ℤ), (21 : ℤ), (22 : ℤ), (23 : ℤ), (24 : ℤ), (25 : ℤ), (26 : ℤ), (27 : ℤ), (28 : ℤ), (29 : ℤ), (30 : ℤ), (31 : ℤ), (32 : ℤ), (33 : ℤ), (34 : ℤ), (35 : ℤ), (36 : ℤ), (37 : ℤ), (38 : ℤ), (39 : ℤ), (40 : ℤ)], []⟩

def degreeSevenStageFourCoverage004 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-3 : ℤ), (-5 : ℤ), ⟨(-19 : ℚ) / 86, (-17 : ℚ) / 77⟩, ⟨(83 : ℚ) / 77, (69 : ℚ) / 64⟩⟩, [(-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ), (18 : ℤ), (19 : ℤ), (20 : ℤ), (21 : ℤ), (22 : ℤ), (23 : ℤ), (24 : ℤ), (25 : ℤ), (26 : ℤ), (27 : ℤ), (28 : ℤ), (29 : ℤ), (30 : ℤ), (31 : ℤ), (32 : ℤ), (33 : ℤ), (34 : ℤ), (35 : ℤ)], []⟩

def degreeSevenStageFourCoverage005 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-3 : ℤ), (-4 : ℤ), ⟨(-11 : ℚ) / 60, (-13 : ℚ) / 71⟩, ⟨(181 : ℚ) / 174, (155 : ℚ) / 149⟩⟩, [(-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ), (18 : ℤ), (19 : ℤ), (20 : ℤ), (21 : ℤ), (22 : ℤ), (23 : ℤ), (24 : ℤ), (25 : ℤ), (26 : ℤ), (27 : ℤ), (28 : ℤ), (29 : ℤ), (30 : ℤ)], []⟩

def degreeSevenStageFourCoverage006 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-3 : ℤ), (-3 : ℤ), ⟨(-4103 : ℚ) / 28672, (-4089 : ℚ) / 28672⟩, ⟨(4095 : ℚ) / 4096, (4097 : ℚ) / 4096⟩⟩, [(-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ), (18 : ℤ), (19 : ℤ), (20 : ℤ), (21 : ℤ), (22 : ℤ), (23 : ℤ), (24 : ℤ)], [(25 : ℤ)]⟩

def degreeSevenStageFourCoverage007 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-3 : ℤ), (-2 : ℤ), ⟨(-23 : ℚ) / 231, (-22 : ℚ) / 221⟩, ⟨(22 : ℚ) / 23, (199 : ℚ) / 208⟩⟩, [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ), (18 : ℤ), (19 : ℤ), (20 : ℤ)], []⟩

def degreeSevenStageFourCoverage008 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-3 : ℤ), (-1 : ℤ), ⟨(-11 : ℚ) / 210, (-10 : ℚ) / 191⟩, ⟨(211 : ℚ) / 232, (201 : ℚ) / 221⟩⟩, [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ)], []⟩

def degreeSevenStageFourCoverage009 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-3 : ℤ), (0 : ℤ), ⟨(-1 : ℚ) / 4096, (1 : ℚ) / 4096⟩, ⟨(24569 : ℚ) / 28672, (24583 : ℚ) / 28672⟩⟩, [(1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ)], [(0 : ℤ)]⟩

def degreeSevenStageFourCoverage010 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-3 : ℤ), (1 : ℤ), ⟨(4 : ℚ) / 67, (7 : ℚ) / 117⟩, ⟨(59 : ℚ) / 74, (63 : ℚ) / 79⟩⟩, [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ)], []⟩

def degreeSevenStageFourCoverage011 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-3 : ℤ), (2 : ℤ), ⟨(8 : ℚ) / 61, (13 : ℚ) / 99⟩, ⟨(45 : ℚ) / 62, (53 : ℚ) / 73⟩⟩, [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ)], []⟩

def degreeSevenStageFourCoverage012 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-3 : ℤ), (3 : ℤ), ⟨(12 : ℚ) / 53, (29 : ℚ) / 128⟩, ⟨(29 : ℚ) / 46, (70 : ℚ) / 111⟩⟩, [(-1 : ℤ)], []⟩

def degreeSevenStageFourCoverage013 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-2 : ℤ), (-12 : ℤ), ⟨(-58 : ℚ) / 111, (-35 : ℚ) / 67⟩, ⟨(35 : ℚ) / 32, (163 : ℚ) / 149⟩⟩, [(-18 : ℤ), (-17 : ℤ), (-16 : ℤ), (-15 : ℤ), (-14 : ℤ), (-13 : ℤ), (-12 : ℤ), (-11 : ℤ), (-10 : ℤ), (-9 : ℤ), (-8 : ℤ), (-7 : ℤ), (-6 : ℤ), (-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ), (18 : ℤ), (19 : ℤ), (20 : ℤ), (21 : ℤ), (22 : ℤ), (23 : ℤ), (24 : ℤ), (25 : ℤ), (26 : ℤ), (27 : ℤ), (28 : ℤ), (29 : ℤ), (30 : ℤ), (31 : ℤ), (32 : ℤ), (33 : ℤ), (34 : ℤ), (35 : ℤ), (36 : ℤ), (37 : ℤ), (38 : ℤ), (39 : ℤ), (40 : ℤ), (41 : ℤ), (42 : ℤ), (43 : ℤ), (44 : ℤ), (45 : ℤ), (46 : ℤ), (47 : ℤ), (48 : ℤ), (49 : ℤ), (50 : ℤ), (51 : ℤ), (52 : ℤ), (53 : ℤ), (54 : ℤ), (55 : ℤ)], []⟩

def degreeSevenStageFourCoverage014 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-2 : ℤ), (-11 : ℤ), ⟨(-33 : ℚ) / 67, (-32 : ℚ) / 65⟩, ⟨(317 : ℚ) / 298, (50 : ℚ) / 47⟩⟩, [(-15 : ℤ), (-14 : ℤ), (-13 : ℤ), (-12 : ℤ), (-11 : ℤ), (-10 : ℤ), (-9 : ℤ), (-8 : ℤ), (-7 : ℤ), (-6 : ℤ), (-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ), (18 : ℤ), (19 : ℤ), (20 : ℤ), (21 : ℤ), (22 : ℤ), (23 : ℤ), (24 : ℤ), (25 : ℤ), (26 : ℤ), (27 : ℤ), (28 : ℤ), (29 : ℤ), (30 : ℤ), (31 : ℤ), (32 : ℤ), (33 : ℤ), (34 : ℤ), (35 : ℤ), (36 : ℤ), (37 : ℤ), (38 : ℤ), (39 : ℤ), (40 : ℤ), (41 : ℤ), (42 : ℤ), (43 : ℤ), (44 : ℤ), (45 : ℤ), (46 : ℤ), (47 : ℤ), (48 : ℤ), (49 : ℤ), (50 : ℤ)], []⟩

def degreeSevenStageFourCoverage015 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-2 : ℤ), (-10 : ℤ), ⟨(-95 : ℚ) / 206, (-89 : ℚ) / 193⟩, ⟨(127 : ℚ) / 123, (95 : ℚ) / 92⟩⟩, [(-13 : ℤ), (-12 : ℤ), (-11 : ℤ), (-10 : ℤ), (-9 : ℤ), (-8 : ℤ), (-7 : ℤ), (-6 : ℤ), (-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ), (18 : ℤ), (19 : ℤ), (20 : ℤ), (21 : ℤ), (22 : ℤ), (23 : ℤ), (24 : ℤ), (25 : ℤ), (26 : ℤ), (27 : ℤ), (28 : ℤ), (29 : ℤ), (30 : ℤ), (31 : ℤ), (32 : ℤ), (33 : ℤ), (34 : ℤ), (35 : ℤ), (36 : ℤ), (37 : ℤ), (38 : ℤ), (39 : ℤ), (40 : ℤ), (41 : ℤ), (42 : ℤ), (43 : ℤ), (44 : ℤ), (45 : ℤ)], []⟩

def degreeSevenStageFourCoverage016 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-2 : ℤ), (-9 : ℤ), ⟨(-12295 : ℚ) / 28672, (-12281 : ℚ) / 28672⟩, ⟨(4095 : ℚ) / 4096, (4097 : ℚ) / 4096⟩⟩, [(-11 : ℤ), (-10 : ℤ), (-9 : ℤ), (-8 : ℤ), (-7 : ℤ), (-6 : ℤ), (-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ), (18 : ℤ), (19 : ℤ), (20 : ℤ), (21 : ℤ), (22 : ℤ), (23 : ℤ), (24 : ℤ), (25 : ℤ), (26 : ℤ), (27 : ℤ), (28 : ℤ), (29 : ℤ), (30 : ℤ), (31 : ℤ), (32 : ℤ), (33 : ℤ), (34 : ℤ), (35 : ℤ), (36 : ℤ), (37 : ℤ), (38 : ℤ), (39 : ℤ)], [(40 : ℤ)]⟩

def degreeSevenStageFourCoverage017 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-2 : ℤ), (-8 : ℤ), ⟨(-43 : ℚ) / 109, (-28 : ℚ) / 71⟩, ⟨(113 : ℚ) / 117, (85 : ℚ) / 88⟩⟩, [(-8 : ℤ), (-7 : ℤ), (-6 : ℤ), (-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ), (18 : ℤ), (19 : ℤ), (20 : ℤ), (21 : ℤ), (22 : ℤ), (23 : ℤ), (24 : ℤ), (25 : ℤ), (26 : ℤ), (27 : ℤ), (28 : ℤ), (29 : ℤ), (30 : ℤ), (31 : ℤ), (32 : ℤ), (33 : ℤ), (34 : ℤ), (35 : ℤ)], []⟩

def degreeSevenStageFourCoverage018 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-2 : ℤ), (-7 : ℤ), ⟨(-19 : ℚ) / 53, (-81 : ℚ) / 226⟩, ⟨(53 : ℚ) / 57, (93 : ℚ) / 100⟩⟩, [(-7 : ℤ), (-6 : ℤ), (-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ), (18 : ℤ), (19 : ℤ), (20 : ℤ), (21 : ℤ), (22 : ℤ), (23 : ℤ), (24 : ℤ), (25 : ℤ), (26 : ℤ), (27 : ℤ), (28 : ℤ), (29 : ℤ), (30 : ℤ)], []⟩

def degreeSevenStageFourCoverage019 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-2 : ℤ), (-6 : ℤ), ⟨(-33 : ℚ) / 103, (-41 : ℚ) / 128⟩, ⟨(107 : ℚ) / 120, (33 : ℚ) / 37⟩⟩, [(-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ), (18 : ℤ), (19 : ℤ), (20 : ℤ), (21 : ℤ), (22 : ℤ), (23 : ℤ), (24 : ℤ), (25 : ℤ)], []⟩

def degreeSevenStageFourCoverage020 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-2 : ℤ), (-5 : ℤ), ⟨(-47 : ℚ) / 168, (-40 : ℚ) / 143⟩, ⟨(40 : ℚ) / 47, (143 : ℚ) / 168⟩⟩, [(-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ), (18 : ℤ), (19 : ℤ), (20 : ℤ), (21 : ℤ)], []⟩

def degreeSevenStageFourCoverage021 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-2 : ℤ), (-4 : ℤ), ⟨(-21 : ℚ) / 89, (-25 : ℚ) / 106⟩, ⟨(88 : ℚ) / 109, (109 : ℚ) / 135⟩⟩, [(-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ)], []⟩

def degreeSevenStageFourCoverage022 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-2 : ℤ), (-3 : ℤ), ⟨(-19 : ℚ) / 101, (-22 : ℚ) / 117⟩, ⟨(60 : ℚ) / 79, (79 : ℚ) / 104⟩⟩, [(-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ)], []⟩

def degreeSevenStageFourCoverage023 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-2 : ℤ), (-2 : ℤ), ⟨(-17 : ℚ) / 126, (-12 : ℚ) / 89⟩, ⟨(113 : ℚ) / 160, (101 : ℚ) / 143⟩⟩, [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ)], []⟩

def degreeSevenStageFourCoverage024 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-2 : ℤ), (-1 : ℤ), ⟨(-11 : ℚ) / 149, (-9 : ℚ) / 122⟩, ⟨(20 : ℚ) / 31, (91 : ℚ) / 141⟩⟩, [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ)], []⟩

def degreeSevenStageFourCoverage025 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-2 : ℤ), (0 : ℤ), ⟨(-1 : ℚ) / 4096, (1 : ℚ) / 4096⟩, ⟨(16377 : ℚ) / 28672, (16391 : ℚ) / 28672⟩⟩, [(1 : ℤ), (2 : ℤ), (3 : ℤ)], [(0 : ℤ)]⟩

def degreeSevenStageFourCoverage026 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-2 : ℤ), (1 : ℤ), ⟨(8 : ℚ) / 79, (7 : ℚ) / 69⟩, ⟨(55 : ℚ) / 117, (63 : ℚ) / 134⟩⟩, [(0 : ℤ)], []⟩

def degreeSevenStageFourCoverage027 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-1 : ℤ), (-13 : ℤ), ⟨(-67 : ℚ) / 102, (-44 : ℚ) / 67⟩, ⟨(49 : ℚ) / 52, (82 : ℚ) / 87⟩⟩, [(-26 : ℤ), (-25 : ℤ), (-24 : ℤ), (-23 : ℤ), (-22 : ℤ), (-21 : ℤ), (-20 : ℤ), (-19 : ℤ), (-18 : ℤ), (-17 : ℤ), (-16 : ℤ), (-15 : ℤ), (-14 : ℤ), (-13 : ℤ), (-12 : ℤ), (-11 : ℤ), (-10 : ℤ), (-9 : ℤ), (-8 : ℤ), (-7 : ℤ), (-6 : ℤ), (-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ), (18 : ℤ), (19 : ℤ), (20 : ℤ), (21 : ℤ), (22 : ℤ), (23 : ℤ), (24 : ℤ), (25 : ℤ), (26 : ℤ), (27 : ℤ), (28 : ℤ), (29 : ℤ), (30 : ℤ), (31 : ℤ), (32 : ℤ), (33 : ℤ), (34 : ℤ), (35 : ℤ), (36 : ℤ), (37 : ℤ), (38 : ℤ), (39 : ℤ), (40 : ℤ), (41 : ℤ), (42 : ℤ), (43 : ℤ), (44 : ℤ), (45 : ℤ)], []⟩

def degreeSevenStageFourCoverage028 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-1 : ℤ), (-12 : ℤ), ⟨(-52 : ℚ) / 83, (-57 : ℚ) / 91⟩, ⟨(83 : ℚ) / 91, (52 : ℚ) / 57⟩⟩, [(-23 : ℤ), (-22 : ℤ), (-21 : ℤ), (-20 : ℤ), (-19 : ℤ), (-18 : ℤ), (-17 : ℤ), (-16 : ℤ), (-15 : ℤ), (-14 : ℤ), (-13 : ℤ), (-12 : ℤ), (-11 : ℤ), (-10 : ℤ), (-9 : ℤ), (-8 : ℤ), (-7 : ℤ), (-6 : ℤ), (-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ), (18 : ℤ), (19 : ℤ), (20 : ℤ), (21 : ℤ), (22 : ℤ), (23 : ℤ), (24 : ℤ), (25 : ℤ), (26 : ℤ), (27 : ℤ), (28 : ℤ), (29 : ℤ), (30 : ℤ), (31 : ℤ), (32 : ℤ), (33 : ℤ), (34 : ℤ), (35 : ℤ), (36 : ℤ), (37 : ℤ), (38 : ℤ), (39 : ℤ), (40 : ℤ)], []⟩

def degreeSevenStageFourCoverage029 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-1 : ℤ), (-11 : ℤ), ⟨(-47 : ℚ) / 79, (-69 : ℚ) / 116⟩, ⟨(81 : ℚ) / 92, (59 : ℚ) / 67⟩⟩, [(-20 : ℤ), (-19 : ℤ), (-18 : ℤ), (-17 : ℤ), (-16 : ℤ), (-15 : ℤ), (-14 : ℤ), (-13 : ℤ), (-12 : ℤ), (-11 : ℤ), (-10 : ℤ), (-9 : ℤ), (-8 : ℤ), (-7 : ℤ), (-6 : ℤ), (-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ), (18 : ℤ), (19 : ℤ), (20 : ℤ), (21 : ℤ), (22 : ℤ), (23 : ℤ), (24 : ℤ), (25 : ℤ), (26 : ℤ), (27 : ℤ), (28 : ℤ), (29 : ℤ), (30 : ℤ), (31 : ℤ), (32 : ℤ), (33 : ℤ), (34 : ℤ), (35 : ℤ), (36 : ℤ)], []⟩

def degreeSevenStageFourCoverage030 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-1 : ℤ), (-10 : ℤ), ⟨(-59 : ℚ) / 105, (-50 : ℚ) / 89⟩, ⟨(50 : ℚ) / 59, (89 : ℚ) / 105⟩⟩, [(-17 : ℤ), (-16 : ℤ), (-15 : ℤ), (-14 : ℤ), (-13 : ℤ), (-12 : ℤ), (-11 : ℤ), (-10 : ℤ), (-9 : ℤ), (-8 : ℤ), (-7 : ℤ), (-6 : ℤ), (-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ), (18 : ℤ), (19 : ℤ), (20 : ℤ), (21 : ℤ), (22 : ℤ), (23 : ℤ), (24 : ℤ), (25 : ℤ), (26 : ℤ), (27 : ℤ), (28 : ℤ), (29 : ℤ), (30 : ℤ), (31 : ℤ)], []⟩

def degreeSevenStageFourCoverage031 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-1 : ℤ), (-9 : ℤ), ⟨(-29 : ℚ) / 55, (-97 : ℚ) / 184⟩, ⟨(126 : ℚ) / 155, (113 : ℚ) / 139⟩⟩, [(-14 : ℤ), (-13 : ℤ), (-12 : ℤ), (-11 : ℤ), (-10 : ℤ), (-9 : ℤ), (-8 : ℤ), (-7 : ℤ), (-6 : ℤ), (-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ), (18 : ℤ), (19 : ℤ), (20 : ℤ), (21 : ℤ), (22 : ℤ), (23 : ℤ), (24 : ℤ), (25 : ℤ), (26 : ℤ), (27 : ℤ)], []⟩

def degreeSevenStageFourCoverage032 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-1 : ℤ), (-8 : ℤ), ⟨(-53 : ℚ) / 108, (-26 : ℚ) / 53⟩, ⟨(59 : ℚ) / 76, (66 : ℚ) / 85⟩⟩, [(-11 : ℤ), (-10 : ℤ), (-9 : ℤ), (-8 : ℤ), (-7 : ℤ), (-6 : ℤ), (-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ), (18 : ℤ), (19 : ℤ), (20 : ℤ), (21 : ℤ), (22 : ℤ), (23 : ℤ)], []⟩

def degreeSevenStageFourCoverage033 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-1 : ℤ), (-7 : ℤ), ⟨(-47 : ℚ) / 104, (-61 : ℚ) / 135⟩, ⟨(59 : ℚ) / 80, (45 : ℚ) / 61⟩⟩, [(-9 : ℤ), (-8 : ℤ), (-7 : ℤ), (-6 : ℤ), (-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ), (18 : ℤ), (19 : ℤ)], []⟩

def degreeSevenStageFourCoverage034 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-1 : ℤ), (-6 : ℤ), ⟨(-55 : ℚ) / 134, (-16 : ℚ) / 39⟩, ⟨(71 : ℚ) / 102, (55 : ℚ) / 79⟩⟩, [(-7 : ℤ), (-6 : ℤ), (-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ)], []⟩

def degreeSevenStageFourCoverage035 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-1 : ℤ), (-5 : ℤ), ⟨(-34 : ℚ) / 93, (-19 : ℚ) / 52⟩, ⟨(28 : ℚ) / 43, (99 : ℚ) / 152⟩⟩, [(-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ)], []⟩

def degreeSevenStageFourCoverage036 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-1 : ℤ), (-4 : ℤ), ⟨(-25 : ℚ) / 79, (-31 : ℚ) / 98⟩, ⟨(59 : ℚ) / 98, (56 : ℚ) / 93⟩⟩, [(-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ)], []⟩

def degreeSevenStageFourCoverage037 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-1 : ℤ), (-3 : ℤ), ⟨(-29 : ℚ) / 111, (-35 : ℚ) / 134⟩, ⟨(35 : ℚ) / 64, (64 : ℚ) / 117⟩⟩, [(-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ)], []⟩

def degreeSevenStageFourCoverage038 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-1 : ℤ), (-2 : ℤ), ⟨(-15 : ℚ) / 76, (-14 : ℚ) / 71⟩, ⟨(14 : ℚ) / 29, (71 : ℚ) / 147⟩⟩, [(-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ)], []⟩

def degreeSevenStageFourCoverage039 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-1 : ℤ), (-1 : ℤ), ⟨(-21 : ℚ) / 178, (-23 : ℚ) / 195⟩, ⟨(44 : ℚ) / 109, (21 : ℚ) / 52⟩⟩, [(0 : ℤ), (1 : ℤ), (2 : ℤ)], []⟩

def degreeSevenStageFourCoverage040 : DegreeSevenStageFourCoverage :=
  ⟨⟨(-1 : ℤ), (0 : ℤ), ⟨(-1 : ℚ) / 4096, (1 : ℚ) / 4096⟩, ⟨(8185 : ℚ) / 28672, (8199 : ℚ) / 28672⟩⟩, [], [(0 : ℤ)]⟩

def degreeSevenStageFourCoverage041 : DegreeSevenStageFourCoverage :=
  ⟨⟨(0 : ℤ), (-13 : ℤ), ⟨(-48 : ℚ) / 61, (-59 : ℚ) / 75⟩, ⟨(59 : ℚ) / 75, (48 : ℚ) / 61⟩⟩, [(-34 : ℤ), (-33 : ℤ), (-32 : ℤ), (-31 : ℤ), (-30 : ℤ), (-29 : ℤ), (-28 : ℤ), (-27 : ℤ), (-26 : ℤ), (-25 : ℤ), (-24 : ℤ), (-23 : ℤ), (-22 : ℤ), (-21 : ℤ), (-20 : ℤ), (-19 : ℤ), (-18 : ℤ), (-17 : ℤ), (-16 : ℤ), (-15 : ℤ), (-14 : ℤ), (-13 : ℤ), (-12 : ℤ), (-11 : ℤ), (-10 : ℤ), (-9 : ℤ), (-8 : ℤ), (-7 : ℤ), (-6 : ℤ), (-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ), (18 : ℤ), (19 : ℤ), (20 : ℤ), (21 : ℤ), (22 : ℤ), (23 : ℤ), (24 : ℤ), (25 : ℤ), (26 : ℤ), (27 : ℤ), (28 : ℤ), (29 : ℤ), (30 : ℤ), (31 : ℤ), (32 : ℤ), (33 : ℤ), (34 : ℤ)], []⟩

def degreeSevenStageFourCoverage042 : DegreeSevenStageFourCoverage :=
  ⟨⟨(0 : ℤ), (-12 : ℤ), ⟨(-31 : ℚ) / 41, (-96 : ℚ) / 127⟩, ⟨(96 : ℚ) / 127, (31 : ℚ) / 41⟩⟩, [(-30 : ℤ), (-29 : ℤ), (-28 : ℤ), (-27 : ℤ), (-26 : ℤ), (-25 : ℤ), (-24 : ℤ), (-23 : ℤ), (-22 : ℤ), (-21 : ℤ), (-20 : ℤ), (-19 : ℤ), (-18 : ℤ), (-17 : ℤ), (-16 : ℤ), (-15 : ℤ), (-14 : ℤ), (-13 : ℤ), (-12 : ℤ), (-11 : ℤ), (-10 : ℤ), (-9 : ℤ), (-8 : ℤ), (-7 : ℤ), (-6 : ℤ), (-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ), (18 : ℤ), (19 : ℤ), (20 : ℤ), (21 : ℤ), (22 : ℤ), (23 : ℤ), (24 : ℤ), (25 : ℤ), (26 : ℤ), (27 : ℤ), (28 : ℤ), (29 : ℤ), (30 : ℤ)], []⟩

def degreeSevenStageFourCoverage043 : DegreeSevenStageFourCoverage :=
  ⟨⟨(0 : ℤ), (-11 : ℤ), ⟨(-76 : ℚ) / 105, (-55 : ℚ) / 76⟩, ⟨(55 : ℚ) / 76, (76 : ℚ) / 105⟩⟩, [(-26 : ℤ), (-25 : ℤ), (-24 : ℤ), (-23 : ℤ), (-22 : ℤ), (-21 : ℤ), (-20 : ℤ), (-19 : ℤ), (-18 : ℤ), (-17 : ℤ), (-16 : ℤ), (-15 : ℤ), (-14 : ℤ), (-13 : ℤ), (-12 : ℤ), (-11 : ℤ), (-10 : ℤ), (-9 : ℤ), (-8 : ℤ), (-7 : ℤ), (-6 : ℤ), (-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ), (18 : ℤ), (19 : ℤ), (20 : ℤ), (21 : ℤ), (22 : ℤ), (23 : ℤ), (24 : ℤ), (25 : ℤ), (26 : ℤ)], []⟩

def degreeSevenStageFourCoverage044 : DegreeSevenStageFourCoverage :=
  ⟨⟨(0 : ℤ), (-10 : ℤ), ⟨(-49 : ℚ) / 71, (-69 : ℚ) / 100⟩, ⟨(69 : ℚ) / 100, (49 : ℚ) / 71⟩⟩, [(-23 : ℤ), (-22 : ℤ), (-21 : ℤ), (-20 : ℤ), (-19 : ℤ), (-18 : ℤ), (-17 : ℤ), (-16 : ℤ), (-15 : ℤ), (-14 : ℤ), (-13 : ℤ), (-12 : ℤ), (-11 : ℤ), (-10 : ℤ), (-9 : ℤ), (-8 : ℤ), (-7 : ℤ), (-6 : ℤ), (-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ), (18 : ℤ), (19 : ℤ), (20 : ℤ), (21 : ℤ), (22 : ℤ), (23 : ℤ)], []⟩

def degreeSevenStageFourCoverage045 : DegreeSevenStageFourCoverage :=
  ⟨⟨(0 : ℤ), (-9 : ℤ), ⟨(-55 : ℚ) / 84, (-36 : ℚ) / 55⟩, ⟨(36 : ℚ) / 55, (55 : ℚ) / 84⟩⟩, [(-19 : ℤ), (-18 : ℤ), (-17 : ℤ), (-16 : ℤ), (-15 : ℤ), (-14 : ℤ), (-13 : ℤ), (-12 : ℤ), (-11 : ℤ), (-10 : ℤ), (-9 : ℤ), (-8 : ℤ), (-7 : ℤ), (-6 : ℤ), (-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ), (17 : ℤ), (18 : ℤ), (19 : ℤ)], []⟩

def degreeSevenStageFourCoverage046 : DegreeSevenStageFourCoverage :=
  ⟨⟨(0 : ℤ), (-8 : ℤ), ⟨(-50 : ℚ) / 81, (-79 : ℚ) / 128⟩, ⟨(79 : ℚ) / 128, (50 : ℚ) / 81⟩⟩, [(-16 : ℤ), (-15 : ℤ), (-14 : ℤ), (-13 : ℤ), (-12 : ℤ), (-11 : ℤ), (-10 : ℤ), (-9 : ℤ), (-8 : ℤ), (-7 : ℤ), (-6 : ℤ), (-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ)], []⟩

def degreeSevenStageFourCoverage047 : DegreeSevenStageFourCoverage :=
  ⟨⟨(0 : ℤ), (-7 : ℤ), ⟨(-41 : ℚ) / 71, (-56 : ℚ) / 97⟩, ⟨(56 : ℚ) / 97, (41 : ℚ) / 71⟩⟩, [(-13 : ℤ), (-12 : ℤ), (-11 : ℤ), (-10 : ℤ), (-9 : ℤ), (-8 : ℤ), (-7 : ℤ), (-6 : ℤ), (-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ)], []⟩

def degreeSevenStageFourCoverage048 : DegreeSevenStageFourCoverage :=
  ⟨⟨(0 : ℤ), (-6 : ℤ), ⟨(-54 : ℚ) / 101, (-31 : ℚ) / 58⟩, ⟨(31 : ℚ) / 58, (54 : ℚ) / 101⟩⟩, [(-10 : ℤ), (-9 : ℤ), (-8 : ℤ), (-7 : ℤ), (-6 : ℤ), (-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ)], []⟩

def degreeSevenStageFourCoverage049 : DegreeSevenStageFourCoverage :=
  ⟨⟨(0 : ℤ), (-5 : ℤ), ⟨(-61 : ℚ) / 125, (-20 : ℚ) / 41⟩, ⟨(20 : ℚ) / 41, (61 : ℚ) / 125⟩⟩, [(-8 : ℤ), (-7 : ℤ), (-6 : ℤ), (-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ)], []⟩

def degreeSevenStageFourCoverage050 : DegreeSevenStageFourCoverage :=
  ⟨⟨(0 : ℤ), (-4 : ℤ), ⟨(-79 : ℚ) / 181, (-24 : ℚ) / 55⟩, ⟨(24 : ℚ) / 55, (79 : ℚ) / 181⟩⟩, [(-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ)], []⟩

def degreeSevenStageFourCoverage051 : DegreeSevenStageFourCoverage :=
  ⟨⟨(0 : ℤ), (-3 : ℤ), ⟨(-31 : ℚ) / 82, (-48 : ℚ) / 127⟩, ⟨(48 : ℚ) / 127, (31 : ℚ) / 82⟩⟩, [(-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ)], []⟩

def degreeSevenStageFourCoverage052 : DegreeSevenStageFourCoverage :=
  ⟨⟨(0 : ℤ), (-2 : ℤ), ⟨(-25 : ℚ) / 81, (-29 : ℚ) / 94⟩, ⟨(29 : ℚ) / 94, (25 : ℚ) / 81⟩⟩, [(-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ)], []⟩

def degreeSevenStageFourCoverage053 : DegreeSevenStageFourCoverage :=
  ⟨⟨(0 : ℤ), (-1 : ℤ), ⟨(-19 : ℚ) / 87, (-12 : ℚ) / 55⟩, ⟨(12 : ℚ) / 55, (19 : ℚ) / 87⟩⟩, [(0 : ℤ)], []⟩

def degreeSevenStageFourCoverages :
    List DegreeSevenStageFourCoverage :=
  [
    degreeSevenStageFourCoverage000,
    degreeSevenStageFourCoverage001,
    degreeSevenStageFourCoverage002,
    degreeSevenStageFourCoverage003,
    degreeSevenStageFourCoverage004,
    degreeSevenStageFourCoverage005,
    degreeSevenStageFourCoverage006,
    degreeSevenStageFourCoverage007,
    degreeSevenStageFourCoverage008,
    degreeSevenStageFourCoverage009,
    degreeSevenStageFourCoverage010,
    degreeSevenStageFourCoverage011,
    degreeSevenStageFourCoverage012,
    degreeSevenStageFourCoverage013,
    degreeSevenStageFourCoverage014,
    degreeSevenStageFourCoverage015,
    degreeSevenStageFourCoverage016,
    degreeSevenStageFourCoverage017,
    degreeSevenStageFourCoverage018,
    degreeSevenStageFourCoverage019,
    degreeSevenStageFourCoverage020,
    degreeSevenStageFourCoverage021,
    degreeSevenStageFourCoverage022,
    degreeSevenStageFourCoverage023,
    degreeSevenStageFourCoverage024,
    degreeSevenStageFourCoverage025,
    degreeSevenStageFourCoverage026,
    degreeSevenStageFourCoverage027,
    degreeSevenStageFourCoverage028,
    degreeSevenStageFourCoverage029,
    degreeSevenStageFourCoverage030,
    degreeSevenStageFourCoverage031,
    degreeSevenStageFourCoverage032,
    degreeSevenStageFourCoverage033,
    degreeSevenStageFourCoverage034,
    degreeSevenStageFourCoverage035,
    degreeSevenStageFourCoverage036,
    degreeSevenStageFourCoverage037,
    degreeSevenStageFourCoverage038,
    degreeSevenStageFourCoverage039,
    degreeSevenStageFourCoverage040,
    degreeSevenStageFourCoverage041,
    degreeSevenStageFourCoverage042,
    degreeSevenStageFourCoverage043,
    degreeSevenStageFourCoverage044,
    degreeSevenStageFourCoverage045,
    degreeSevenStageFourCoverage046,
    degreeSevenStageFourCoverage047,
    degreeSevenStageFourCoverage048,
    degreeSevenStageFourCoverage049,
    degreeSevenStageFourCoverage050,
    degreeSevenStageFourCoverage051,
    degreeSevenStageFourCoverage052,
    degreeSevenStageFourCoverage053
  ]

def degreeSevenStageFourCoverageSurvivingTriples :
    List (ℤ × ℤ × ℤ) :=
  degreeSevenStageFourCoverages.flatMap fun coverage =>
    coverage.surviving.map fun a4 =>
      (coverage.parent.a6, coverage.parent.a5, a4)

def degreeSevenStageFourCoverageRejectedTriples :
    List (ℤ × ℤ × ℤ) :=
  degreeSevenStageFourCoverages.flatMap fun coverage =>
    coverage.rejected.map fun a4 =>
      (coverage.parent.a6, coverage.parent.a5, a4)

/-- The exact 1,641 triples admitted by the first Rolle stage. -/
def degreeSevenStageThreePrefixes : List (ℤ × ℤ × ℤ) :=
  degreeSevenStageThreeEntries.flatMap fun entry =>
    entry.a4Candidates.toList.map fun a4 => (entry.a6, entry.a5, a4)

def degreeSevenStageFourEntries :
    List DegreeSevenStageFourEntry :=
  degreeSevenStageFourEntriesChunk000 ++
    degreeSevenStageFourEntriesChunk001 ++
    degreeSevenStageFourEntriesChunk002 ++
    degreeSevenStageFourEntriesChunk003 ++
    degreeSevenStageFourEntriesChunk004 ++
    degreeSevenStageFourEntriesChunk005 ++
    degreeSevenStageFourEntriesChunk006 ++
    degreeSevenStageFourEntriesChunk007 ++
    degreeSevenStageFourEntriesChunk008 ++
    degreeSevenStageFourEntriesChunk009 ++
    degreeSevenStageFourEntriesChunk010 ++
    degreeSevenStageFourEntriesChunk011 ++
    degreeSevenStageFourEntriesChunk012 ++
    degreeSevenStageFourEntriesChunk013 ++
    degreeSevenStageFourEntriesChunk014 ++
    degreeSevenStageFourEntriesChunk015 ++
    degreeSevenStageFourEntriesChunk016 ++
    degreeSevenStageFourEntriesChunk017 ++
    degreeSevenStageFourEntriesChunk018 ++
    degreeSevenStageFourEntriesChunk019 ++
    degreeSevenStageFourEntriesChunk020 ++
    degreeSevenStageFourEntriesChunk021 ++
    degreeSevenStageFourEntriesChunk022 ++
    degreeSevenStageFourEntriesChunk023 ++
    degreeSevenStageFourEntriesChunk024 ++
    degreeSevenStageFourEntriesChunk025 ++
    degreeSevenStageFourEntriesChunk026 ++
    degreeSevenStageFourEntriesChunk027 ++
    degreeSevenStageFourEntriesChunk028 ++
    degreeSevenStageFourEntriesChunk029 ++
    degreeSevenStageFourEntriesChunk030 ++
    degreeSevenStageFourEntriesChunk031 ++
    degreeSevenStageFourEntriesChunk032 ++
    degreeSevenStageFourEntriesChunk033 ++
    degreeSevenStageFourEntriesChunk034 ++
    degreeSevenStageFourEntriesChunk035 ++
    degreeSevenStageFourEntriesChunk036 ++
    degreeSevenStageFourEntriesChunk037 ++
    degreeSevenStageFourEntriesChunk038 ++
    degreeSevenStageFourEntriesChunk039 ++
    degreeSevenStageFourEntriesChunk040 ++
    degreeSevenStageFourEntriesChunk041 ++
    degreeSevenStageFourEntriesChunk042 ++
    degreeSevenStageFourEntriesChunk043 ++
    degreeSevenStageFourEntriesChunk044 ++
    degreeSevenStageFourEntriesChunk045 ++
    degreeSevenStageFourEntriesChunk046 ++
    degreeSevenStageFourEntriesChunk047 ++
    degreeSevenStageFourEntriesChunk048 ++
    degreeSevenStageFourEntriesChunk049 ++
    degreeSevenStageFourEntriesChunk050 ++
    degreeSevenStageFourEntriesChunk051 ++
    degreeSevenStageFourEntriesChunk052 ++
    degreeSevenStageFourEntriesChunk053 ++
    degreeSevenStageFourEntriesChunk054 ++
    degreeSevenStageFourEntriesChunk055 ++
    degreeSevenStageFourEntriesChunk056 ++
    degreeSevenStageFourEntriesChunk057 ++
    degreeSevenStageFourEntriesChunk058 ++
    degreeSevenStageFourEntriesChunk059 ++
    degreeSevenStageFourEntriesChunk060 ++
    degreeSevenStageFourEntriesChunk061 ++
    degreeSevenStageFourEntriesChunk062 ++
    degreeSevenStageFourEntriesChunk063 ++
    degreeSevenStageFourEntriesChunk064 ++
    degreeSevenStageFourEntriesChunk065

/-- The exact coefficient ranges attached to all 1,636 certified cubic rows. -/
def degreeSevenStageFourExpectedRanges :
    List (ℤ × ℤ × ℤ × ℤ × ℤ) :=
  degreeSevenStageFourExpectedRangesChunk000 ++
    degreeSevenStageFourExpectedRangesChunk001 ++
    degreeSevenStageFourExpectedRangesChunk002 ++
    degreeSevenStageFourExpectedRangesChunk003 ++
    degreeSevenStageFourExpectedRangesChunk004 ++
    degreeSevenStageFourExpectedRangesChunk005 ++
    degreeSevenStageFourExpectedRangesChunk006 ++
    degreeSevenStageFourExpectedRangesChunk007 ++
    degreeSevenStageFourExpectedRangesChunk008 ++
    degreeSevenStageFourExpectedRangesChunk009 ++
    degreeSevenStageFourExpectedRangesChunk010 ++
    degreeSevenStageFourExpectedRangesChunk011 ++
    degreeSevenStageFourExpectedRangesChunk012 ++
    degreeSevenStageFourExpectedRangesChunk013 ++
    degreeSevenStageFourExpectedRangesChunk014 ++
    degreeSevenStageFourExpectedRangesChunk015 ++
    degreeSevenStageFourExpectedRangesChunk016 ++
    degreeSevenStageFourExpectedRangesChunk017 ++
    degreeSevenStageFourExpectedRangesChunk018 ++
    degreeSevenStageFourExpectedRangesChunk019 ++
    degreeSevenStageFourExpectedRangesChunk020 ++
    degreeSevenStageFourExpectedRangesChunk021 ++
    degreeSevenStageFourExpectedRangesChunk022 ++
    degreeSevenStageFourExpectedRangesChunk023 ++
    degreeSevenStageFourExpectedRangesChunk024 ++
    degreeSevenStageFourExpectedRangesChunk025 ++
    degreeSevenStageFourExpectedRangesChunk026 ++
    degreeSevenStageFourExpectedRangesChunk027 ++
    degreeSevenStageFourExpectedRangesChunk028 ++
    degreeSevenStageFourExpectedRangesChunk029 ++
    degreeSevenStageFourExpectedRangesChunk030 ++
    degreeSevenStageFourExpectedRangesChunk031 ++
    degreeSevenStageFourExpectedRangesChunk032 ++
    degreeSevenStageFourExpectedRangesChunk033 ++
    degreeSevenStageFourExpectedRangesChunk034 ++
    degreeSevenStageFourExpectedRangesChunk035 ++
    degreeSevenStageFourExpectedRangesChunk036 ++
    degreeSevenStageFourExpectedRangesChunk037 ++
    degreeSevenStageFourExpectedRangesChunk038 ++
    degreeSevenStageFourExpectedRangesChunk039 ++
    degreeSevenStageFourExpectedRangesChunk040 ++
    degreeSevenStageFourExpectedRangesChunk041 ++
    degreeSevenStageFourExpectedRangesChunk042 ++
    degreeSevenStageFourExpectedRangesChunk043 ++
    degreeSevenStageFourExpectedRangesChunk044 ++
    degreeSevenStageFourExpectedRangesChunk045 ++
    degreeSevenStageFourExpectedRangesChunk046 ++
    degreeSevenStageFourExpectedRangesChunk047 ++
    degreeSevenStageFourExpectedRangesChunk048 ++
    degreeSevenStageFourExpectedRangesChunk049 ++
    degreeSevenStageFourExpectedRangesChunk050 ++
    degreeSevenStageFourExpectedRangesChunk051 ++
    degreeSevenStageFourExpectedRangesChunk052 ++
    degreeSevenStageFourExpectedRangesChunk053 ++
    degreeSevenStageFourExpectedRangesChunk054 ++
    degreeSevenStageFourExpectedRangesChunk055 ++
    degreeSevenStageFourExpectedRangesChunk056 ++
    degreeSevenStageFourExpectedRangesChunk057 ++
    degreeSevenStageFourExpectedRangesChunk058 ++
    degreeSevenStageFourExpectedRangesChunk059 ++
    degreeSevenStageFourExpectedRangesChunk060 ++
    degreeSevenStageFourExpectedRangesChunk061 ++
    degreeSevenStageFourExpectedRangesChunk062 ++
    degreeSevenStageFourExpectedRangesChunk063 ++
    degreeSevenStageFourExpectedRangesChunk064 ++
    degreeSevenStageFourExpectedRangesChunk065

/-- Coefficient triples represented by the certified cubic rows. -/
def degreeSevenStageFourTopTriples : List (ℤ × ℤ × ℤ) :=
  [
    ((-3 : ℤ), (-9 : ℤ), (-8 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (-7 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (-6 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (-5 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (-4 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (-3 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (-2 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (-1 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (0 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (1 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (2 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (3 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (4 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (5 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (6 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (7 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (8 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (9 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (10 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (11 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (12 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (13 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (14 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (15 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (16 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (17 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (18 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (19 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (20 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (21 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (22 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (23 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (24 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (25 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (26 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (27 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (28 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (29 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (30 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (31 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (32 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (33 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (34 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (35 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (36 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (37 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (38 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (39 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (40 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (41 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (42 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (43 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (44 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (45 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (46 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (47 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (48 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (49 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (50 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (51 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (52 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (53 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (54 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (55 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (56 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (57 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (58 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (-7 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (-6 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (-5 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (-4 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (-3 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (-2 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (-1 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (0 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (1 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (2 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (3 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (4 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (5 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (6 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (7 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (8 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (9 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (10 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (11 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (12 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (13 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (14 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (15 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (16 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (17 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (18 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (19 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (20 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (21 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (22 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (23 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (24 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (25 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (26 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (27 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (28 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (29 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (30 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (31 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (32 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (33 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (34 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (35 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (36 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (37 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (38 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (39 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (40 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (41 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (42 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (43 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (44 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (45 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (46 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (47 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (48 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (49 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (50 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (51 : ℤ)),
    ((-3 : ℤ), (-8 : ℤ), (52 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (-5 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (-4 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (-3 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (-2 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (-1 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (0 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (1 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (2 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (3 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (4 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (5 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (6 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (7 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (8 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (9 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (10 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (11 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (12 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (13 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (14 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (15 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (16 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (17 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (18 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (19 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (20 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (21 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (22 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (23 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (24 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (25 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (26 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (27 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (28 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (29 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (30 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (31 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (32 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (33 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (34 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (35 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (36 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (37 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (38 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (39 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (40 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (41 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (42 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (43 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (44 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (45 : ℤ)),
    ((-3 : ℤ), (-7 : ℤ), (46 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (-4 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (-3 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (-2 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (-1 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (0 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (1 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (2 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (3 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (4 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (5 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (6 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (7 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (8 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (9 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (10 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (11 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (12 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (13 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (14 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (15 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (16 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (17 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (18 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (19 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (20 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (21 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (22 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (23 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (24 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (25 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (26 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (27 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (28 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (29 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (30 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (31 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (32 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (33 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (34 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (35 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (36 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (37 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (38 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (39 : ℤ)),
    ((-3 : ℤ), (-6 : ℤ), (40 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (-2 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (-1 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (0 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (1 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (2 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (3 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (4 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (5 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (6 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (7 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (8 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (9 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (10 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (11 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (12 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (13 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (14 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (15 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (16 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (17 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (18 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (19 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (20 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (21 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (22 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (23 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (24 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (25 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (26 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (27 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (28 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (29 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (30 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (31 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (32 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (33 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (34 : ℤ)),
    ((-3 : ℤ), (-5 : ℤ), (35 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (-1 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (0 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (1 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (2 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (3 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (4 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (5 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (6 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (7 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (8 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (9 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (10 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (11 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (12 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (13 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (14 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (15 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (16 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (17 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (18 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (19 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (20 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (21 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (22 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (23 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (24 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (25 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (26 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (27 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (28 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (29 : ℤ)),
    ((-3 : ℤ), (-4 : ℤ), (30 : ℤ)),
    ((-3 : ℤ), (-3 : ℤ), (-1 : ℤ)),
    ((-3 : ℤ), (-3 : ℤ), (0 : ℤ)),
    ((-3 : ℤ), (-3 : ℤ), (1 : ℤ)),
    ((-3 : ℤ), (-3 : ℤ), (2 : ℤ)),
    ((-3 : ℤ), (-3 : ℤ), (3 : ℤ)),
    ((-3 : ℤ), (-3 : ℤ), (4 : ℤ)),
    ((-3 : ℤ), (-3 : ℤ), (5 : ℤ)),
    ((-3 : ℤ), (-3 : ℤ), (6 : ℤ)),
    ((-3 : ℤ), (-3 : ℤ), (7 : ℤ)),
    ((-3 : ℤ), (-3 : ℤ), (8 : ℤ)),
    ((-3 : ℤ), (-3 : ℤ), (9 : ℤ)),
    ((-3 : ℤ), (-3 : ℤ), (10 : ℤ)),
    ((-3 : ℤ), (-3 : ℤ), (11 : ℤ)),
    ((-3 : ℤ), (-3 : ℤ), (12 : ℤ)),
    ((-3 : ℤ), (-3 : ℤ), (13 : ℤ)),
    ((-3 : ℤ), (-3 : ℤ), (14 : ℤ)),
    ((-3 : ℤ), (-3 : ℤ), (15 : ℤ)),
    ((-3 : ℤ), (-3 : ℤ), (16 : ℤ)),
    ((-3 : ℤ), (-3 : ℤ), (17 : ℤ)),
    ((-3 : ℤ), (-3 : ℤ), (18 : ℤ)),
    ((-3 : ℤ), (-3 : ℤ), (19 : ℤ)),
    ((-3 : ℤ), (-3 : ℤ), (20 : ℤ)),
    ((-3 : ℤ), (-3 : ℤ), (21 : ℤ)),
    ((-3 : ℤ), (-3 : ℤ), (22 : ℤ)),
    ((-3 : ℤ), (-3 : ℤ), (23 : ℤ)),
    ((-3 : ℤ), (-3 : ℤ), (24 : ℤ)),
    ((-3 : ℤ), (-2 : ℤ), (0 : ℤ)),
    ((-3 : ℤ), (-2 : ℤ), (1 : ℤ)),
    ((-3 : ℤ), (-2 : ℤ), (2 : ℤ)),
    ((-3 : ℤ), (-2 : ℤ), (3 : ℤ)),
    ((-3 : ℤ), (-2 : ℤ), (4 : ℤ)),
    ((-3 : ℤ), (-2 : ℤ), (5 : ℤ)),
    ((-3 : ℤ), (-2 : ℤ), (6 : ℤ)),
    ((-3 : ℤ), (-2 : ℤ), (7 : ℤ)),
    ((-3 : ℤ), (-2 : ℤ), (8 : ℤ)),
    ((-3 : ℤ), (-2 : ℤ), (9 : ℤ)),
    ((-3 : ℤ), (-2 : ℤ), (10 : ℤ)),
    ((-3 : ℤ), (-2 : ℤ), (11 : ℤ)),
    ((-3 : ℤ), (-2 : ℤ), (12 : ℤ)),
    ((-3 : ℤ), (-2 : ℤ), (13 : ℤ)),
    ((-3 : ℤ), (-2 : ℤ), (14 : ℤ)),
    ((-3 : ℤ), (-2 : ℤ), (15 : ℤ)),
    ((-3 : ℤ), (-2 : ℤ), (16 : ℤ)),
    ((-3 : ℤ), (-2 : ℤ), (17 : ℤ)),
    ((-3 : ℤ), (-2 : ℤ), (18 : ℤ)),
    ((-3 : ℤ), (-2 : ℤ), (19 : ℤ)),
    ((-3 : ℤ), (-2 : ℤ), (20 : ℤ)),
    ((-3 : ℤ), (-1 : ℤ), (0 : ℤ)),
    ((-3 : ℤ), (-1 : ℤ), (1 : ℤ)),
    ((-3 : ℤ), (-1 : ℤ), (2 : ℤ)),
    ((-3 : ℤ), (-1 : ℤ), (3 : ℤ)),
    ((-3 : ℤ), (-1 : ℤ), (4 : ℤ)),
    ((-3 : ℤ), (-1 : ℤ), (5 : ℤ)),
    ((-3 : ℤ), (-1 : ℤ), (6 : ℤ)),
    ((-3 : ℤ), (-1 : ℤ), (7 : ℤ)),
    ((-3 : ℤ), (-1 : ℤ), (8 : ℤ)),
    ((-3 : ℤ), (-1 : ℤ), (9 : ℤ)),
    ((-3 : ℤ), (-1 : ℤ), (10 : ℤ)),
    ((-3 : ℤ), (-1 : ℤ), (11 : ℤ)),
    ((-3 : ℤ), (-1 : ℤ), (12 : ℤ)),
    ((-3 : ℤ), (-1 : ℤ), (13 : ℤ)),
    ((-3 : ℤ), (-1 : ℤ), (14 : ℤ)),
    ((-3 : ℤ), (-1 : ℤ), (15 : ℤ)),
    ((-3 : ℤ), (0 : ℤ), (1 : ℤ)),
    ((-3 : ℤ), (0 : ℤ), (2 : ℤ)),
    ((-3 : ℤ), (0 : ℤ), (3 : ℤ)),
    ((-3 : ℤ), (0 : ℤ), (4 : ℤ)),
    ((-3 : ℤ), (0 : ℤ), (5 : ℤ)),
    ((-3 : ℤ), (0 : ℤ), (6 : ℤ)),
    ((-3 : ℤ), (0 : ℤ), (7 : ℤ)),
    ((-3 : ℤ), (0 : ℤ), (8 : ℤ)),
    ((-3 : ℤ), (0 : ℤ), (9 : ℤ)),
    ((-3 : ℤ), (0 : ℤ), (10 : ℤ)),
    ((-3 : ℤ), (0 : ℤ), (11 : ℤ)),
    ((-3 : ℤ), (1 : ℤ), (0 : ℤ)),
    ((-3 : ℤ), (1 : ℤ), (1 : ℤ)),
    ((-3 : ℤ), (1 : ℤ), (2 : ℤ)),
    ((-3 : ℤ), (1 : ℤ), (3 : ℤ)),
    ((-3 : ℤ), (1 : ℤ), (4 : ℤ)),
    ((-3 : ℤ), (1 : ℤ), (5 : ℤ)),
    ((-3 : ℤ), (1 : ℤ), (6 : ℤ)),
    ((-3 : ℤ), (2 : ℤ), (0 : ℤ)),
    ((-3 : ℤ), (2 : ℤ), (1 : ℤ)),
    ((-3 : ℤ), (2 : ℤ), (2 : ℤ)),
    ((-3 : ℤ), (2 : ℤ), (3 : ℤ)),
    ((-3 : ℤ), (3 : ℤ), (-1 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (-18 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (-17 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (-16 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (-15 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (-14 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (-13 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (-12 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (-11 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (-10 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (-9 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (-8 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (-7 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (-6 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (-5 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (-4 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (-3 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (-2 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (-1 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (0 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (1 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (2 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (3 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (4 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (5 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (6 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (7 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (8 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (9 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (10 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (11 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (12 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (13 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (14 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (15 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (16 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (17 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (18 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (19 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (20 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (21 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (22 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (23 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (24 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (25 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (26 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (27 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (28 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (29 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (30 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (31 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (32 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (33 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (34 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (35 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (36 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (37 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (38 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (39 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (40 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (41 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (42 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (43 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (44 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (45 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (46 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (47 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (48 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (49 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (50 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (51 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (52 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (53 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (54 : ℤ)),
    ((-2 : ℤ), (-12 : ℤ), (55 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (-15 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (-14 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (-13 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (-12 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (-11 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (-10 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (-9 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (-8 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (-7 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (-6 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (-5 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (-4 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (-3 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (-2 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (-1 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (0 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (1 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (2 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (3 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (4 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (5 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (6 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (7 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (8 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (9 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (10 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (11 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (12 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (13 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (14 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (15 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (16 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (17 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (18 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (19 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (20 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (21 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (22 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (23 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (24 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (25 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (26 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (27 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (28 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (29 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (30 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (31 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (32 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (33 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (34 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (35 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (36 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (37 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (38 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (39 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (40 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (41 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (42 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (43 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (44 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (45 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (46 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (47 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (48 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (49 : ℤ)),
    ((-2 : ℤ), (-11 : ℤ), (50 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (-13 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (-12 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (-11 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (-10 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (-9 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (-8 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (-7 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (-6 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (-5 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (-4 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (-3 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (-2 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (-1 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (0 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (1 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (2 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (3 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (4 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (5 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (6 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (7 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (8 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (9 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (10 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (11 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (12 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (13 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (14 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (15 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (16 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (17 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (18 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (19 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (20 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (21 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (22 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (23 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (24 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (25 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (26 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (27 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (28 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (29 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (30 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (31 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (32 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (33 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (34 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (35 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (36 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (37 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (38 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (39 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (40 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (41 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (42 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (43 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (44 : ℤ)),
    ((-2 : ℤ), (-10 : ℤ), (45 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (-11 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (-10 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (-9 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (-8 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (-7 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (-6 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (-5 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (-4 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (-3 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (-2 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (-1 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (0 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (1 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (2 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (3 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (4 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (5 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (6 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (7 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (8 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (9 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (10 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (11 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (12 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (13 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (14 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (15 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (16 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (17 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (18 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (19 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (20 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (21 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (22 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (23 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (24 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (25 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (26 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (27 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (28 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (29 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (30 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (31 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (32 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (33 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (34 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (35 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (36 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (37 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (38 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (39 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (-8 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (-7 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (-6 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (-5 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (-4 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (-3 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (-2 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (-1 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (0 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (1 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (2 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (3 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (4 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (5 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (6 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (7 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (8 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (9 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (10 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (11 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (12 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (13 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (14 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (15 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (16 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (17 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (18 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (19 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (20 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (21 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (22 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (23 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (24 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (25 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (26 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (27 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (28 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (29 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (30 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (31 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (32 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (33 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (34 : ℤ)),
    ((-2 : ℤ), (-8 : ℤ), (35 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (-7 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (-6 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (-5 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (-4 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (-3 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (-2 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (-1 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (0 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (1 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (2 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (3 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (4 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (5 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (6 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (7 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (8 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (9 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (10 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (11 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (12 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (13 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (14 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (15 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (16 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (17 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (18 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (19 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (20 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (21 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (22 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (23 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (24 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (25 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (26 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (27 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (28 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (29 : ℤ)),
    ((-2 : ℤ), (-7 : ℤ), (30 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (-5 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (-4 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (-3 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (-2 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (-1 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (0 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (1 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (2 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (3 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (4 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (5 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (6 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (7 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (8 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (9 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (10 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (11 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (12 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (13 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (14 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (15 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (16 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (17 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (18 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (19 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (20 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (21 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (22 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (23 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (24 : ℤ)),
    ((-2 : ℤ), (-6 : ℤ), (25 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (-3 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (-2 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (-1 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (0 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (1 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (2 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (3 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (4 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (5 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (6 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (7 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (8 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (9 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (10 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (11 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (12 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (13 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (14 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (15 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (16 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (17 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (18 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (19 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (20 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (21 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (-2 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (-1 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (0 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (1 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (2 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (3 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (4 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (5 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (6 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (7 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (8 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (9 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (10 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (11 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (12 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (13 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (14 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (15 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (16 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (17 : ℤ)),
    ((-2 : ℤ), (-3 : ℤ), (-1 : ℤ)),
    ((-2 : ℤ), (-3 : ℤ), (0 : ℤ)),
    ((-2 : ℤ), (-3 : ℤ), (1 : ℤ)),
    ((-2 : ℤ), (-3 : ℤ), (2 : ℤ)),
    ((-2 : ℤ), (-3 : ℤ), (3 : ℤ)),
    ((-2 : ℤ), (-3 : ℤ), (4 : ℤ)),
    ((-2 : ℤ), (-3 : ℤ), (5 : ℤ)),
    ((-2 : ℤ), (-3 : ℤ), (6 : ℤ)),
    ((-2 : ℤ), (-3 : ℤ), (7 : ℤ)),
    ((-2 : ℤ), (-3 : ℤ), (8 : ℤ)),
    ((-2 : ℤ), (-3 : ℤ), (9 : ℤ)),
    ((-2 : ℤ), (-3 : ℤ), (10 : ℤ)),
    ((-2 : ℤ), (-3 : ℤ), (11 : ℤ)),
    ((-2 : ℤ), (-3 : ℤ), (12 : ℤ)),
    ((-2 : ℤ), (-3 : ℤ), (13 : ℤ)),
    ((-2 : ℤ), (-2 : ℤ), (0 : ℤ)),
    ((-2 : ℤ), (-2 : ℤ), (1 : ℤ)),
    ((-2 : ℤ), (-2 : ℤ), (2 : ℤ)),
    ((-2 : ℤ), (-2 : ℤ), (3 : ℤ)),
    ((-2 : ℤ), (-2 : ℤ), (4 : ℤ)),
    ((-2 : ℤ), (-2 : ℤ), (5 : ℤ)),
    ((-2 : ℤ), (-2 : ℤ), (6 : ℤ)),
    ((-2 : ℤ), (-2 : ℤ), (7 : ℤ)),
    ((-2 : ℤ), (-2 : ℤ), (8 : ℤ)),
    ((-2 : ℤ), (-2 : ℤ), (9 : ℤ)),
    ((-2 : ℤ), (-1 : ℤ), (0 : ℤ)),
    ((-2 : ℤ), (-1 : ℤ), (1 : ℤ)),
    ((-2 : ℤ), (-1 : ℤ), (2 : ℤ)),
    ((-2 : ℤ), (-1 : ℤ), (3 : ℤ)),
    ((-2 : ℤ), (-1 : ℤ), (4 : ℤ)),
    ((-2 : ℤ), (-1 : ℤ), (5 : ℤ)),
    ((-2 : ℤ), (-1 : ℤ), (6 : ℤ)),
    ((-2 : ℤ), (0 : ℤ), (1 : ℤ)),
    ((-2 : ℤ), (0 : ℤ), (2 : ℤ)),
    ((-2 : ℤ), (0 : ℤ), (3 : ℤ)),
    ((-2 : ℤ), (1 : ℤ), (0 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (-26 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (-25 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (-24 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (-23 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (-22 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (-21 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (-20 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (-19 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (-18 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (-17 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (-16 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (-15 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (-14 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (-13 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (-12 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (-11 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (-10 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (-9 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (-8 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (-7 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (-6 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (-5 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (-4 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (-3 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (-2 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (-1 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (0 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (1 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (2 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (3 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (4 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (5 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (6 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (7 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (8 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (9 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (10 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (11 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (12 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (13 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (14 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (15 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (16 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (17 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (18 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (19 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (20 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (21 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (22 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (23 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (24 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (25 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (26 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (27 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (28 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (29 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (30 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (31 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (32 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (33 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (34 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (35 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (36 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (37 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (38 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (39 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (40 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (41 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (42 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (43 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (44 : ℤ)),
    ((-1 : ℤ), (-13 : ℤ), (45 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (-23 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (-22 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (-21 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (-20 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (-19 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (-18 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (-17 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (-16 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (-15 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (-14 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (-13 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (-12 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (-11 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (-10 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (-9 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (-8 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (-7 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (-6 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (-5 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (-4 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (-3 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (-2 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (-1 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (0 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (1 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (2 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (3 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (4 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (5 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (6 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (7 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (8 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (9 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (10 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (11 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (12 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (13 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (14 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (15 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (16 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (17 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (18 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (19 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (20 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (21 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (22 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (23 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (24 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (25 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (26 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (27 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (28 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (29 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (30 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (31 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (32 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (33 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (34 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (35 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (36 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (37 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (38 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (39 : ℤ)),
    ((-1 : ℤ), (-12 : ℤ), (40 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (-20 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (-19 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (-18 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (-17 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (-16 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (-15 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (-14 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (-13 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (-12 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (-11 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (-10 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (-9 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (-8 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (-7 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (-6 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (-5 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (-4 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (-3 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (-2 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (-1 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (0 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (1 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (2 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (3 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (4 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (5 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (6 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (7 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (8 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (9 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (10 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (11 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (12 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (13 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (14 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (15 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (16 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (17 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (18 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (19 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (20 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (21 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (22 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (23 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (24 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (25 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (26 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (27 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (28 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (29 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (30 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (31 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (32 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (33 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (34 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (35 : ℤ)),
    ((-1 : ℤ), (-11 : ℤ), (36 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (-17 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (-16 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (-15 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (-14 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (-13 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (-12 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (-11 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (-10 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (-9 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (-8 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (-7 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (-6 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (-5 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (-4 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (-3 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (-2 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (-1 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (0 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (1 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (2 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (3 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (4 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (5 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (6 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (7 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (8 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (9 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (10 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (11 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (12 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (13 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (14 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (15 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (16 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (17 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (18 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (19 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (20 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (21 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (22 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (23 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (24 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (25 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (26 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (27 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (28 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (29 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (30 : ℤ)),
    ((-1 : ℤ), (-10 : ℤ), (31 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (-14 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (-13 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (-12 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (-11 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (-10 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (-9 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (-8 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (-7 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (-6 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (-5 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (-4 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (-3 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (-2 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (-1 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (0 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (1 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (2 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (3 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (4 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (5 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (6 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (7 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (8 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (9 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (10 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (11 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (12 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (13 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (14 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (15 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (16 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (17 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (18 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (19 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (20 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (21 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (22 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (23 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (24 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (25 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (26 : ℤ)),
    ((-1 : ℤ), (-9 : ℤ), (27 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (-11 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (-10 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (-9 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (-8 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (-7 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (-6 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (-5 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (-4 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (-3 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (-2 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (-1 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (0 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (1 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (2 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (3 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (4 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (5 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (6 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (7 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (8 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (9 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (10 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (11 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (12 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (13 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (14 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (15 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (16 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (17 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (18 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (19 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (20 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (21 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (22 : ℤ)),
    ((-1 : ℤ), (-8 : ℤ), (23 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (-9 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (-8 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (-7 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (-6 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (-5 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (-4 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (-3 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (-2 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (-1 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (0 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (1 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (2 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (3 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (4 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (5 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (6 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (7 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (8 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (9 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (10 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (11 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (12 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (13 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (14 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (15 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (16 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (17 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (18 : ℤ)),
    ((-1 : ℤ), (-7 : ℤ), (19 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (-7 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (-6 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (-5 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (-4 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (-3 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (-2 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (-1 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (0 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (1 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (2 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (3 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (4 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (5 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (6 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (7 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (8 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (9 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (10 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (11 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (12 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (13 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (14 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (15 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (16 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (-5 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (-4 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (-3 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (-2 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (-1 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (0 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (1 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (2 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (3 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (4 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (5 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (6 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (7 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (8 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (9 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (10 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (11 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (12 : ℤ)),
    ((-1 : ℤ), (-4 : ℤ), (-3 : ℤ)),
    ((-1 : ℤ), (-4 : ℤ), (-2 : ℤ)),
    ((-1 : ℤ), (-4 : ℤ), (-1 : ℤ)),
    ((-1 : ℤ), (-4 : ℤ), (0 : ℤ)),
    ((-1 : ℤ), (-4 : ℤ), (1 : ℤ)),
    ((-1 : ℤ), (-4 : ℤ), (2 : ℤ)),
    ((-1 : ℤ), (-4 : ℤ), (3 : ℤ)),
    ((-1 : ℤ), (-4 : ℤ), (4 : ℤ)),
    ((-1 : ℤ), (-4 : ℤ), (5 : ℤ)),
    ((-1 : ℤ), (-4 : ℤ), (6 : ℤ)),
    ((-1 : ℤ), (-4 : ℤ), (7 : ℤ)),
    ((-1 : ℤ), (-4 : ℤ), (8 : ℤ)),
    ((-1 : ℤ), (-4 : ℤ), (9 : ℤ)),
    ((-1 : ℤ), (-3 : ℤ), (-2 : ℤ)),
    ((-1 : ℤ), (-3 : ℤ), (-1 : ℤ)),
    ((-1 : ℤ), (-3 : ℤ), (0 : ℤ)),
    ((-1 : ℤ), (-3 : ℤ), (1 : ℤ)),
    ((-1 : ℤ), (-3 : ℤ), (2 : ℤ)),
    ((-1 : ℤ), (-3 : ℤ), (3 : ℤ)),
    ((-1 : ℤ), (-3 : ℤ), (4 : ℤ)),
    ((-1 : ℤ), (-3 : ℤ), (5 : ℤ)),
    ((-1 : ℤ), (-3 : ℤ), (6 : ℤ)),
    ((-1 : ℤ), (-2 : ℤ), (-1 : ℤ)),
    ((-1 : ℤ), (-2 : ℤ), (0 : ℤ)),
    ((-1 : ℤ), (-2 : ℤ), (1 : ℤ)),
    ((-1 : ℤ), (-2 : ℤ), (2 : ℤ)),
    ((-1 : ℤ), (-2 : ℤ), (3 : ℤ)),
    ((-1 : ℤ), (-2 : ℤ), (4 : ℤ)),
    ((-1 : ℤ), (-1 : ℤ), (0 : ℤ)),
    ((-1 : ℤ), (-1 : ℤ), (1 : ℤ)),
    ((-1 : ℤ), (-1 : ℤ), (2 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-34 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-33 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-32 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-31 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-30 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-29 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-28 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-27 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-26 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-25 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-24 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-23 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-22 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-21 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-20 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-19 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-18 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-17 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-16 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-15 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-14 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-13 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-12 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-11 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-10 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-9 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-8 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-7 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-6 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-5 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-4 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-3 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-2 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (-1 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (1 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (2 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (3 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (4 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (5 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (6 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (7 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (8 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (9 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (10 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (11 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (12 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (13 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (14 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (15 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (16 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (17 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (18 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (19 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (20 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (21 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (22 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (23 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (24 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (25 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (26 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (27 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (28 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (29 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (30 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (31 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (32 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (33 : ℤ)),
    ((0 : ℤ), (-13 : ℤ), (34 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-30 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-29 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-28 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-27 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-26 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-25 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-24 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-23 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-22 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-21 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-20 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-19 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-18 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-17 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-16 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-15 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-14 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-13 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-12 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-11 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-10 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-9 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-8 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-7 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-6 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-5 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-4 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-3 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-2 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (-1 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (1 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (2 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (3 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (4 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (5 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (6 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (7 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (8 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (9 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (10 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (11 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (12 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (13 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (14 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (15 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (16 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (17 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (18 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (19 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (20 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (21 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (22 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (23 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (24 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (25 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (26 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (27 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (28 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (29 : ℤ)),
    ((0 : ℤ), (-12 : ℤ), (30 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (-26 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (-25 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (-24 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (-23 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (-22 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (-21 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (-20 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (-19 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (-18 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (-17 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (-16 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (-15 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (-14 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (-13 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (-12 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (-11 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (-10 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (-9 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (-8 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (-7 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (-6 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (-5 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (-4 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (-3 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (-2 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (-1 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (1 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (2 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (3 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (4 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (5 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (6 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (7 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (8 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (9 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (10 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (11 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (12 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (13 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (14 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (15 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (16 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (17 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (18 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (19 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (20 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (21 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (22 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (23 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (24 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (25 : ℤ)),
    ((0 : ℤ), (-11 : ℤ), (26 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (-23 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (-22 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (-21 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (-20 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (-19 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (-18 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (-17 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (-16 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (-15 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (-14 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (-13 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (-12 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (-11 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (-10 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (-9 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (-8 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (-7 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (-6 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (-5 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (-4 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (-3 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (-2 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (-1 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (1 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (2 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (3 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (4 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (5 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (6 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (7 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (8 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (9 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (10 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (11 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (12 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (13 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (14 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (15 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (16 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (17 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (18 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (19 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (20 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (21 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (22 : ℤ)),
    ((0 : ℤ), (-10 : ℤ), (23 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (-19 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (-18 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (-17 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (-16 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (-15 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (-14 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (-13 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (-12 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (-11 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (-10 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (-9 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (-8 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (-7 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (-6 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (-5 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (-4 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (-3 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (-2 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (-1 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (1 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (2 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (3 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (4 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (5 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (6 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (7 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (8 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (9 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (10 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (11 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (12 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (13 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (14 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (15 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (16 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (17 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (18 : ℤ)),
    ((0 : ℤ), (-9 : ℤ), (19 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (-16 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (-15 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (-14 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (-13 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (-12 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (-11 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (-10 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (-9 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (-8 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (-7 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (-6 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (-5 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (-4 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (-3 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (-2 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (-1 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (1 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (2 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (3 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (4 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (5 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (6 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (7 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (8 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (9 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (10 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (11 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (12 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (13 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (14 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (15 : ℤ)),
    ((0 : ℤ), (-8 : ℤ), (16 : ℤ)),
    ((0 : ℤ), (-7 : ℤ), (-13 : ℤ)),
    ((0 : ℤ), (-7 : ℤ), (-12 : ℤ)),
    ((0 : ℤ), (-7 : ℤ), (-11 : ℤ)),
    ((0 : ℤ), (-7 : ℤ), (-10 : ℤ)),
    ((0 : ℤ), (-7 : ℤ), (-9 : ℤ)),
    ((0 : ℤ), (-7 : ℤ), (-8 : ℤ)),
    ((0 : ℤ), (-7 : ℤ), (-7 : ℤ)),
    ((0 : ℤ), (-7 : ℤ), (-6 : ℤ)),
    ((0 : ℤ), (-7 : ℤ), (-5 : ℤ)),
    ((0 : ℤ), (-7 : ℤ), (-4 : ℤ)),
    ((0 : ℤ), (-7 : ℤ), (-3 : ℤ)),
    ((0 : ℤ), (-7 : ℤ), (-2 : ℤ)),
    ((0 : ℤ), (-7 : ℤ), (-1 : ℤ)),
    ((0 : ℤ), (-7 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (-7 : ℤ), (1 : ℤ)),
    ((0 : ℤ), (-7 : ℤ), (2 : ℤ)),
    ((0 : ℤ), (-7 : ℤ), (3 : ℤ)),
    ((0 : ℤ), (-7 : ℤ), (4 : ℤ)),
    ((0 : ℤ), (-7 : ℤ), (5 : ℤ)),
    ((0 : ℤ), (-7 : ℤ), (6 : ℤ)),
    ((0 : ℤ), (-7 : ℤ), (7 : ℤ)),
    ((0 : ℤ), (-7 : ℤ), (8 : ℤ)),
    ((0 : ℤ), (-7 : ℤ), (9 : ℤ)),
    ((0 : ℤ), (-7 : ℤ), (10 : ℤ)),
    ((0 : ℤ), (-7 : ℤ), (11 : ℤ)),
    ((0 : ℤ), (-7 : ℤ), (12 : ℤ)),
    ((0 : ℤ), (-7 : ℤ), (13 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (-10 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (-9 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (-8 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (-7 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (-6 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (-5 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (-4 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (-3 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (-2 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (-1 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (1 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (2 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (3 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (4 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (5 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (6 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (7 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (8 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (9 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (10 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (-8 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (-7 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (-6 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (-5 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (-4 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (-3 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (-2 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (-1 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (1 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (2 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (3 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (4 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (5 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (6 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (7 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (8 : ℤ)),
    ((0 : ℤ), (-4 : ℤ), (-5 : ℤ)),
    ((0 : ℤ), (-4 : ℤ), (-4 : ℤ)),
    ((0 : ℤ), (-4 : ℤ), (-3 : ℤ)),
    ((0 : ℤ), (-4 : ℤ), (-2 : ℤ)),
    ((0 : ℤ), (-4 : ℤ), (-1 : ℤ)),
    ((0 : ℤ), (-4 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (-4 : ℤ), (1 : ℤ)),
    ((0 : ℤ), (-4 : ℤ), (2 : ℤ)),
    ((0 : ℤ), (-4 : ℤ), (3 : ℤ)),
    ((0 : ℤ), (-4 : ℤ), (4 : ℤ)),
    ((0 : ℤ), (-4 : ℤ), (5 : ℤ)),
    ((0 : ℤ), (-3 : ℤ), (-3 : ℤ)),
    ((0 : ℤ), (-3 : ℤ), (-2 : ℤ)),
    ((0 : ℤ), (-3 : ℤ), (-1 : ℤ)),
    ((0 : ℤ), (-3 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (-3 : ℤ), (1 : ℤ)),
    ((0 : ℤ), (-3 : ℤ), (2 : ℤ)),
    ((0 : ℤ), (-3 : ℤ), (3 : ℤ)),
    ((0 : ℤ), (-2 : ℤ), (-2 : ℤ)),
    ((0 : ℤ), (-2 : ℤ), (-1 : ℤ)),
    ((0 : ℤ), (-2 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (-2 : ℤ), (1 : ℤ)),
    ((0 : ℤ), (-2 : ℤ), (2 : ℤ)),
    ((0 : ℤ), (-1 : ℤ), (0 : ℤ))
  ]

/-- The five third-stage triples whose cubic has a multiple root. -/
def degreeSevenStageFourRejectedTriples : List (ℤ × ℤ × ℤ) :=
  [
    ((-3 : ℤ), (-3 : ℤ), (25 : ℤ)),
    ((-3 : ℤ), (0 : ℤ), (0 : ℤ)),
    ((-2 : ℤ), (-9 : ℤ), (40 : ℤ)),
    ((-2 : ℤ), (0 : ℤ), (0 : ℤ)),
    ((-1 : ℤ), (0 : ℤ), (0 : ℤ))
  ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This expands all generated structures and checks their coefficient keys.
theorem degreeSevenStageFourTopTriples_checked :
    degreeSevenStageFourEntries.map (fun entry =>
      (entry.a6, entry.a5, entry.a4)) =
        degreeSevenStageFourTopTriples := by
  simp only [degreeSevenStageFourEntries, List.map_append,
    degreeSevenStageFourEntriesChunk000, degreeSevenStageFourEntriesChunk001, degreeSevenStageFourEntriesChunk002, degreeSevenStageFourEntriesChunk003, degreeSevenStageFourEntriesChunk004, degreeSevenStageFourEntriesChunk005, degreeSevenStageFourEntriesChunk006, degreeSevenStageFourEntriesChunk007, degreeSevenStageFourEntriesChunk008, degreeSevenStageFourEntriesChunk009, degreeSevenStageFourEntriesChunk010, degreeSevenStageFourEntriesChunk011, degreeSevenStageFourEntriesChunk012, degreeSevenStageFourEntriesChunk013, degreeSevenStageFourEntriesChunk014, degreeSevenStageFourEntriesChunk015, degreeSevenStageFourEntriesChunk016, degreeSevenStageFourEntriesChunk017, degreeSevenStageFourEntriesChunk018, degreeSevenStageFourEntriesChunk019, degreeSevenStageFourEntriesChunk020, degreeSevenStageFourEntriesChunk021, degreeSevenStageFourEntriesChunk022, degreeSevenStageFourEntriesChunk023, degreeSevenStageFourEntriesChunk024, degreeSevenStageFourEntriesChunk025, degreeSevenStageFourEntriesChunk026, degreeSevenStageFourEntriesChunk027, degreeSevenStageFourEntriesChunk028, degreeSevenStageFourEntriesChunk029, degreeSevenStageFourEntriesChunk030, degreeSevenStageFourEntriesChunk031, degreeSevenStageFourEntriesChunk032, degreeSevenStageFourEntriesChunk033, degreeSevenStageFourEntriesChunk034, degreeSevenStageFourEntriesChunk035, degreeSevenStageFourEntriesChunk036, degreeSevenStageFourEntriesChunk037, degreeSevenStageFourEntriesChunk038, degreeSevenStageFourEntriesChunk039, degreeSevenStageFourEntriesChunk040, degreeSevenStageFourEntriesChunk041, degreeSevenStageFourEntriesChunk042, degreeSevenStageFourEntriesChunk043, degreeSevenStageFourEntriesChunk044, degreeSevenStageFourEntriesChunk045, degreeSevenStageFourEntriesChunk046, degreeSevenStageFourEntriesChunk047, degreeSevenStageFourEntriesChunk048, degreeSevenStageFourEntriesChunk049, degreeSevenStageFourEntriesChunk050, degreeSevenStageFourEntriesChunk051, degreeSevenStageFourEntriesChunk052, degreeSevenStageFourEntriesChunk053, degreeSevenStageFourEntriesChunk054, degreeSevenStageFourEntriesChunk055, degreeSevenStageFourEntriesChunk056, degreeSevenStageFourEntriesChunk057, degreeSevenStageFourEntriesChunk058, degreeSevenStageFourEntriesChunk059, degreeSevenStageFourEntriesChunk060, degreeSevenStageFourEntriesChunk061, degreeSevenStageFourEntriesChunk062, degreeSevenStageFourEntriesChunk063, degreeSevenStageFourEntriesChunk064, degreeSevenStageFourEntriesChunk065, degreeSevenStageFourTopTriples]
  rfl

theorem degreeSevenStageFourCoverage_parents_checked :
    degreeSevenStageFourCoverages.map
        DegreeSevenStageFourCoverage.parent =
      degreeSevenStageThreeEntries := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage000_valid :
    degreeSevenStageFourCoverage000.Valid := by
  norm_num [degreeSevenStageFourCoverage000,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage001_valid :
    degreeSevenStageFourCoverage001.Valid := by
  norm_num [degreeSevenStageFourCoverage001,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage002_valid :
    degreeSevenStageFourCoverage002.Valid := by
  norm_num [degreeSevenStageFourCoverage002,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage003_valid :
    degreeSevenStageFourCoverage003.Valid := by
  norm_num [degreeSevenStageFourCoverage003,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage004_valid :
    degreeSevenStageFourCoverage004.Valid := by
  norm_num [degreeSevenStageFourCoverage004,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage005_valid :
    degreeSevenStageFourCoverage005.Valid := by
  norm_num [degreeSevenStageFourCoverage005,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage006_valid :
    degreeSevenStageFourCoverage006.Valid := by
  norm_num [degreeSevenStageFourCoverage006,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage007_valid :
    degreeSevenStageFourCoverage007.Valid := by
  norm_num [degreeSevenStageFourCoverage007,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage008_valid :
    degreeSevenStageFourCoverage008.Valid := by
  norm_num [degreeSevenStageFourCoverage008,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage009_valid :
    degreeSevenStageFourCoverage009.Valid := by
  norm_num [degreeSevenStageFourCoverage009,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage010_valid :
    degreeSevenStageFourCoverage010.Valid := by
  norm_num [degreeSevenStageFourCoverage010,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage011_valid :
    degreeSevenStageFourCoverage011.Valid := by
  norm_num [degreeSevenStageFourCoverage011,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage012_valid :
    degreeSevenStageFourCoverage012.Valid := by
  norm_num [degreeSevenStageFourCoverage012,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage013_valid :
    degreeSevenStageFourCoverage013.Valid := by
  norm_num [degreeSevenStageFourCoverage013,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage014_valid :
    degreeSevenStageFourCoverage014.Valid := by
  norm_num [degreeSevenStageFourCoverage014,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage015_valid :
    degreeSevenStageFourCoverage015.Valid := by
  norm_num [degreeSevenStageFourCoverage015,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage016_valid :
    degreeSevenStageFourCoverage016.Valid := by
  norm_num [degreeSevenStageFourCoverage016,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage017_valid :
    degreeSevenStageFourCoverage017.Valid := by
  norm_num [degreeSevenStageFourCoverage017,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage018_valid :
    degreeSevenStageFourCoverage018.Valid := by
  norm_num [degreeSevenStageFourCoverage018,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage019_valid :
    degreeSevenStageFourCoverage019.Valid := by
  norm_num [degreeSevenStageFourCoverage019,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage020_valid :
    degreeSevenStageFourCoverage020.Valid := by
  norm_num [degreeSevenStageFourCoverage020,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage021_valid :
    degreeSevenStageFourCoverage021.Valid := by
  norm_num [degreeSevenStageFourCoverage021,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage022_valid :
    degreeSevenStageFourCoverage022.Valid := by
  norm_num [degreeSevenStageFourCoverage022,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage023_valid :
    degreeSevenStageFourCoverage023.Valid := by
  norm_num [degreeSevenStageFourCoverage023,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage024_valid :
    degreeSevenStageFourCoverage024.Valid := by
  norm_num [degreeSevenStageFourCoverage024,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage025_valid :
    degreeSevenStageFourCoverage025.Valid := by
  norm_num [degreeSevenStageFourCoverage025,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage026_valid :
    degreeSevenStageFourCoverage026.Valid := by
  norm_num [degreeSevenStageFourCoverage026,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage027_valid :
    degreeSevenStageFourCoverage027.Valid := by
  norm_num [degreeSevenStageFourCoverage027,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage028_valid :
    degreeSevenStageFourCoverage028.Valid := by
  norm_num [degreeSevenStageFourCoverage028,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage029_valid :
    degreeSevenStageFourCoverage029.Valid := by
  norm_num [degreeSevenStageFourCoverage029,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage030_valid :
    degreeSevenStageFourCoverage030.Valid := by
  norm_num [degreeSevenStageFourCoverage030,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage031_valid :
    degreeSevenStageFourCoverage031.Valid := by
  norm_num [degreeSevenStageFourCoverage031,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage032_valid :
    degreeSevenStageFourCoverage032.Valid := by
  norm_num [degreeSevenStageFourCoverage032,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage033_valid :
    degreeSevenStageFourCoverage033.Valid := by
  norm_num [degreeSevenStageFourCoverage033,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage034_valid :
    degreeSevenStageFourCoverage034.Valid := by
  norm_num [degreeSevenStageFourCoverage034,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage035_valid :
    degreeSevenStageFourCoverage035.Valid := by
  norm_num [degreeSevenStageFourCoverage035,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage036_valid :
    degreeSevenStageFourCoverage036.Valid := by
  norm_num [degreeSevenStageFourCoverage036,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage037_valid :
    degreeSevenStageFourCoverage037.Valid := by
  norm_num [degreeSevenStageFourCoverage037,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage038_valid :
    degreeSevenStageFourCoverage038.Valid := by
  norm_num [degreeSevenStageFourCoverage038,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage039_valid :
    degreeSevenStageFourCoverage039.Valid := by
  norm_num [degreeSevenStageFourCoverage039,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage040_valid :
    degreeSevenStageFourCoverage040.Valid := by
  norm_num [degreeSevenStageFourCoverage040,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage041_valid :
    degreeSevenStageFourCoverage041.Valid := by
  norm_num [degreeSevenStageFourCoverage041,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage042_valid :
    degreeSevenStageFourCoverage042.Valid := by
  norm_num [degreeSevenStageFourCoverage042,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage043_valid :
    degreeSevenStageFourCoverage043.Valid := by
  norm_num [degreeSevenStageFourCoverage043,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage044_valid :
    degreeSevenStageFourCoverage044.Valid := by
  norm_num [degreeSevenStageFourCoverage044,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage045_valid :
    degreeSevenStageFourCoverage045.Valid := by
  norm_num [degreeSevenStageFourCoverage045,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage046_valid :
    degreeSevenStageFourCoverage046.Valid := by
  norm_num [degreeSevenStageFourCoverage046,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage047_valid :
    degreeSevenStageFourCoverage047.Valid := by
  norm_num [degreeSevenStageFourCoverage047,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage048_valid :
    degreeSevenStageFourCoverage048.Valid := by
  norm_num [degreeSevenStageFourCoverage048,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage049_valid :
    degreeSevenStageFourCoverage049.Valid := by
  norm_num [degreeSevenStageFourCoverage049,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage050_valid :
    degreeSevenStageFourCoverage050.Valid := by
  norm_num [degreeSevenStageFourCoverage050,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage051_valid :
    degreeSevenStageFourCoverage051.Valid := by
  norm_num [degreeSevenStageFourCoverage051,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage052_valid :
    degreeSevenStageFourCoverage052.Valid := by
  norm_num [degreeSevenStageFourCoverage052,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem degreeSevenStageFourCoverage053_valid :
    degreeSevenStageFourCoverage053.Valid := by
  norm_num [degreeSevenStageFourCoverage053,
    DegreeSevenStageFourCoverage.Valid,
    DegreeSevenStageThreeEntry.a4Candidates,
    DegreeSevenStageThreeEntry.baseCoefficients,
    cubicTranslationCandidates, integerIcc,
    cubicTranslationLowerBound, cubicTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] <;>
    decide

/-- The 54 separate kernel certificates cover every parent row. -/
theorem degreeSevenStageFourCoverages_valid :
    degreeSevenStageFourCoverages.Forall
      DegreeSevenStageFourCoverage.Valid := by
  simp only [degreeSevenStageFourCoverages,
    List.forall_cons]
  exact ⟨degreeSevenStageFourCoverage000_valid, ⟨degreeSevenStageFourCoverage001_valid, ⟨degreeSevenStageFourCoverage002_valid, ⟨degreeSevenStageFourCoverage003_valid, ⟨degreeSevenStageFourCoverage004_valid, ⟨degreeSevenStageFourCoverage005_valid, ⟨degreeSevenStageFourCoverage006_valid, ⟨degreeSevenStageFourCoverage007_valid, ⟨degreeSevenStageFourCoverage008_valid, ⟨degreeSevenStageFourCoverage009_valid, ⟨degreeSevenStageFourCoverage010_valid, ⟨degreeSevenStageFourCoverage011_valid, ⟨degreeSevenStageFourCoverage012_valid, ⟨degreeSevenStageFourCoverage013_valid, ⟨degreeSevenStageFourCoverage014_valid, ⟨degreeSevenStageFourCoverage015_valid, ⟨degreeSevenStageFourCoverage016_valid, ⟨degreeSevenStageFourCoverage017_valid, ⟨degreeSevenStageFourCoverage018_valid, ⟨degreeSevenStageFourCoverage019_valid, ⟨degreeSevenStageFourCoverage020_valid, ⟨degreeSevenStageFourCoverage021_valid, ⟨degreeSevenStageFourCoverage022_valid, ⟨degreeSevenStageFourCoverage023_valid, ⟨degreeSevenStageFourCoverage024_valid, ⟨degreeSevenStageFourCoverage025_valid, ⟨degreeSevenStageFourCoverage026_valid, ⟨degreeSevenStageFourCoverage027_valid, ⟨degreeSevenStageFourCoverage028_valid, ⟨degreeSevenStageFourCoverage029_valid, ⟨degreeSevenStageFourCoverage030_valid, ⟨degreeSevenStageFourCoverage031_valid, ⟨degreeSevenStageFourCoverage032_valid, ⟨degreeSevenStageFourCoverage033_valid, ⟨degreeSevenStageFourCoverage034_valid, ⟨degreeSevenStageFourCoverage035_valid, ⟨degreeSevenStageFourCoverage036_valid, ⟨degreeSevenStageFourCoverage037_valid, ⟨degreeSevenStageFourCoverage038_valid, ⟨degreeSevenStageFourCoverage039_valid, ⟨degreeSevenStageFourCoverage040_valid, ⟨degreeSevenStageFourCoverage041_valid, ⟨degreeSevenStageFourCoverage042_valid, ⟨degreeSevenStageFourCoverage043_valid, ⟨degreeSevenStageFourCoverage044_valid, ⟨degreeSevenStageFourCoverage045_valid, ⟨degreeSevenStageFourCoverage046_valid, ⟨degreeSevenStageFourCoverage047_valid, ⟨degreeSevenStageFourCoverage048_valid, ⟨degreeSevenStageFourCoverage049_valid, ⟨degreeSevenStageFourCoverage050_valid, ⟨degreeSevenStageFourCoverage051_valid, ⟨degreeSevenStageFourCoverage052_valid, ⟨degreeSevenStageFourCoverage053_valid, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Expanding the coverage rows gives the generated simple-root key list.
theorem degreeSevenStageFourCoverage_surviving_checked :
    degreeSevenStageFourCoverageSurvivingTriples =
      degreeSevenStageFourTopTriples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFourCoverage_rejected_checked :
    degreeSevenStageFourCoverageRejectedTriples =
      degreeSevenStageFourRejectedTriples := by
  rfl

theorem degreeSevenStageFourEntries_valid :
    degreeSevenStageFourEntries.Forall
      DegreeSevenStageFourEntry.Valid := by
  simp only [degreeSevenStageFourEntries, List.forall_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨degreeSevenStageFourEntriesChunk000_valid, degreeSevenStageFourEntriesChunk001_valid⟩, degreeSevenStageFourEntriesChunk002_valid⟩, degreeSevenStageFourEntriesChunk003_valid⟩, degreeSevenStageFourEntriesChunk004_valid⟩, degreeSevenStageFourEntriesChunk005_valid⟩, degreeSevenStageFourEntriesChunk006_valid⟩, degreeSevenStageFourEntriesChunk007_valid⟩, degreeSevenStageFourEntriesChunk008_valid⟩, degreeSevenStageFourEntriesChunk009_valid⟩, degreeSevenStageFourEntriesChunk010_valid⟩, degreeSevenStageFourEntriesChunk011_valid⟩, degreeSevenStageFourEntriesChunk012_valid⟩, degreeSevenStageFourEntriesChunk013_valid⟩, degreeSevenStageFourEntriesChunk014_valid⟩, degreeSevenStageFourEntriesChunk015_valid⟩, degreeSevenStageFourEntriesChunk016_valid⟩, degreeSevenStageFourEntriesChunk017_valid⟩, degreeSevenStageFourEntriesChunk018_valid⟩, degreeSevenStageFourEntriesChunk019_valid⟩, degreeSevenStageFourEntriesChunk020_valid⟩, degreeSevenStageFourEntriesChunk021_valid⟩, degreeSevenStageFourEntriesChunk022_valid⟩, degreeSevenStageFourEntriesChunk023_valid⟩, degreeSevenStageFourEntriesChunk024_valid⟩, degreeSevenStageFourEntriesChunk025_valid⟩, degreeSevenStageFourEntriesChunk026_valid⟩, degreeSevenStageFourEntriesChunk027_valid⟩, degreeSevenStageFourEntriesChunk028_valid⟩, degreeSevenStageFourEntriesChunk029_valid⟩, degreeSevenStageFourEntriesChunk030_valid⟩, degreeSevenStageFourEntriesChunk031_valid⟩, degreeSevenStageFourEntriesChunk032_valid⟩, degreeSevenStageFourEntriesChunk033_valid⟩, degreeSevenStageFourEntriesChunk034_valid⟩, degreeSevenStageFourEntriesChunk035_valid⟩, degreeSevenStageFourEntriesChunk036_valid⟩, degreeSevenStageFourEntriesChunk037_valid⟩, degreeSevenStageFourEntriesChunk038_valid⟩, degreeSevenStageFourEntriesChunk039_valid⟩, degreeSevenStageFourEntriesChunk040_valid⟩, degreeSevenStageFourEntriesChunk041_valid⟩, degreeSevenStageFourEntriesChunk042_valid⟩, degreeSevenStageFourEntriesChunk043_valid⟩, degreeSevenStageFourEntriesChunk044_valid⟩, degreeSevenStageFourEntriesChunk045_valid⟩, degreeSevenStageFourEntriesChunk046_valid⟩, degreeSevenStageFourEntriesChunk047_valid⟩, degreeSevenStageFourEntriesChunk048_valid⟩, degreeSevenStageFourEntriesChunk049_valid⟩, degreeSevenStageFourEntriesChunk050_valid⟩, degreeSevenStageFourEntriesChunk051_valid⟩, degreeSevenStageFourEntriesChunk052_valid⟩, degreeSevenStageFourEntriesChunk053_valid⟩, degreeSevenStageFourEntriesChunk054_valid⟩, degreeSevenStageFourEntriesChunk055_valid⟩, degreeSevenStageFourEntriesChunk056_valid⟩, degreeSevenStageFourEntriesChunk057_valid⟩, degreeSevenStageFourEntriesChunk058_valid⟩, degreeSevenStageFourEntriesChunk059_valid⟩, degreeSevenStageFourEntriesChunk060_valid⟩, degreeSevenStageFourEntriesChunk061_valid⟩, degreeSevenStageFourEntriesChunk062_valid⟩, degreeSevenStageFourEntriesChunk063_valid⟩, degreeSevenStageFourEntriesChunk064_valid⟩, degreeSevenStageFourEntriesChunk065_valid⟩

theorem degreeSevenStageFourRanges_checked :
    degreeSevenStageFourEntries.map (fun entry =>
      (entry.a6, entry.a5, entry.a4,
        quarticTranslationLowerBound entry.baseCoefficients
          (-16) 16 entry.secondRoot,
        quarticTranslationUpperBound entry.baseCoefficients
          entry.firstRoot entry.thirdRoot)) =
      degreeSevenStageFourExpectedRanges := by
  simp only [degreeSevenStageFourEntries,
    degreeSevenStageFourExpectedRanges, List.map_append,
    degreeSevenStageFourRangesChunk000_checked, degreeSevenStageFourRangesChunk001_checked, degreeSevenStageFourRangesChunk002_checked, degreeSevenStageFourRangesChunk003_checked, degreeSevenStageFourRangesChunk004_checked, degreeSevenStageFourRangesChunk005_checked, degreeSevenStageFourRangesChunk006_checked, degreeSevenStageFourRangesChunk007_checked, degreeSevenStageFourRangesChunk008_checked, degreeSevenStageFourRangesChunk009_checked, degreeSevenStageFourRangesChunk010_checked, degreeSevenStageFourRangesChunk011_checked, degreeSevenStageFourRangesChunk012_checked, degreeSevenStageFourRangesChunk013_checked, degreeSevenStageFourRangesChunk014_checked, degreeSevenStageFourRangesChunk015_checked, degreeSevenStageFourRangesChunk016_checked, degreeSevenStageFourRangesChunk017_checked, degreeSevenStageFourRangesChunk018_checked, degreeSevenStageFourRangesChunk019_checked, degreeSevenStageFourRangesChunk020_checked, degreeSevenStageFourRangesChunk021_checked, degreeSevenStageFourRangesChunk022_checked, degreeSevenStageFourRangesChunk023_checked, degreeSevenStageFourRangesChunk024_checked, degreeSevenStageFourRangesChunk025_checked, degreeSevenStageFourRangesChunk026_checked, degreeSevenStageFourRangesChunk027_checked, degreeSevenStageFourRangesChunk028_checked, degreeSevenStageFourRangesChunk029_checked, degreeSevenStageFourRangesChunk030_checked, degreeSevenStageFourRangesChunk031_checked, degreeSevenStageFourRangesChunk032_checked, degreeSevenStageFourRangesChunk033_checked, degreeSevenStageFourRangesChunk034_checked, degreeSevenStageFourRangesChunk035_checked, degreeSevenStageFourRangesChunk036_checked, degreeSevenStageFourRangesChunk037_checked, degreeSevenStageFourRangesChunk038_checked, degreeSevenStageFourRangesChunk039_checked, degreeSevenStageFourRangesChunk040_checked, degreeSevenStageFourRangesChunk041_checked, degreeSevenStageFourRangesChunk042_checked, degreeSevenStageFourRangesChunk043_checked, degreeSevenStageFourRangesChunk044_checked, degreeSevenStageFourRangesChunk045_checked, degreeSevenStageFourRangesChunk046_checked, degreeSevenStageFourRangesChunk047_checked, degreeSevenStageFourRangesChunk048_checked, degreeSevenStageFourRangesChunk049_checked, degreeSevenStageFourRangesChunk050_checked, degreeSevenStageFourRangesChunk051_checked, degreeSevenStageFourRangesChunk052_checked, degreeSevenStageFourRangesChunk053_checked, degreeSevenStageFourRangesChunk054_checked, degreeSevenStageFourRangesChunk055_checked, degreeSevenStageFourRangesChunk056_checked, degreeSevenStageFourRangesChunk057_checked, degreeSevenStageFourRangesChunk058_checked, degreeSevenStageFourRangesChunk059_checked, degreeSevenStageFourRangesChunk060_checked, degreeSevenStageFourRangesChunk061_checked, degreeSevenStageFourRangesChunk062_checked, degreeSevenStageFourRangesChunk063_checked, degreeSevenStageFourRangesChunk064_checked, degreeSevenStageFourRangesChunk065_checked]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Computing the total length unfolds all generated entries.
theorem degreeSevenStageFour_entry_count :
    degreeSevenStageFourEntries.length = 1636 := by
  calc
    degreeSevenStageFourEntries.length =
        (degreeSevenStageFourEntries.map fun entry =>
          (entry.a6, entry.a5, entry.a4)).length := by
      rw [List.length_map]
    _ = degreeSevenStageFourTopTriples.length := by
      rw [degreeSevenStageFourTopTriples_checked]
    _ = 1636 := by norm_num [degreeSevenStageFourTopTriples]

theorem degreeSevenStageThree_prefix_count_closed :
    degreeSevenStageThreePrefixes.length = 1641 := by
  simpa [degreeSevenStageThreePrefixes] using
    degreeSevenStageThree_prefix_count

theorem degreeSevenStageFour_prefix_count :
    (degreeSevenStageFourEntries.flatMap fun entry =>
      entry.a3Candidates.toList.map fun a3 =>
        (entry.a6, entry.a5, entry.a4, a3)).length = 48710 := by
  simp only [degreeSevenStageFourEntries, List.flatMap_append,
    List.length_append, degreeSevenStageFourPrefixCountChunk000, degreeSevenStageFourPrefixCountChunk001, degreeSevenStageFourPrefixCountChunk002, degreeSevenStageFourPrefixCountChunk003, degreeSevenStageFourPrefixCountChunk004, degreeSevenStageFourPrefixCountChunk005, degreeSevenStageFourPrefixCountChunk006, degreeSevenStageFourPrefixCountChunk007, degreeSevenStageFourPrefixCountChunk008, degreeSevenStageFourPrefixCountChunk009, degreeSevenStageFourPrefixCountChunk010, degreeSevenStageFourPrefixCountChunk011, degreeSevenStageFourPrefixCountChunk012, degreeSevenStageFourPrefixCountChunk013, degreeSevenStageFourPrefixCountChunk014, degreeSevenStageFourPrefixCountChunk015, degreeSevenStageFourPrefixCountChunk016, degreeSevenStageFourPrefixCountChunk017, degreeSevenStageFourPrefixCountChunk018, degreeSevenStageFourPrefixCountChunk019, degreeSevenStageFourPrefixCountChunk020, degreeSevenStageFourPrefixCountChunk021, degreeSevenStageFourPrefixCountChunk022, degreeSevenStageFourPrefixCountChunk023, degreeSevenStageFourPrefixCountChunk024, degreeSevenStageFourPrefixCountChunk025, degreeSevenStageFourPrefixCountChunk026, degreeSevenStageFourPrefixCountChunk027, degreeSevenStageFourPrefixCountChunk028, degreeSevenStageFourPrefixCountChunk029, degreeSevenStageFourPrefixCountChunk030, degreeSevenStageFourPrefixCountChunk031, degreeSevenStageFourPrefixCountChunk032, degreeSevenStageFourPrefixCountChunk033, degreeSevenStageFourPrefixCountChunk034, degreeSevenStageFourPrefixCountChunk035, degreeSevenStageFourPrefixCountChunk036, degreeSevenStageFourPrefixCountChunk037, degreeSevenStageFourPrefixCountChunk038, degreeSevenStageFourPrefixCountChunk039, degreeSevenStageFourPrefixCountChunk040, degreeSevenStageFourPrefixCountChunk041, degreeSevenStageFourPrefixCountChunk042, degreeSevenStageFourPrefixCountChunk043, degreeSevenStageFourPrefixCountChunk044, degreeSevenStageFourPrefixCountChunk045, degreeSevenStageFourPrefixCountChunk046, degreeSevenStageFourPrefixCountChunk047, degreeSevenStageFourPrefixCountChunk048, degreeSevenStageFourPrefixCountChunk049, degreeSevenStageFourPrefixCountChunk050, degreeSevenStageFourPrefixCountChunk051, degreeSevenStageFourPrefixCountChunk052, degreeSevenStageFourPrefixCountChunk053, degreeSevenStageFourPrefixCountChunk054, degreeSevenStageFourPrefixCountChunk055, degreeSevenStageFourPrefixCountChunk056, degreeSevenStageFourPrefixCountChunk057, degreeSevenStageFourPrefixCountChunk058, degreeSevenStageFourPrefixCountChunk059, degreeSevenStageFourPrefixCountChunk060, degreeSevenStageFourPrefixCountChunk061, degreeSevenStageFourPrefixCountChunk062, degreeSevenStageFourPrefixCountChunk063, degreeSevenStageFourPrefixCountChunk064, degreeSevenStageFourPrefixCountChunk065]

end

end TraceEuclidean
