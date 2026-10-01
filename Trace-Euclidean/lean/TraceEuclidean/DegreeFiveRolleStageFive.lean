import TraceEuclidean.DegreeFiveRolleStageFour
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk000
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk001
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk002
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk003
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk004
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk005
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk006
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk007
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk008
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk009
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk010
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk011
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk012
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk013
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk014
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk015
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk016
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk017
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk018
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk019
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk020
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk021
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk022
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk023
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk024
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk025
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk026
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk027
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk028
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk029
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk030
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk031
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk032
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk033
import TraceEuclidean.DegreeFiveRolleStageFiveCertificates.Chunk034

/-! Complete generated final-stage frontier for the quintic Rolle search. -/

namespace TraceEuclidean

def degreeFiveStageFiveEntries :
    List DegreeFiveStageFiveEntry :=
  degreeFiveStageFiveEntriesChunk000 ++
    degreeFiveStageFiveEntriesChunk001 ++
    degreeFiveStageFiveEntriesChunk002 ++
    degreeFiveStageFiveEntriesChunk003 ++
    degreeFiveStageFiveEntriesChunk004 ++
    degreeFiveStageFiveEntriesChunk005 ++
    degreeFiveStageFiveEntriesChunk006 ++
    degreeFiveStageFiveEntriesChunk007 ++
    degreeFiveStageFiveEntriesChunk008 ++
    degreeFiveStageFiveEntriesChunk009 ++
    degreeFiveStageFiveEntriesChunk010 ++
    degreeFiveStageFiveEntriesChunk011 ++
    degreeFiveStageFiveEntriesChunk012 ++
    degreeFiveStageFiveEntriesChunk013 ++
    degreeFiveStageFiveEntriesChunk014 ++
    degreeFiveStageFiveEntriesChunk015 ++
    degreeFiveStageFiveEntriesChunk016 ++
    degreeFiveStageFiveEntriesChunk017 ++
    degreeFiveStageFiveEntriesChunk018 ++
    degreeFiveStageFiveEntriesChunk019 ++
    degreeFiveStageFiveEntriesChunk020 ++
    degreeFiveStageFiveEntriesChunk021 ++
    degreeFiveStageFiveEntriesChunk022 ++
    degreeFiveStageFiveEntriesChunk023 ++
    degreeFiveStageFiveEntriesChunk024 ++
    degreeFiveStageFiveEntriesChunk025 ++
    degreeFiveStageFiveEntriesChunk026 ++
    degreeFiveStageFiveEntriesChunk027 ++
    degreeFiveStageFiveEntriesChunk028 ++
    degreeFiveStageFiveEntriesChunk029 ++
    degreeFiveStageFiveEntriesChunk030 ++
    degreeFiveStageFiveEntriesChunk031 ++
    degreeFiveStageFiveEntriesChunk032 ++
    degreeFiveStageFiveEntriesChunk033 ++
    degreeFiveStageFiveEntriesChunk034

/-- One complete finite split of a fourth-stage coefficient interval. -/
structure DegreeFiveStageFiveCoverage where
  a4 : ℤ
  a3 : ℤ
  a2 : ℤ
  lower : ℤ
  upper : ℤ
  survivingA1 : List ℤ
  rejectedA1Roots : List (ℤ × ℤ)
deriving DecidableEq, Repr

/-- A rejected quartic together with an integral common root of it and its
derivative. -/
structure DegreeFiveRejectedQuarticWitness where
  a4 : ℤ
  a3 : ℤ
  a2 : ℤ
  a1 : ℤ
  root : ℤ
deriving DecidableEq, Repr

namespace DegreeFiveStageFiveCoverage

def rangeRecord (coverage : DegreeFiveStageFiveCoverage) :
    ℤ × ℤ × ℤ × ℤ × ℤ :=
  (coverage.a4, coverage.a3, coverage.a2,
    coverage.lower, coverage.upper)

def topQuadruples (coverage : DegreeFiveStageFiveCoverage) :
    List (ℤ × ℤ × ℤ × ℤ) :=
  coverage.survivingA1.map fun a1 =>
    (coverage.a4, coverage.a3, coverage.a2, a1)

def rejectedQuadruples (coverage : DegreeFiveStageFiveCoverage) :
    List (ℤ × ℤ × ℤ × ℤ) :=
  coverage.rejectedA1Roots.map fun pair =>
    (coverage.a4, coverage.a3, coverage.a2, pair.1)

def rejectedWitnesses (coverage : DegreeFiveStageFiveCoverage) :
    List DegreeFiveRejectedQuarticWitness :=
  coverage.rejectedA1Roots.map fun pair =>
    ⟨coverage.a4, coverage.a3, coverage.a2, pair.1, pair.2⟩

/-- The recorded surviving and rejected values exhaust the exact integer
interval attached to this parent row. -/
def Valid (coverage : DegreeFiveStageFiveCoverage) : Prop :=
  integerIcc coverage.lower coverage.upper =
    (coverage.survivingA1 ++
      coverage.rejectedA1Roots.map Prod.fst).toFinset

instance (coverage : DegreeFiveStageFiveCoverage) :
    Decidable coverage.Valid := by
  unfold Valid
  infer_instance

end DegreeFiveStageFiveCoverage

/-- The 187 parent intervals, each split into simple-root and multiple-root
quartics. -/
def degreeFiveStageFiveCoverages :
    List DegreeFiveStageFiveCoverage :=
  [
    ⟨(-2 : ℤ), (-5 : ℤ), (-3 : ℤ), (0 : ℤ), (-1 : ℤ), [], []⟩,
    ⟨(-2 : ℤ), (-5 : ℤ), (-2 : ℤ), (0 : ℤ), (0 : ℤ), [(0 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-5 : ℤ), (-1 : ℤ), (0 : ℤ), (2 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-5 : ℤ), (0 : ℤ), (0 : ℤ), (3 : ℤ), [(1 : ℤ), (2 : ℤ), (3 : ℤ)], [((0 : ℤ), (0 : ℤ))]⟩,
    ⟨(-2 : ℤ), (-5 : ℤ), (1 : ℤ), (0 : ℤ), (5 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-5 : ℤ), (2 : ℤ), (0 : ℤ), (6 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-5 : ℤ), (3 : ℤ), (0 : ℤ), (8 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-5 : ℤ), (4 : ℤ), (0 : ℤ), (10 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-5 : ℤ), (5 : ℤ), (-1 : ℤ), (12 : ℤ), [(-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-5 : ℤ), (6 : ℤ), (-2 : ℤ), (14 : ℤ), [(-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-5 : ℤ), (7 : ℤ), (-2 : ℤ), (16 : ℤ), [(-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ)], [((16 : ℤ), (-1 : ℤ))]⟩,
    ⟨(-2 : ℤ), (-5 : ℤ), (8 : ℤ), (-3 : ℤ), (13 : ℤ), [(-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-5 : ℤ), (9 : ℤ), (-4 : ℤ), (10 : ℤ), [(-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-5 : ℤ), (10 : ℤ), (-5 : ℤ), (6 : ℤ), [(-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-5 : ℤ), (11 : ℤ), (-6 : ℤ), (3 : ℤ), [(-6 : ℤ), (-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-5 : ℤ), (12 : ℤ), (-7 : ℤ), (0 : ℤ), [(-7 : ℤ), (-6 : ℤ), (-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-5 : ℤ), (13 : ℤ), (-9 : ℤ), (-4 : ℤ), [(-9 : ℤ), (-8 : ℤ), (-7 : ℤ), (-6 : ℤ), (-5 : ℤ), (-4 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-5 : ℤ), (14 : ℤ), (-10 : ℤ), (-7 : ℤ), [(-10 : ℤ), (-9 : ℤ), (-8 : ℤ), (-7 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-5 : ℤ), (15 : ℤ), (-12 : ℤ), (-10 : ℤ), [(-12 : ℤ), (-11 : ℤ), (-10 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-5 : ℤ), (16 : ℤ), (-14 : ℤ), (-13 : ℤ), [(-14 : ℤ), (-13 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-5 : ℤ), (17 : ℤ), (-16 : ℤ), (-16 : ℤ), [], [((-16 : ℤ), (1 : ℤ))]⟩,
    ⟨(-2 : ℤ), (-5 : ℤ), (18 : ℤ), (-18 : ℤ), (-19 : ℤ), [], []⟩,
    ⟨(-2 : ℤ), (-4 : ℤ), (-2 : ℤ), (0 : ℤ), (-1 : ℤ), [], []⟩,
    ⟨(-2 : ℤ), (-4 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), [(0 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-4 : ℤ), (0 : ℤ), (0 : ℤ), (1 : ℤ), [(1 : ℤ)], [((0 : ℤ), (0 : ℤ))]⟩,
    ⟨(-2 : ℤ), (-4 : ℤ), (1 : ℤ), (0 : ℤ), (3 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-4 : ℤ), (2 : ℤ), (0 : ℤ), (4 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-4 : ℤ), (3 : ℤ), (0 : ℤ), (6 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-4 : ℤ), (4 : ℤ), (-1 : ℤ), (7 : ℤ), [(-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-4 : ℤ), (5 : ℤ), (-1 : ℤ), (9 : ℤ), [(-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-4 : ℤ), (6 : ℤ), (-2 : ℤ), (11 : ℤ), [(-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-4 : ℤ), (7 : ℤ), (-3 : ℤ), (8 : ℤ), [(-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-4 : ℤ), (8 : ℤ), (-4 : ℤ), (5 : ℤ), [(-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-4 : ℤ), (9 : ℤ), (-5 : ℤ), (1 : ℤ), [(-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-4 : ℤ), (10 : ℤ), (-6 : ℤ), (-2 : ℤ), [(-6 : ℤ), (-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-4 : ℤ), (11 : ℤ), (-7 : ℤ), (-5 : ℤ), [(-7 : ℤ), (-6 : ℤ), (-5 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-4 : ℤ), (12 : ℤ), (-9 : ℤ), (-8 : ℤ), [(-9 : ℤ), (-8 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-4 : ℤ), (13 : ℤ), (-11 : ℤ), (-11 : ℤ), [(-11 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-4 : ℤ), (14 : ℤ), (-13 : ℤ), (-13 : ℤ), [], [((-13 : ℤ), (1 : ℤ))]⟩,
    ⟨(-2 : ℤ), (-3 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), [(0 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-3 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), [], [((0 : ℤ), (0 : ℤ))]⟩,
    ⟨(-2 : ℤ), (-3 : ℤ), (1 : ℤ), (0 : ℤ), (2 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-3 : ℤ), (2 : ℤ), (0 : ℤ), (3 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-3 : ℤ), (3 : ℤ), (0 : ℤ), (4 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-3 : ℤ), (4 : ℤ), (-1 : ℤ), (6 : ℤ), [(-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-3 : ℤ), (5 : ℤ), (-2 : ℤ), (7 : ℤ), [(-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-3 : ℤ), (6 : ℤ), (-3 : ℤ), (3 : ℤ), [(-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-3 : ℤ), (7 : ℤ), (-4 : ℤ), (0 : ℤ), [(-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-3 : ℤ), (8 : ℤ), (-5 : ℤ), (-2 : ℤ), [(-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-3 : ℤ), (9 : ℤ), (-6 : ℤ), (-5 : ℤ), [(-6 : ℤ), (-5 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-3 : ℤ), (10 : ℤ), (-8 : ℤ), (-8 : ℤ), [(-8 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-3 : ℤ), (11 : ℤ), (-10 : ℤ), (-10 : ℤ), [], [((-10 : ℤ), (1 : ℤ))]⟩,
    ⟨(-2 : ℤ), (-2 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), [], [((0 : ℤ), (0 : ℤ))]⟩,
    ⟨(-2 : ℤ), (-2 : ℤ), (1 : ℤ), (0 : ℤ), (1 : ℤ), [(0 : ℤ), (1 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-2 : ℤ), (2 : ℤ), (0 : ℤ), (2 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-2 : ℤ), (3 : ℤ), (-1 : ℤ), (3 : ℤ), [(-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-2 : ℤ), (4 : ℤ), (-1 : ℤ), (3 : ℤ), [(-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-2 : ℤ), (5 : ℤ), (-2 : ℤ), (0 : ℤ), [(-2 : ℤ), (-1 : ℤ), (0 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-2 : ℤ), (6 : ℤ), (-3 : ℤ), (-3 : ℤ), [(-3 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-2 : ℤ), (7 : ℤ), (-5 : ℤ), (-5 : ℤ), [(-5 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), [], [((0 : ℤ), (0 : ℤ))]⟩,
    ⟨(-2 : ℤ), (-1 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), [(0 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-1 : ℤ), (2 : ℤ), (0 : ℤ), (1 : ℤ), [(0 : ℤ), (1 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-1 : ℤ), (3 : ℤ), (-1 : ℤ), (0 : ℤ), [(-1 : ℤ), (0 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-1 : ℤ), (4 : ℤ), (-2 : ℤ), (-2 : ℤ), [(-2 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (-1 : ℤ), (5 : ℤ), (-4 : ℤ), (-4 : ℤ), [], [((-4 : ℤ), (1 : ℤ))]⟩,
    ⟨(-2 : ℤ), (0 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), [(0 : ℤ)], []⟩,
    ⟨(-2 : ℤ), (0 : ℤ), (2 : ℤ), (-1 : ℤ), (-1 : ℤ), [], [((-1 : ℤ), (1 : ℤ))]⟩,
    ⟨(-2 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), [], [((0 : ℤ), (0 : ℤ))]⟩,
    ⟨(-1 : ℤ), (-6 : ℤ), (-6 : ℤ), (-2 : ℤ), (-3 : ℤ), [], []⟩,
    ⟨(-1 : ℤ), (-6 : ℤ), (-5 : ℤ), (-1 : ℤ), (-1 : ℤ), [(-1 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-6 : ℤ), (-4 : ℤ), (0 : ℤ), (1 : ℤ), [(0 : ℤ), (1 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-6 : ℤ), (-3 : ℤ), (0 : ℤ), (3 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-6 : ℤ), (-2 : ℤ), (0 : ℤ), (5 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ)], [((5 : ℤ), (-1 : ℤ))]⟩,
    ⟨(-1 : ℤ), (-6 : ℤ), (-1 : ℤ), (0 : ℤ), (7 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-6 : ℤ), (0 : ℤ), (0 : ℤ), (9 : ℤ), [(1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ)], [((0 : ℤ), (0 : ℤ))]⟩,
    ⟨(-1 : ℤ), (-6 : ℤ), (1 : ℤ), (0 : ℤ), (11 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-6 : ℤ), (2 : ℤ), (0 : ℤ), (13 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-6 : ℤ), (3 : ℤ), (0 : ℤ), (15 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-6 : ℤ), (4 : ℤ), (0 : ℤ), (16 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-6 : ℤ), (5 : ℤ), (-1 : ℤ), (13 : ℤ), [(-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-6 : ℤ), (6 : ℤ), (-1 : ℤ), (10 : ℤ), [(-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-6 : ℤ), (7 : ℤ), (-2 : ℤ), (7 : ℤ), [(-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-6 : ℤ), (8 : ℤ), (-3 : ℤ), (4 : ℤ), [(-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-6 : ℤ), (9 : ℤ), (-4 : ℤ), (1 : ℤ), [(-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-6 : ℤ), (10 : ℤ), (-5 : ℤ), (-1 : ℤ), [(-5 : ℤ), (-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-6 : ℤ), (11 : ℤ), (-6 : ℤ), (-4 : ℤ), [(-6 : ℤ), (-5 : ℤ), (-4 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-6 : ℤ), (12 : ℤ), (-7 : ℤ), (-7 : ℤ), [(-7 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-6 : ℤ), (13 : ℤ), (-9 : ℤ), (-9 : ℤ), [(-9 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-5 : ℤ), (-4 : ℤ), (-1 : ℤ), (-1 : ℤ), [(-1 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-5 : ℤ), (-3 : ℤ), (0 : ℤ), (0 : ℤ), [(0 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-5 : ℤ), (-2 : ℤ), (0 : ℤ), (2 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-5 : ℤ), (-1 : ℤ), (0 : ℤ), (4 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-5 : ℤ), (0 : ℤ), (0 : ℤ), (6 : ℤ), [(1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ)], [((0 : ℤ), (0 : ℤ))]⟩,
    ⟨(-1 : ℤ), (-5 : ℤ), (1 : ℤ), (0 : ℤ), (8 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ)], [((8 : ℤ), (-1 : ℤ))]⟩,
    ⟨(-1 : ℤ), (-5 : ℤ), (2 : ℤ), (0 : ℤ), (10 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-5 : ℤ), (3 : ℤ), (0 : ℤ), (12 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-5 : ℤ), (4 : ℤ), (-1 : ℤ), (10 : ℤ), [(-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-5 : ℤ), (5 : ℤ), (-1 : ℤ), (7 : ℤ), [(-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-5 : ℤ), (6 : ℤ), (-2 : ℤ), (4 : ℤ), [(-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-5 : ℤ), (7 : ℤ), (-3 : ℤ), (1 : ℤ), [(-3 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-5 : ℤ), (8 : ℤ), (-4 : ℤ), (-1 : ℤ), [(-4 : ℤ), (-3 : ℤ), (-2 : ℤ), (-1 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-5 : ℤ), (9 : ℤ), (-5 : ℤ), (-4 : ℤ), [(-5 : ℤ), (-4 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-5 : ℤ), (10 : ℤ), (-6 : ℤ), (-6 : ℤ), [(-6 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-5 : ℤ), (11 : ℤ), (-8 : ℤ), (-8 : ℤ), [], [((-8 : ℤ), (1 : ℤ))]⟩,
    ⟨(-1 : ℤ), (-4 : ℤ), (-3 : ℤ), (0 : ℤ), (-1 : ℤ), [], []⟩,
    ⟨(-1 : ℤ), (-4 : ℤ), (-2 : ℤ), (0 : ℤ), (0 : ℤ), [(0 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-4 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), [(0 : ℤ), (1 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-4 : ℤ), (0 : ℤ), (0 : ℤ), (3 : ℤ), [(1 : ℤ), (2 : ℤ), (3 : ℤ)], [((0 : ℤ), (0 : ℤ))]⟩,
    ⟨(-1 : ℤ), (-4 : ℤ), (1 : ℤ), (0 : ℤ), (5 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-4 : ℤ), (2 : ℤ), (0 : ℤ), (7 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-4 : ℤ), (3 : ℤ), (0 : ℤ), (7 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-4 : ℤ), (4 : ℤ), (-1 : ℤ), (4 : ℤ), [(-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-4 : ℤ), (5 : ℤ), (-1 : ℤ), (1 : ℤ), [(-1 : ℤ), (0 : ℤ), (1 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-4 : ℤ), (6 : ℤ), (-2 : ℤ), (-1 : ℤ), [(-2 : ℤ), (-1 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-4 : ℤ), (7 : ℤ), (-3 : ℤ), (-3 : ℤ), [(-3 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-4 : ℤ), (8 : ℤ), (-5 : ℤ), (-5 : ℤ), [], [((-5 : ℤ), (1 : ℤ))]⟩,
    ⟨(-1 : ℤ), (-3 : ℤ), (-2 : ℤ), (0 : ℤ), (-1 : ℤ), [], []⟩,
    ⟨(-1 : ℤ), (-3 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), [(0 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-3 : ℤ), (0 : ℤ), (0 : ℤ), (1 : ℤ), [(1 : ℤ)], [((0 : ℤ), (0 : ℤ))]⟩,
    ⟨(-1 : ℤ), (-3 : ℤ), (1 : ℤ), (0 : ℤ), (3 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-3 : ℤ), (2 : ℤ), (0 : ℤ), (4 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-3 : ℤ), (3 : ℤ), (0 : ℤ), (2 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-3 : ℤ), (4 : ℤ), (-1 : ℤ), (0 : ℤ), [(-1 : ℤ), (0 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-3 : ℤ), (5 : ℤ), (-2 : ℤ), (-2 : ℤ), [], [((-2 : ℤ), (1 : ℤ))]⟩,
    ⟨(-1 : ℤ), (-2 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), [], [((0 : ℤ), (0 : ℤ))]⟩,
    ⟨(-1 : ℤ), (-2 : ℤ), (1 : ℤ), (0 : ℤ), (1 : ℤ), [(0 : ℤ), (1 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-2 : ℤ), (2 : ℤ), (0 : ℤ), (1 : ℤ), [(0 : ℤ)], [((1 : ℤ), (1 : ℤ))]⟩,
    ⟨(-1 : ℤ), (-2 : ℤ), (3 : ℤ), (-1 : ℤ), (-1 : ℤ), [(-1 : ℤ)], []⟩,
    ⟨(-1 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), [], [((0 : ℤ), (0 : ℤ))]⟩,
    ⟨(-1 : ℤ), (-1 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), [(0 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-6 : ℤ), (-9 : ℤ), (-4 : ℤ), (-5 : ℤ), [], []⟩,
    ⟨(0 : ℤ), (-6 : ℤ), (-8 : ℤ), (-3 : ℤ), (-3 : ℤ), [], [((-3 : ℤ), (-1 : ℤ))]⟩,
    ⟨(0 : ℤ), (-6 : ℤ), (-7 : ℤ), (-2 : ℤ), (-1 : ℤ), [(-2 : ℤ), (-1 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-6 : ℤ), (-6 : ℤ), (-2 : ℤ), (1 : ℤ), [(-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-6 : ℤ), (-5 : ℤ), (-1 : ℤ), (3 : ℤ), [(-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-6 : ℤ), (-4 : ℤ), (0 : ℤ), (5 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-6 : ℤ), (-3 : ℤ), (0 : ℤ), (8 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-6 : ℤ), (-2 : ℤ), (0 : ℤ), (10 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-6 : ℤ), (-1 : ℤ), (0 : ℤ), (13 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-6 : ℤ), (0 : ℤ), (0 : ℤ), (16 : ℤ), [(1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ), (14 : ℤ), (15 : ℤ), (16 : ℤ)], [((0 : ℤ), (0 : ℤ))]⟩,
    ⟨(0 : ℤ), (-6 : ℤ), (1 : ℤ), (0 : ℤ), (13 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ), (12 : ℤ), (13 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-6 : ℤ), (2 : ℤ), (0 : ℤ), (10 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-6 : ℤ), (3 : ℤ), (0 : ℤ), (8 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-6 : ℤ), (4 : ℤ), (0 : ℤ), (5 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-6 : ℤ), (5 : ℤ), (-1 : ℤ), (3 : ℤ), [(-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-6 : ℤ), (6 : ℤ), (-2 : ℤ), (1 : ℤ), [(-2 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-6 : ℤ), (7 : ℤ), (-2 : ℤ), (-1 : ℤ), [(-2 : ℤ), (-1 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-6 : ℤ), (8 : ℤ), (-3 : ℤ), (-3 : ℤ), [], [((-3 : ℤ), (1 : ℤ))]⟩,
    ⟨(0 : ℤ), (-6 : ℤ), (9 : ℤ), (-4 : ℤ), (-5 : ℤ), [], []⟩,
    ⟨(0 : ℤ), (-5 : ℤ), (-7 : ℤ), (-3 : ℤ), (-4 : ℤ), [], []⟩,
    ⟨(0 : ℤ), (-5 : ℤ), (-6 : ℤ), (-2 : ℤ), (-2 : ℤ), [(-2 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-5 : ℤ), (-5 : ℤ), (-1 : ℤ), (0 : ℤ), [(-1 : ℤ)], [((0 : ℤ), (-1 : ℤ))]⟩,
    ⟨(0 : ℤ), (-5 : ℤ), (-4 : ℤ), (-1 : ℤ), (2 : ℤ), [(-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-5 : ℤ), (-3 : ℤ), (0 : ℤ), (4 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-5 : ℤ), (-2 : ℤ), (0 : ℤ), (6 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-5 : ℤ), (-1 : ℤ), (0 : ℤ), (8 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-5 : ℤ), (0 : ℤ), (0 : ℤ), (11 : ℤ), [(1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ), (10 : ℤ), (11 : ℤ)], [((0 : ℤ), (0 : ℤ))]⟩,
    ⟨(0 : ℤ), (-5 : ℤ), (1 : ℤ), (0 : ℤ), (8 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-5 : ℤ), (2 : ℤ), (0 : ℤ), (6 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-5 : ℤ), (3 : ℤ), (0 : ℤ), (4 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-5 : ℤ), (4 : ℤ), (-1 : ℤ), (2 : ℤ), [(-1 : ℤ), (0 : ℤ), (1 : ℤ), (2 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-5 : ℤ), (5 : ℤ), (-1 : ℤ), (0 : ℤ), [(-1 : ℤ)], [((0 : ℤ), (1 : ℤ))]⟩,
    ⟨(0 : ℤ), (-5 : ℤ), (6 : ℤ), (-2 : ℤ), (-2 : ℤ), [(-2 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-5 : ℤ), (7 : ℤ), (-3 : ℤ), (-4 : ℤ), [], []⟩,
    ⟨(0 : ℤ), (-4 : ℤ), (-5 : ℤ), (-2 : ℤ), (-3 : ℤ), [], []⟩,
    ⟨(0 : ℤ), (-4 : ℤ), (-4 : ℤ), (-1 : ℤ), (-1 : ℤ), [(-1 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-4 : ℤ), (-3 : ℤ), (0 : ℤ), (1 : ℤ), [(0 : ℤ), (1 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-4 : ℤ), (-2 : ℤ), (0 : ℤ), (3 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ)], [((3 : ℤ), (-1 : ℤ))]⟩,
    ⟨(0 : ℤ), (-4 : ℤ), (-1 : ℤ), (0 : ℤ), (5 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-4 : ℤ), (0 : ℤ), (0 : ℤ), (7 : ℤ), [(1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ)], [((0 : ℤ), (0 : ℤ))]⟩,
    ⟨(0 : ℤ), (-4 : ℤ), (1 : ℤ), (0 : ℤ), (5 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-4 : ℤ), (2 : ℤ), (0 : ℤ), (3 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ)], [((3 : ℤ), (1 : ℤ))]⟩,
    ⟨(0 : ℤ), (-4 : ℤ), (3 : ℤ), (0 : ℤ), (1 : ℤ), [(0 : ℤ), (1 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-4 : ℤ), (4 : ℤ), (-1 : ℤ), (-1 : ℤ), [(-1 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-4 : ℤ), (5 : ℤ), (-2 : ℤ), (-3 : ℤ), [], []⟩,
    ⟨(0 : ℤ), (-3 : ℤ), (-3 : ℤ), (-1 : ℤ), (-1 : ℤ), [(-1 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-3 : ℤ), (-2 : ℤ), (0 : ℤ), (0 : ℤ), [(0 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-3 : ℤ), (-1 : ℤ), (0 : ℤ), (2 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-3 : ℤ), (0 : ℤ), (0 : ℤ), (4 : ℤ), [(1 : ℤ), (2 : ℤ), (3 : ℤ), (4 : ℤ)], [((0 : ℤ), (0 : ℤ))]⟩,
    ⟨(0 : ℤ), (-3 : ℤ), (1 : ℤ), (0 : ℤ), (2 : ℤ), [(0 : ℤ), (1 : ℤ), (2 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-3 : ℤ), (2 : ℤ), (0 : ℤ), (0 : ℤ), [(0 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-3 : ℤ), (3 : ℤ), (-1 : ℤ), (-1 : ℤ), [(-1 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), [(0 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-2 : ℤ), (0 : ℤ), (0 : ℤ), (1 : ℤ), [(1 : ℤ)], [((0 : ℤ), (0 : ℤ))]⟩,
    ⟨(0 : ℤ), (-2 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), [(0 : ℤ)], []⟩,
    ⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), [], [((0 : ℤ), (0 : ℤ))]⟩
  ]

/-- Coefficient quadruples represented by the certified quartic rows. -/
def degreeFiveStageFiveTopQuadruples : List (ℤ × ℤ × ℤ × ℤ) :=
  degreeFiveStageFiveCoverages.flatMap
    DegreeFiveStageFiveCoverage.topQuadruples

/-- The fourth-stage quadruples whose quartic has a multiple root. -/
def degreeFiveStageFiveRejectedQuadruples : List (ℤ × ℤ × ℤ × ℤ) :=
  degreeFiveStageFiveCoverages.flatMap
    DegreeFiveStageFiveCoverage.rejectedQuadruples

/-- Each rejected quadruple together with one integral common root of the
quartic and its derivative. -/
def degreeFiveStageFiveRejectedWitnesses :
    List DegreeFiveRejectedQuarticWitness :=
  degreeFiveStageFiveCoverages.flatMap
    DegreeFiveStageFiveCoverage.rejectedWitnesses

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem degreeFiveStageFiveCoverageRanges_checked :
    degreeFiveStageFiveCoverages.map
        DegreeFiveStageFiveCoverage.rangeRecord =
      degreeFiveStageFourExpectedRanges := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Pure kernel evaluation checks all 187 finite interval partitions.
theorem degreeFiveStageFiveCoverages_valid :
    degreeFiveStageFiveCoverages.Forall
      DegreeFiveStageFiveCoverage.Valid := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every generated rejection carries an exactly checked common root. -/
theorem degreeFiveStageFiveRejectedWitnesses_valid :
    degreeFiveStageFiveRejectedWitnesses.Forall fun witness =>
      integerPolynomialRationalEval
          [witness.a1, 2 * witness.a2, 3 * witness.a3,
            4 * witness.a4, 5] witness.root = 0 ∧
        integerPolynomialRationalEval
          [witness.a2, 3 * witness.a3,
            6 * witness.a4, 10] witness.root = 0 := by
  norm_num [degreeFiveStageFiveRejectedWitnesses,
    degreeFiveStageFiveCoverages,
    DegreeFiveStageFiveCoverage.rejectedWitnesses,
    integerPolynomialRationalEval, DensePolynomial.eval]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem degreeFiveStageFiveTopQuadruples_checked :
    degreeFiveStageFiveEntries.map (fun entry =>
      (entry.a4, entry.a3, entry.a2, entry.a1)) =
        degreeFiveStageFiveTopQuadruples := by
  simp only [degreeFiveStageFiveEntries, List.map_append,
    degreeFiveStageFiveEntriesChunk000, degreeFiveStageFiveEntriesChunk001, degreeFiveStageFiveEntriesChunk002, degreeFiveStageFiveEntriesChunk003, degreeFiveStageFiveEntriesChunk004, degreeFiveStageFiveEntriesChunk005, degreeFiveStageFiveEntriesChunk006, degreeFiveStageFiveEntriesChunk007, degreeFiveStageFiveEntriesChunk008, degreeFiveStageFiveEntriesChunk009, degreeFiveStageFiveEntriesChunk010, degreeFiveStageFiveEntriesChunk011, degreeFiveStageFiveEntriesChunk012, degreeFiveStageFiveEntriesChunk013, degreeFiveStageFiveEntriesChunk014, degreeFiveStageFiveEntriesChunk015, degreeFiveStageFiveEntriesChunk016, degreeFiveStageFiveEntriesChunk017, degreeFiveStageFiveEntriesChunk018, degreeFiveStageFiveEntriesChunk019, degreeFiveStageFiveEntriesChunk020, degreeFiveStageFiveEntriesChunk021, degreeFiveStageFiveEntriesChunk022, degreeFiveStageFiveEntriesChunk023, degreeFiveStageFiveEntriesChunk024, degreeFiveStageFiveEntriesChunk025, degreeFiveStageFiveEntriesChunk026, degreeFiveStageFiveEntriesChunk027, degreeFiveStageFiveEntriesChunk028, degreeFiveStageFiveEntriesChunk029, degreeFiveStageFiveEntriesChunk030, degreeFiveStageFiveEntriesChunk031, degreeFiveStageFiveEntriesChunk032, degreeFiveStageFiveEntriesChunk033, degreeFiveStageFiveEntriesChunk034, degreeFiveStageFiveTopQuadruples,
    degreeFiveStageFiveCoverages]
  rfl

/-- The explicit 900-element fourth-stage prefix list, separated into the
864 simple-root rows and the 36 rejected multiple-root rows.  Its relation
to the kernel-checked coefficient intervals is proved in the completeness
module. -/
def degreeFiveStageFourPrefixes : List (ℤ × ℤ × ℤ × ℤ) :=
  degreeFiveStageFiveTopQuadruples ++
    degreeFiveStageFiveRejectedQuadruples

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation checks the exact 900 = 864 + 36 partition.
theorem degreeFiveStageFive_partition :
    degreeFiveStageFourPrefixes.toFinset =
      degreeFiveStageFiveTopQuadruples.toFinset ∪
        degreeFiveStageFiveRejectedQuadruples.toFinset := by
  simp [degreeFiveStageFourPrefixes]

theorem degreeFiveStageFiveEntries_valid :
    degreeFiveStageFiveEntries.Forall
      DegreeFiveStageFiveEntry.Valid := by
  simp only [degreeFiveStageFiveEntries, List.forall_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨degreeFiveStageFiveEntriesChunk000_valid, degreeFiveStageFiveEntriesChunk001_valid⟩, degreeFiveStageFiveEntriesChunk002_valid⟩, degreeFiveStageFiveEntriesChunk003_valid⟩, degreeFiveStageFiveEntriesChunk004_valid⟩, degreeFiveStageFiveEntriesChunk005_valid⟩, degreeFiveStageFiveEntriesChunk006_valid⟩, degreeFiveStageFiveEntriesChunk007_valid⟩, degreeFiveStageFiveEntriesChunk008_valid⟩, degreeFiveStageFiveEntriesChunk009_valid⟩, degreeFiveStageFiveEntriesChunk010_valid⟩, degreeFiveStageFiveEntriesChunk011_valid⟩, degreeFiveStageFiveEntriesChunk012_valid⟩, degreeFiveStageFiveEntriesChunk013_valid⟩, degreeFiveStageFiveEntriesChunk014_valid⟩, degreeFiveStageFiveEntriesChunk015_valid⟩, degreeFiveStageFiveEntriesChunk016_valid⟩, degreeFiveStageFiveEntriesChunk017_valid⟩, degreeFiveStageFiveEntriesChunk018_valid⟩, degreeFiveStageFiveEntriesChunk019_valid⟩, degreeFiveStageFiveEntriesChunk020_valid⟩, degreeFiveStageFiveEntriesChunk021_valid⟩, degreeFiveStageFiveEntriesChunk022_valid⟩, degreeFiveStageFiveEntriesChunk023_valid⟩, degreeFiveStageFiveEntriesChunk024_valid⟩, degreeFiveStageFiveEntriesChunk025_valid⟩, degreeFiveStageFiveEntriesChunk026_valid⟩, degreeFiveStageFiveEntriesChunk027_valid⟩, degreeFiveStageFiveEntriesChunk028_valid⟩, degreeFiveStageFiveEntriesChunk029_valid⟩, degreeFiveStageFiveEntriesChunk030_valid⟩, degreeFiveStageFiveEntriesChunk031_valid⟩, degreeFiveStageFiveEntriesChunk032_valid⟩, degreeFiveStageFiveEntriesChunk033_valid⟩, degreeFiveStageFiveEntriesChunk034_valid⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem degreeFiveStageFive_entry_count :
    degreeFiveStageFiveEntries.length = 864 := by
  norm_num [degreeFiveStageFiveEntries, degreeFiveStageFiveEntriesChunk000, degreeFiveStageFiveEntriesChunk001, degreeFiveStageFiveEntriesChunk002, degreeFiveStageFiveEntriesChunk003, degreeFiveStageFiveEntriesChunk004, degreeFiveStageFiveEntriesChunk005, degreeFiveStageFiveEntriesChunk006, degreeFiveStageFiveEntriesChunk007, degreeFiveStageFiveEntriesChunk008, degreeFiveStageFiveEntriesChunk009, degreeFiveStageFiveEntriesChunk010, degreeFiveStageFiveEntriesChunk011, degreeFiveStageFiveEntriesChunk012, degreeFiveStageFiveEntriesChunk013, degreeFiveStageFiveEntriesChunk014, degreeFiveStageFiveEntriesChunk015, degreeFiveStageFiveEntriesChunk016, degreeFiveStageFiveEntriesChunk017, degreeFiveStageFiveEntriesChunk018, degreeFiveStageFiveEntriesChunk019, degreeFiveStageFiveEntriesChunk020, degreeFiveStageFiveEntriesChunk021, degreeFiveStageFiveEntriesChunk022, degreeFiveStageFiveEntriesChunk023, degreeFiveStageFiveEntriesChunk024, degreeFiveStageFiveEntriesChunk025, degreeFiveStageFiveEntriesChunk026, degreeFiveStageFiveEntriesChunk027, degreeFiveStageFiveEntriesChunk028, degreeFiveStageFiveEntriesChunk029, degreeFiveStageFiveEntriesChunk030, degreeFiveStageFiveEntriesChunk031, degreeFiveStageFiveEntriesChunk032, degreeFiveStageFiveEntriesChunk033, degreeFiveStageFiveEntriesChunk034]

theorem degreeFiveStageFive_prefix_count :
    (degreeFiveStageFiveEntries.flatMap fun entry =>
      entry.a0Candidates.toList.map fun a0 =>
        (entry.a4, entry.a3, entry.a2, entry.a1, a0)).length = 1217 := by
  simp only [degreeFiveStageFiveEntries, List.flatMap_append,
    List.length_append, degreeFiveStageFivePrefixCountChunk000, degreeFiveStageFivePrefixCountChunk001, degreeFiveStageFivePrefixCountChunk002, degreeFiveStageFivePrefixCountChunk003, degreeFiveStageFivePrefixCountChunk004, degreeFiveStageFivePrefixCountChunk005, degreeFiveStageFivePrefixCountChunk006, degreeFiveStageFivePrefixCountChunk007, degreeFiveStageFivePrefixCountChunk008, degreeFiveStageFivePrefixCountChunk009, degreeFiveStageFivePrefixCountChunk010, degreeFiveStageFivePrefixCountChunk011, degreeFiveStageFivePrefixCountChunk012, degreeFiveStageFivePrefixCountChunk013, degreeFiveStageFivePrefixCountChunk014, degreeFiveStageFivePrefixCountChunk015, degreeFiveStageFivePrefixCountChunk016, degreeFiveStageFivePrefixCountChunk017, degreeFiveStageFivePrefixCountChunk018, degreeFiveStageFivePrefixCountChunk019, degreeFiveStageFivePrefixCountChunk020, degreeFiveStageFivePrefixCountChunk021, degreeFiveStageFivePrefixCountChunk022, degreeFiveStageFivePrefixCountChunk023, degreeFiveStageFivePrefixCountChunk024, degreeFiveStageFivePrefixCountChunk025, degreeFiveStageFivePrefixCountChunk026, degreeFiveStageFivePrefixCountChunk027, degreeFiveStageFivePrefixCountChunk028, degreeFiveStageFivePrefixCountChunk029, degreeFiveStageFivePrefixCountChunk030, degreeFiveStageFivePrefixCountChunk031, degreeFiveStageFivePrefixCountChunk032, degreeFiveStageFivePrefixCountChunk033, degreeFiveStageFivePrefixCountChunk034]

end TraceEuclidean
