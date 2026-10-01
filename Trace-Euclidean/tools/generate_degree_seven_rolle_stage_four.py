#!/usr/bin/env python3
"""Generate exact cubic-root certificates for the second septic Rolle step.

The input is the pure-kernel stage-three frontier. Five triples give a cubic
with a multiple root and are discarded. For every remaining triple this
script finds three rational isolating intervals and the exact integer range
for ``a3``. Lean rechecks all sign changes and interval bounds.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

from sympy import Poly, Rational, symbols

from generate_degree_seven_rolle_stage_three import (
    Entry as StageThreeEntry,
    RootInterval,
    compute_entries as compute_stage_three_entries,
    interval_eval,
    lean_int,
    lean_interval,
)


ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "lean" / "TraceEuclidean"
BASE_OUTPUT = LEAN_ROOT / "DegreeSevenRolleStageFourBase.lean"
CHUNK_DIR = LEAN_ROOT / "DegreeSevenRolleStageFourCertificates"
UMBRELLA_OUTPUT = LEAN_ROOT / "DegreeSevenRolleStageFour.lean"
CHUNK_SIZE = 25
ROOT_INTERVAL_EPSILON = Rational(1, 2**12)
X = symbols("x")


@dataclass(frozen=True)
class StageFourEntry:
    a6: int
    a5: int
    a4: int
    roots: tuple[RootInterval, RootInterval, RootInterval]
    a3_lower: int
    a3_upper: int


def as_fraction(value: Rational) -> Fraction:
    return Fraction(int(value.p), int(value.q))


def fraction_ceil(value: Fraction) -> int:
    return -((-value.numerator) // value.denominator)


def fraction_floor(value: Fraction) -> int:
    return value.numerator // value.denominator


def isolate_cubic(
    a6: int, a5: int, a4: int
) -> tuple[RootInterval, RootInterval, RootInterval] | None:
    polynomial = Poly(
        35 * X**3 + 15 * a6 * X**2 + 5 * a5 * X + a4,
        X,
        domain="QQ",
    )
    raw_intervals = polynomial.intervals(eps=ROOT_INTERVAL_EPSILON)
    if len(raw_intervals) != 3 or any(
        multiplicity != 1 for _, multiplicity in raw_intervals
    ):
        return None
    intervals: list[RootInterval] = []
    for (lower, upper), _ in raw_intervals:
        lo = as_fraction(lower)
        hi = as_fraction(upper)
        if lo == hi:
            delta = Fraction(1, 2**12)
            lo -= delta
            hi += delta
        intervals.append(RootInterval(lo, hi))
    if not all(
        left.upper < right.lower
        for left, right in zip(intervals, intervals[1:])
    ):
        raise ArithmeticError("cubic root intervals are not strictly separated")
    return intervals[0], intervals[1], intervals[2]


def a3_bounds(
    a6: int,
    a5: int,
    a4: int,
    roots: tuple[RootInterval, RootInterval, RootInterval],
) -> tuple[int, int]:
    base = [0, 4 * a4, 10 * a5, 20 * a6, 35]
    samples = (
        interval_eval(base, RootInterval(Fraction(-16), Fraction(-16))),
        interval_eval(base, roots[0]),
        interval_eval(base, roots[1]),
        interval_eval(base, roots[2]),
        interval_eval(base, RootInterval(Fraction(16), Fraction(16))),
    )
    lower = max(fraction_ceil(-samples[index][1]) for index in (0, 2, 4))
    upper = min(fraction_floor(-samples[index][0]) for index in (1, 3))
    return lower, upper


def stage_three_values(entry: StageThreeEntry) -> range:
    return range(entry.a4_lower, entry.a4_upper + 1)


REJECTED = [
    (-3, -3, 25),
    (-3, 0, 0),
    (-2, -9, 40),
    (-2, 0, 0),
    (-1, 0, 0),
]


def compute_entries() -> list[StageFourEntry]:
    entries: list[StageFourEntry] = []
    rejected: list[tuple[int, int, int]] = []
    for parent in compute_stage_three_entries():
        for a4 in stage_three_values(parent):
            roots = isolate_cubic(parent.a6, parent.a5, a4)
            if roots is None:
                rejected.append((parent.a6, parent.a5, a4))
                continue
            lower, upper = a3_bounds(parent.a6, parent.a5, a4, roots)
            entries.append(
                StageFourEntry(
                    parent.a6,
                    parent.a5,
                    a4,
                    roots,
                    lower,
                    upper,
                )
            )

    if rejected != REJECTED:
        raise ArithmeticError(f"unexpected nonsimple cubics: {rejected}")
    if len(entries) != 1636:
        raise ArithmeticError(f"expected 1636 cubic rows, found {len(entries)}")
    total = sum(
        max(0, entry.a3_upper - entry.a3_lower + 1) for entry in entries
    )
    if total != 48710:
        raise ArithmeticError(f"expected 48710 quartic prefixes, found {total}")
    return entries


def chunks(entries: list[StageFourEntry]) -> list[list[StageFourEntry]]:
    return [
        entries[start : start + CHUNK_SIZE]
        for start in range(0, len(entries), CHUNK_SIZE)
    ]


def render_base() -> str:
    return """import TraceEuclidean.VoightHigherCoefficientPruning

/-! Shared definitions for the generated degree-seven fourth Rolle stage. -/

namespace TraceEuclidean

/-- A certified cubic derivative stage and the top coefficients determining
it. -/
structure DegreeSevenStageFourEntry where
  a6 : ℤ
  a5 : ℤ
  a4 : ℤ
  firstRoot : RationalRootInterval
  secondRoot : RationalRootInterval
  thirdRoot : RationalRootInterval
deriving DecidableEq, Repr

namespace DegreeSevenStageFourEntry

def derivativeCoefficients (entry : DegreeSevenStageFourEntry) : List ℤ :=
  [entry.a4, 5 * entry.a5, 15 * entry.a6, 35]

def baseCoefficients (entry : DegreeSevenStageFourEntry) : List ℤ :=
  [0, 4 * entry.a4, 10 * entry.a5, 20 * entry.a6, 35]

def rootIntervals (entry : DegreeSevenStageFourEntry) :
    List RationalRootInterval :=
  [entry.firstRoot, entry.secondRoot, entry.thirdRoot]

def Valid (entry : DegreeSevenStageFourEntry) : Prop :=
  GeneralRationalRootIntervalCertificate.Valid 3
    entry.derivativeCoefficients entry.rootIntervals

def a3Candidates (entry : DegreeSevenStageFourEntry) : Finset ℤ :=
  quarticTranslationCandidates entry.baseCoefficients
    (-16) 16 entry.firstRoot entry.secondRoot entry.thirdRoot

end DegreeSevenStageFourEntry

end TraceEuclidean
"""


def chunk_name(index: int) -> str:
    return f"Chunk{index:03d}"


def render_chunk(index: int, entries: list[StageFourEntry]) -> str:
    name = chunk_name(index)
    entry_lines = ",\n".join(
        "    ⟨"
        + ", ".join(
            (
                lean_int(entry.a6),
                lean_int(entry.a5),
                lean_int(entry.a4),
                *(lean_interval(root) for root in entry.roots),
            )
        )
        + "⟩"
        for entry in entries
    )
    range_lines = ",\n".join(
        f"    ({lean_int(entry.a6)}, {lean_int(entry.a5)}, "
        f"{lean_int(entry.a4)}, {lean_int(entry.a3_lower)}, "
        f"{lean_int(entry.a3_upper)})"
        for entry in entries
    )
    count = sum(
        max(0, entry.a3_upper - entry.a3_lower + 1) for entry in entries
    )
    return f"""import TraceEuclidean.DegreeSevenRolleStageFourBase

/-! Generated exact cubic root intervals, {name}. -/

namespace TraceEuclidean

set_option linter.style.longLine false

def degreeSevenStageFourEntries{name} :
    List DegreeSevenStageFourEntry :=
  [
{entry_lines}
  ]

def degreeSevenStageFourExpectedRanges{name} :
    List (ℤ × ℤ × ℤ × ℤ × ℤ) :=
  [
{range_lines}
  ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Exact rational sign checks for this generated chunk require deep reduction.
theorem degreeSevenStageFourEntries{name}_valid :
    degreeSevenStageFourEntries{name}.Forall
      DegreeSevenStageFourEntry.Valid := by
  norm_num [degreeSevenStageFourEntries{name},
    DegreeSevenStageFourEntry.Valid,
    DegreeSevenStageFourEntry.derivativeCoefficients,
    DegreeSevenStageFourEntry.rootIntervals,
    GeneralRationalRootIntervalCertificate.Valid,
    integerPolynomialRationalEval, DensePolynomial.eval]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Exact Horner interval evaluation for this generated chunk is kernel checked.
theorem degreeSevenStageFourRanges{name}_checked :
    degreeSevenStageFourEntries{name}.map (fun entry =>
      (entry.a6, entry.a5, entry.a4,
        quarticTranslationLowerBound entry.baseCoefficients
          (-16) 16 entry.secondRoot,
        quarticTranslationUpperBound entry.baseCoefficients
          entry.firstRoot entry.thirdRoot)) =
      degreeSevenStageFourExpectedRanges{name} := by
  norm_num [degreeSevenStageFourEntries{name},
    degreeSevenStageFourExpectedRanges{name},
    DegreeSevenStageFourEntry.baseCoefficients,
    quarticTranslationLowerBound, quarticTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The finite candidate count is reduced by the Lean kernel.
theorem degreeSevenStageFourPrefixCount{name} :
    (degreeSevenStageFourEntries{name}.flatMap fun entry =>
      entry.a3Candidates.toList.map fun a3 =>
        (entry.a6, entry.a5, entry.a4, a3)).length = {count} := by
  norm_num [degreeSevenStageFourEntries{name},
    DegreeSevenStageFourEntry.a3Candidates,
    DegreeSevenStageFourEntry.baseCoefficients,
    quarticTranslationCandidates, integerIcc,
    quarticTranslationLowerBound, quarticTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat]

end TraceEuclidean
"""


def render_umbrella(parts: list[list[StageFourEntry]]) -> str:
    names = [chunk_name(index) for index in range(len(parts))]
    imports = "import TraceEuclidean.DegreeSevenRolleStageThree\n" + "\n".join(
        f"import TraceEuclidean.DegreeSevenRolleStageFourCertificates.{name}"
        for name in names
    )
    appended = " ++\n    ".join(
        f"degreeSevenStageFourEntries{name}" for name in names
    )
    ranges_appended = " ++\n    ".join(
        f"degreeSevenStageFourExpectedRanges{name}" for name in names
    )
    valid_chain = f"degreeSevenStageFourEntries{names[0]}_valid"
    for name in names[1:]:
        valid_chain = (
            f"⟨{valid_chain}, "
            f"degreeSevenStageFourEntries{name}_valid⟩"
        )
    count_rewrites = ", ".join(
        f"degreeSevenStageFourPrefixCount{name}" for name in names
    )
    entries = [entry for part in parts for entry in part]
    top_triple_lines = ",\n".join(
        f"    ({lean_int(entry.a6)}, {lean_int(entry.a5)}, {lean_int(entry.a4)})"
        for entry in entries
    )
    rejected_triple_lines = ",\n".join(
        f"    ({lean_int(a6)}, {lean_int(a5)}, {lean_int(a4)})"
        for a6, a5, a4 in REJECTED
    )
    parents = compute_stage_three_entries()
    all_stage_three = [
        (parent.a6, parent.a5, a4)
        for parent in parents
        for a4 in stage_three_values(parent)
    ]
    if set(all_stage_three) != {
        (entry.a6, entry.a5, entry.a4) for entry in entries
    } | set(REJECTED):
        raise ArithmeticError(
            "fourth-stage partition does not match third-stage prefixes"
        )
    surviving_by_parent: dict[tuple[int, int], list[int]] = {}
    for entry in entries:
        surviving_by_parent.setdefault((entry.a6, entry.a5), []).append(entry.a4)
    rejected_by_parent: dict[tuple[int, int], list[int]] = {}
    for a6, a5, a4 in REJECTED:
        rejected_by_parent.setdefault((a6, a5), []).append(a4)
    coverage_names: list[str] = []
    coverage_definitions: list[str] = []
    coverage_valid_theorems: list[str] = []
    coverage_valid_names: list[str] = []
    for index, parent in enumerate(parents):
        key = (parent.a6, parent.a5)
        surviving = surviving_by_parent.get(key, [])
        rejected = rejected_by_parent.get(key, [])
        name = f"degreeSevenStageFourCoverage{index:03d}"
        valid_name = f"degreeSevenStageFourCoverage{index:03d}_valid"
        value = (
            "⟨⟨"
            + ", ".join(
                (
                    lean_int(parent.a6),
                    lean_int(parent.a5),
                    lean_interval(parent.first_root),
                    lean_interval(parent.second_root),
                )
            )
            + "⟩, ["
            + ", ".join(lean_int(value) for value in surviving)
            + "], ["
            + ", ".join(lean_int(value) for value in rejected)
            + "]⟩"
        )
        coverage_names.append(name)
        coverage_valid_names.append(valid_name)
        coverage_definitions.append(
            f"def {name} : DegreeSevenStageFourCoverage :=\n  {value}"
        )
        coverage_valid_theorems.append(
            f"""set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This parent interval is checked by ordinary kernel reduction.
theorem {valid_name} :
    {name}.Valid := by
  norm_num [{name},
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
    decide"""
        )
    coverage_source = ",\n".join(f"    {name}" for name in coverage_names)
    coverage_definitions_source = "\n\n".join(coverage_definitions)
    coverage_valid_source = "\n\n".join(coverage_valid_theorems)
    coverage_valid_chain = "True.intro"
    for valid_name in reversed(coverage_valid_names):
        coverage_valid_chain = f"⟨{valid_name}, {coverage_valid_chain}⟩"
    coverage_surviving = [
        (parent.a6, parent.a5, a4)
        for parent in parents
        for a4 in surviving_by_parent.get((parent.a6, parent.a5), [])
    ]
    coverage_rejected = [
        (parent.a6, parent.a5, a4)
        for parent in parents
        for a4 in rejected_by_parent.get((parent.a6, parent.a5), [])
    ]
    if coverage_surviving != [
        (entry.a6, entry.a5, entry.a4) for entry in entries
    ]:
        raise ArithmeticError("coverage order does not match surviving rows")
    if coverage_rejected != REJECTED:
        raise ArithmeticError("coverage order does not match rejected rows")
    entry_names = ", ".join(
        f"degreeSevenStageFourEntries{name}" for name in names
    )
    range_theorems = ", ".join(
        f"degreeSevenStageFourRanges{name}_checked" for name in names
    )
    return f"""{imports}

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

{coverage_definitions_source}

def degreeSevenStageFourCoverages :
    List DegreeSevenStageFourCoverage :=
  [
{coverage_source}
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
  {appended}

/-- The exact coefficient ranges attached to all 1,636 certified cubic rows. -/
def degreeSevenStageFourExpectedRanges :
    List (ℤ × ℤ × ℤ × ℤ × ℤ) :=
  {ranges_appended}

/-- Coefficient triples represented by the certified cubic rows. -/
def degreeSevenStageFourTopTriples : List (ℤ × ℤ × ℤ) :=
  [
{top_triple_lines}
  ]

/-- The five third-stage triples whose cubic has a multiple root. -/
def degreeSevenStageFourRejectedTriples : List (ℤ × ℤ × ℤ) :=
  [
{rejected_triple_lines}
  ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This expands all generated structures and checks their coefficient keys.
theorem degreeSevenStageFourTopTriples_checked :
    degreeSevenStageFourEntries.map (fun entry =>
      (entry.a6, entry.a5, entry.a4)) =
        degreeSevenStageFourTopTriples := by
  simp only [degreeSevenStageFourEntries, List.map_append,
    {entry_names}, degreeSevenStageFourTopTriples]
  rfl

theorem degreeSevenStageFourCoverage_parents_checked :
    degreeSevenStageFourCoverages.map
        DegreeSevenStageFourCoverage.parent =
      degreeSevenStageThreeEntries := by
  rfl

{coverage_valid_source}

/-- The 54 separate kernel certificates cover every parent row. -/
theorem degreeSevenStageFourCoverages_valid :
    degreeSevenStageFourCoverages.Forall
      DegreeSevenStageFourCoverage.Valid := by
  simp only [degreeSevenStageFourCoverages,
    List.forall_cons]
  exact {coverage_valid_chain}

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
  exact {valid_chain}

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
    {range_theorems}]

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
    List.length_append, {count_rewrites}]

end

end TraceEuclidean
"""


def generated_files(entries: list[StageFourEntry]) -> dict[Path, str]:
    parts = chunks(entries)
    files = {
        BASE_OUTPUT: render_base(),
        UMBRELLA_OUTPUT: render_umbrella(parts),
    }
    for index, part in enumerate(parts):
        files[CHUNK_DIR / f"{chunk_name(index)}.lean"] = render_chunk(
            index, part
        )
    return files


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    files = generated_files(compute_entries())

    if args.check:
        stale = [
            path
            for path, content in files.items()
            if not path.exists() or path.read_text(encoding="utf-8") != content
        ]
        if stale:
            raise SystemExit(
                "stale generated files:\n" + "\n".join(map(str, stale))
            )
        print(f"checked {len(files)} generated files")
        return

    CHUNK_DIR.mkdir(parents=True, exist_ok=True)
    expected_chunk_files = {
        path for path in files if path.parent == CHUNK_DIR
    }
    for old in CHUNK_DIR.glob("Chunk*.lean"):
        if old not in expected_chunk_files:
            old.unlink()
    for path, content in files.items():
        path.write_text(content, encoding="utf-8", newline="\n")
    print(f"wrote {len(files)} generated files")


if __name__ == "__main__":
    main()
