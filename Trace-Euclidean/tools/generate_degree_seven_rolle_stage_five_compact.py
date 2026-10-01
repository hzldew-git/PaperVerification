#!/usr/bin/env python3
"""Generate compact exact certificates for the fifth septic Rolle stage.

The input is the kernel-checked fourth-stage frontier.  Simple totally real
quartics use four width-two dyadic cells with denominator 4096.  Multiple-root
quartics carry an integral common root.  The remaining non-split quartics
carry a critical-point interval on which their sign contradicts the sign
forced by four simple real roots.  Lean rechecks every finite certificate.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from pathlib import Path

from sympy import Poly, Rational, gcd, symbols

from generate_degree_seven_rolle_stage_three import (
    RootInterval,
    interval_eval,
    lean_int,
    lean_interval,
)
from generate_degree_seven_rolle_stage_four import (
    StageFourEntry,
    compute_entries as compute_stage_four_entries,
    fraction_ceil,
    fraction_floor,
)


ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "lean" / "TraceEuclidean"
ENTRY_CHUNK_DIR = (
    LEAN_ROOT / "DegreeSevenRolleStageFiveCertificates"
)
COVERAGE_CHUNK_DIR = (
    LEAN_ROOT / "DegreeSevenRolleStageFiveCoverages"
)
LINK_CHUNK_DIR = LEAN_ROOT / "DegreeSevenRolleStageFiveLinks"
UMBRELLA_OUTPUT = LEAN_ROOT / "DegreeSevenRolleStageFive.lean"
REJECTED_OUTPUT = LEAN_ROOT / "DegreeSevenRolleStageFiveRejected.lean"
# Large chunks amortize Lean's module startup cost.  The generated entry proof
# uses the integer-scaled arithmetic interface, so 1,000 rows remain practical.
ENTRY_CHUNK_SIZE = 1000
COVERAGE_CHUNK_SIZE = 25
DYADIC_DENOMINATOR = 4096
ROOT_INTERVAL_EPSILON = Rational(1, 2**13)
EXPECTED_A2_PREFIX_COUNT = 943005
X = symbols("x")


@dataclass(frozen=True)
class StageFiveEntry:
    a6: int
    a5: int
    a4: int
    a3: int
    cells: tuple[int, int, int, int]
    a2_lower: int
    a2_upper: int


@dataclass(frozen=True)
class MultipleRootRejection:
    parent: StageFourEntry
    a3: int
    common_root: int


@dataclass(frozen=True)
class CriticalSignRejection:
    parent: StageFourEntry
    witness_parent: StageFourEntry
    a3: int
    point: int


@dataclass(frozen=True)
class Coverage:
    parent: StageFourEntry
    surviving: tuple[int, ...]
    multiple_roots: tuple[tuple[int, int], ...]
    critical_signs: tuple[CriticalSignRejection, ...]


def as_fraction(value: Rational) -> Fraction:
    return Fraction(int(value.p), int(value.q))


def quartic(parent: StageFourEntry, a3: int) -> Poly:
    return Poly(
        35 * X**4
        + 20 * parent.a6 * X**3
        + 10 * parent.a5 * X**2
        + 4 * parent.a4 * X
        + a3,
        X,
        domain="QQ",
    )


def quartic_coefficients(parent: StageFourEntry, a3: int) -> list[int]:
    return [
        a3,
        4 * parent.a4,
        10 * parent.a5,
        20 * parent.a6,
        35,
    ]


def exact_value(polynomial: Poly, value: Fraction) -> Fraction:
    evaluated = polynomial.eval(Rational(value.numerator, value.denominator))
    return as_fraction(evaluated)


def dyadic_cells(
    polynomial: Poly, lower: Fraction, upper: Fraction
) -> tuple[int, ...]:
    midpoint = (lower + upper) / 2
    center = (midpoint.numerator * DYADIC_DENOMINATOR) // midpoint.denominator
    cells: list[int] = []
    for cell in range(center - 4, center + 5):
        left = Fraction(cell, DYADIC_DENOMINATOR)
        right = Fraction(cell + 2, DYADIC_DENOMINATOR)
        if exact_value(polynomial, left) * exact_value(polynomial, right) < 0:
            cells.append(cell)
    if not cells:
        raise ArithmeticError(
            f"no width-two dyadic cell near [{lower}, {upper}] for {polynomial}"
        )
    return tuple(cells)


def isolate_quartic_dyadic(
    polynomial: Poly,
) -> tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...], tuple[int, ...]] | None:
    raw_intervals = polynomial.intervals(eps=ROOT_INTERVAL_EPSILON)
    if len(raw_intervals) != 4 or any(
        multiplicity != 1 for _, multiplicity in raw_intervals
    ):
        return None
    cells: list[tuple[int, ...]] = []
    for (lower, upper), _ in raw_intervals:
        cells.append(
            dyadic_cells(
                polynomial,
                as_fraction(lower),
                as_fraction(upper),
            )
        )
    return cells[0], cells[1], cells[2], cells[3]


def best_cells_and_bounds(
    parent: StageFourEntry,
    a3: int,
    options: tuple[
        tuple[int, ...], tuple[int, ...], tuple[int, ...], tuple[int, ...]
    ],
) -> tuple[tuple[int, int, int, int], int, int]:
    candidates: list[tuple[int, int, tuple[int, int, int, int], int, int]] = []
    for raw_cells in product(*options):
        cells = (raw_cells[0], raw_cells[1], raw_cells[2], raw_cells[3])
        if not all(
            left + 2 < right for left, right in zip(cells, cells[1:])
        ):
            continue
        lower, upper = a2_bounds(parent, a3, cells)
        count = max(0, upper - lower + 1)
        candidates.append((count, upper - lower, cells, lower, upper))
    if not candidates:
        raise ArithmeticError(f"no separated dyadic cell family for {parent}, {a3}")
    _, _, cells, lower, upper = min(candidates)
    return cells, lower, upper


def common_integral_root(polynomial: Poly) -> int:
    common = gcd(polynomial, polynomial.diff())
    if common.degree() <= 0:
        raise ArithmeticError(f"polynomial has no multiple root: {polynomial}")
    roots = common.all_roots()
    integral = [int(root) for root in roots if bool(root.is_Integer)]
    if not integral:
        raise ArithmeticError(
            f"multiple-root polynomial has no integral common root: {polynomial}"
        )
    return integral[0]


def refined_parent(
    parent: StageFourEntry, precision: int
) -> StageFourEntry:
    polynomial = Poly(
        35 * X**3
        + 15 * parent.a6 * X**2
        + 5 * parent.a5 * X
        + parent.a4,
        X,
        domain="QQ",
    )
    raw_intervals = polynomial.intervals(eps=Rational(1, 2**precision))
    if len(raw_intervals) != 3 or any(
        multiplicity != 1 for _, multiplicity in raw_intervals
    ):
        raise ArithmeticError(f"parent cubic is not simple real split: {parent}")
    intervals: list[RootInterval] = []
    for (lower, upper), _ in raw_intervals:
        lo = as_fraction(lower)
        hi = as_fraction(upper)
        if lo == hi:
            delta = Fraction(1, 2**precision)
            lo -= delta
            hi += delta
        intervals.append(RootInterval(lo, hi))
    if not all(
        left.upper < right.lower
        for left, right in zip(intervals, intervals[1:])
    ):
        raise ArithmeticError("refined cubic intervals are not separated")
    return StageFourEntry(
        parent.a6,
        parent.a5,
        parent.a4,
        (intervals[0], intervals[1], intervals[2]),
        parent.a3_lower,
        parent.a3_upper,
    )


def critical_sign_point(
    parent: StageFourEntry, a3: int
) -> tuple[StageFourEntry, int]:
    coefficients = quartic_coefficients(parent, a3)
    last_ranges: list[tuple[Fraction, Fraction]] = []
    for precision in (16, 24, 32, 40):
        refined = refined_parent(parent, precision)
        ranges = [
            interval_eval(coefficients, interval) for interval in refined.roots
        ]
        contradictory = [
            index
            for index, value_range in enumerate(ranges)
            if (index in (0, 2) and 0 < value_range[0])
            or (index == 1 and value_range[1] < 0)
        ]
        if contradictory:
            return refined, contradictory[0]
        last_ranges = ranges
    raise ArithmeticError(
        "no critical-sign contradiction for "
        f"{parent.a6, parent.a5, parent.a4, a3}: {last_ranges}"
    )


def dyadic_interval(cell: int) -> RootInterval:
    return RootInterval(
        Fraction(cell, DYADIC_DENOMINATOR),
        Fraction(cell + 2, DYADIC_DENOMINATOR),
    )


def a2_bounds(
    parent: StageFourEntry,
    a3: int,
    cells: tuple[int, int, int, int],
) -> tuple[int, int]:
    base = [
        0,
        3 * a3,
        6 * parent.a4,
        10 * parent.a5,
        15 * parent.a6,
        21,
    ]
    roots = tuple(dyadic_interval(cell) for cell in cells)
    left = Fraction(-parent.a6 - 38, 7)
    right = Fraction(-parent.a6 + 38, 7)
    samples = (
        interval_eval(base, RootInterval(left, left)),
        interval_eval(base, roots[0]),
        interval_eval(base, roots[1]),
        interval_eval(base, roots[2]),
        interval_eval(base, roots[3]),
        interval_eval(base, RootInterval(right, right)),
    )
    lower = max(fraction_ceil(-samples[index][1]) for index in (1, 3, 5))
    upper = min(fraction_floor(-samples[index][0]) for index in (0, 2, 4))
    return lower, upper


def parent_values(parent: StageFourEntry) -> range:
    return range(parent.a3_lower, parent.a3_upper + 1)


def compute_frontier() -> tuple[
    list[StageFiveEntry],
    list[MultipleRootRejection],
    list[CriticalSignRejection],
    list[Coverage],
]:
    entries: list[StageFiveEntry] = []
    multiple_roots: list[MultipleRootRejection] = []
    critical_signs: list[CriticalSignRejection] = []
    coverages: list[Coverage] = []

    for parent in compute_stage_four_entries():
        parent_surviving: list[int] = []
        parent_multiple: list[tuple[int, int]] = []
        parent_critical: list[CriticalSignRejection] = []
        for a3 in parent_values(parent):
            polynomial = quartic(parent, a3)
            cell_options = isolate_quartic_dyadic(polynomial)
            if cell_options is not None:
                cells, lower, upper = best_cells_and_bounds(
                    parent, a3, cell_options
                )
                entries.append(
                    StageFiveEntry(
                        parent.a6,
                        parent.a5,
                        parent.a4,
                        a3,
                        cells,
                        lower,
                        upper,
                    )
                )
                parent_surviving.append(a3)
                continue

            common = gcd(polynomial, polynomial.diff())
            if common.degree() > 0:
                root = common_integral_root(polynomial)
                multiple_roots.append(MultipleRootRejection(parent, a3, root))
                parent_multiple.append((a3, root))
            else:
                witness_parent, point = critical_sign_point(parent, a3)
                rejection = CriticalSignRejection(
                    parent, witness_parent, a3, point
                )
                critical_signs.append(rejection)
                parent_critical.append(rejection)

        coverages.append(
            Coverage(
                parent,
                tuple(parent_surviving),
                tuple(parent_multiple),
                tuple(parent_critical),
            )
        )

    if len(entries) != 48594:
        raise ArithmeticError(
            f"expected 48594 simple quartics, found {len(entries)}"
        )
    if len(multiple_roots) != 100:
        raise ArithmeticError(
            f"expected 100 multiple-root quartics, found {len(multiple_roots)}"
        )
    if len(critical_signs) != 16:
        raise ArithmeticError(
            f"expected 16 critical-sign rejections, found {len(critical_signs)}"
        )
    if len(coverages) != 1636:
        raise ArithmeticError(
            f"expected 1636 parent coverages, found {len(coverages)}"
        )
    total = sum(
        max(0, entry.a2_upper - entry.a2_lower + 1)
        for entry in entries
    )
    if total != EXPECTED_A2_PREFIX_COUNT:
        raise ArithmeticError(
            f"expected {EXPECTED_A2_PREFIX_COUNT} a2 prefixes, found {total}"
        )
    if len(entries) + len(multiple_roots) + len(critical_signs) != 48710:
        raise ArithmeticError("fifth-stage partition does not have 48710 rows")
    return entries, multiple_roots, critical_signs, coverages


def split_chunks[T](values: list[T], size: int) -> list[list[T]]:
    return [values[start : start + size] for start in range(0, len(values), size)]


def entry_chunk_name(index: int) -> str:
    return f"Chunk{index:03d}"


def coverage_chunk_name(index: int) -> str:
    return f"Chunk{index:03d}"


def link_chunk_name(index: int) -> str:
    return f"Chunk{index:03d}"


def render_parent(parent: StageFourEntry) -> str:
    return "⟨" + ", ".join(
        (
            lean_int(parent.a6),
            lean_int(parent.a5),
            lean_int(parent.a4),
            *(lean_interval(root) for root in parent.roots),
        )
    ) + "⟩"


def render_point(point: int) -> str:
    names = (".first", ".second", ".third")
    return names[point]


def render_entry_chunk(index: int, entries: list[StageFiveEntry]) -> str:
    name = entry_chunk_name(index)
    entry_lines = ",\n".join(
        "    ⟨"
        + ", ".join(
            (
                lean_int(entry.a6),
                lean_int(entry.a5),
                lean_int(entry.a4),
                lean_int(entry.a3),
                *(lean_int(cell) for cell in entry.cells),
            )
        )
        + "⟩"
        for entry in entries
    )
    return f"""import TraceEuclidean.DegreeSevenRolleStageFiveCompact

/-! Generated compact quartic root certificates, {name}. -/

namespace TraceEuclidean

set_option linter.style.longLine false
-- The generated list contains up to one thousand certificate records.
set_option maxRecDepth 100000

def degreeSevenStageFiveEntries{name} :
    List DegreeSevenStageFiveDyadicEntry :=
  [
{entry_lines}
  ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Integer-scaled dyadic sign checks are reduced by the Lean kernel.
theorem degreeSevenStageFiveEntries{name}_valid :
    degreeSevenStageFiveEntries{name}.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have harithmetic :
      degreeSevenStageFiveEntries{name}.Forall
        DegreeSevenStageFiveDyadicEntry.ArithmeticValid := by
    norm_num [degreeSevenStageFiveEntries{name},
      DegreeSevenStageFiveDyadicEntry.ArithmeticValid,
      DegreeSevenStageFiveDyadicEntry.dyadicNumerator]
  exact harithmetic.imp fun entry hentry =>
    DegreeSevenStageFiveDyadicEntry.valid_of_arithmeticValid
      entry hentry

end TraceEuclidean
"""


def render_coverage_chunk(index: int, coverages: list[Coverage]) -> str:
    name = coverage_chunk_name(index)
    lines: list[str] = []
    for coverage in coverages:
        surviving = "[" + ", ".join(
            lean_int(value) for value in coverage.surviving
        ) + "]"
        multiple = "[" + ", ".join(
            f"({lean_int(a3)}, {lean_int(root)})"
            for a3, root in coverage.multiple_roots
        ) + "]"
        critical = "[" + ", ".join(
            render_critical_witness(entry)
            for entry in coverage.critical_signs
        ) + "]"
        lines.append(
            "    ⟨"
            + ", ".join(
                (
                    render_parent(coverage.parent),
                    lean_int(coverage.parent.a3_lower),
                    lean_int(coverage.parent.a3_upper),
                    surviving,
                    multiple,
                    critical,
                )
            )
            + "⟩"
        )
    coverage_lines = ",\n".join(lines)
    return f"""import TraceEuclidean.DegreeSevenRolleStageFiveCompact

/-! Generated fifth-stage coverage records, {name}. -/

namespace TraceEuclidean

set_option linter.style.longLine false

def degreeSevenStageFiveCoverages{name} :
    List DegreeSevenStageFiveCoverage :=
  [
{coverage_lines}
  ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Pure kernel reduction checks each finite parent partition in this chunk.
theorem degreeSevenStageFiveCoverages{name}_valid :
    degreeSevenStageFiveCoverages{name}.Forall
      DegreeSevenStageFiveCoverage.Valid := by
  decide

end TraceEuclidean
"""


def render_multiple_witness(entry: MultipleRootRejection) -> str:
    return "⟨" + ", ".join(
        (
            lean_int(entry.parent.a6),
            lean_int(entry.parent.a5),
            lean_int(entry.parent.a4),
            lean_int(entry.a3),
            lean_int(entry.common_root),
        )
    ) + "⟩"


def render_critical_witness(entry: CriticalSignRejection) -> str:
    return "⟨" + ", ".join(
        (
            render_parent(entry.witness_parent),
            lean_int(entry.a3),
            render_point(entry.point),
        )
    ) + "⟩"


def nested_forall_chain(theorems: list[str]) -> str:
    if not theorems:
        return "by simp"
    chain = theorems[0]
    for theorem in theorems[1:]:
        chain = f"⟨{chain}, {theorem}⟩"
    return chain


def entry_slice_pieces(
    start: int,
    count: int,
    entry_parts: list[list[StageFiveEntry]],
) -> list[tuple[int, int, int]]:
    """Return `(chunk, local offset, length)` pieces for one global slice."""
    pieces: list[tuple[int, int, int]] = []
    position = start
    remaining = count
    while remaining:
        chunk = position // ENTRY_CHUNK_SIZE
        local = position % ENTRY_CHUNK_SIZE
        if chunk >= len(entry_parts):
            raise ArithmeticError("aligned entry slice exceeds generated data")
        length = min(remaining, len(entry_parts[chunk]) - local)
        if length <= 0:
            raise ArithmeticError("empty aligned entry slice piece")
        pieces.append((chunk, local, length))
        position += length
        remaining -= length
    return pieces


def render_link_chunk(
    index: int,
    coverages: list[Coverage],
    entry_start: int,
    entry_parts: list[list[StageFiveEntry]],
) -> str:
    """Link one coverage chunk to a small slice of the validated entry data."""
    name = link_chunk_name(index)
    coverage_name = coverage_chunk_name(index)
    entry_count = sum(len(coverage.surviving) for coverage in coverages)
    pieces = entry_slice_pieces(entry_start, entry_count, entry_parts)
    entry_names = [entry_chunk_name(chunk) for chunk, _, _ in pieces]
    imports = [
        "import TraceEuclidean.DegreeSevenRolleStageFiveCoverages."
        + coverage_name
    ]
    imports.extend(
        "import TraceEuclidean.DegreeSevenRolleStageFiveCertificates."
        + entry_name
        for entry_name in dict.fromkeys(entry_names)
    )

    piece_terms: list[str] = []
    piece_valid_names: list[str] = []
    piece_proofs: list[str] = []
    for piece_index, (chunk, local, length) in enumerate(pieces):
        entry_name = entry_chunk_name(chunk)
        source = f"degreeSevenStageFiveEntries{entry_name}"
        source_valid = f"degreeSevenStageFiveEntries{entry_name}_valid"
        if local == 0 and length == len(entry_parts[chunk]):
            term = source
            proof = source_valid
        else:
            term = f"({source}.drop {local}).take {length}"
            proof_name = f"hpiece{piece_index}"
            proof = proof_name
            piece_proofs.append(
                f"  have {proof_name} :\n"
                f"      ({term}).Forall\n"
                "        DegreeSevenStageFiveDyadicEntry.Valid := by\n"
                "    rw [List.forall_iff_forall_mem]\n"
                "    intro entry hentry\n"
                f"    exact (List.forall_iff_forall_mem.mp {source_valid})\n"
                "      entry (List.mem_of_mem_drop\n"
                "        (List.mem_of_mem_take hentry))"
            )
        piece_terms.append(term)
        piece_valid_names.append(proof)

    appended_entries = " ++\n    ".join(piece_terms)
    validity_setup = "\n".join(piece_proofs)
    if validity_setup:
        validity_setup += "\n"
    validity_chain = nested_forall_chain(piece_valid_names)
    return f"""{chr(10).join(imports)}

/-! Generated local link between coverage and compact entry data, {name}. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntries{name} :
    List DegreeSevenStageFiveDyadicEntry :=
  {appended_entries}

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntries{name}_valid :
    degreeSevenStageFiveAlignedEntries{name}.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
{validity_setup}  simp only [degreeSevenStageFiveAlignedEntries{name},
    List.forall_append]
  exact {validity_chain}

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntries{name}_top_checked :
    degreeSevenStageFiveAlignedEntries{name}.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoverages{coverage_name}.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntries{name}_length :
    degreeSevenStageFiveAlignedEntries{name}.length = {entry_count} := by
  rfl

end TraceEuclidean
"""


def render_rejected(
    multiple_roots: list[MultipleRootRejection],
    critical_signs: list[CriticalSignRejection],
) -> str:
    multiple_source = ",\n".join(
        "    " + render_multiple_witness(entry) for entry in multiple_roots
    )
    critical_source = ",\n".join(
        "    " + render_critical_witness(entry) for entry in critical_signs
    )
    return f"""import TraceEuclidean.DegreeSevenRolleStageFiveCompact

/-! Generated exceptional-row certificates for the fifth septic Rolle stage. -/

namespace TraceEuclidean

noncomputable section

def degreeSevenStageFiveMultipleRootWitnesses :
    List DegreeSevenStageFiveMultipleRootWitness :=
  [
{multiple_source}
  ]

def degreeSevenStageFiveCriticalSignWitnesses :
    List DegreeSevenStageFiveCriticalSignWitness :=
  [
{critical_source}
  ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem degreeSevenStageFiveMultipleRootWitnesses_valid :
    degreeSevenStageFiveMultipleRootWitnesses.Forall
      DegreeSevenStageFiveMultipleRootWitness.Valid := by
  norm_num [degreeSevenStageFiveMultipleRootWitnesses,
    DegreeSevenStageFiveMultipleRootWitness.Valid,
    DegreeSevenStageFiveMultipleRootWitness.coefficients,
    DegreeSevenStageFiveMultipleRootWitness.derivativeCoefficients,
    integerPolynomialRationalEval, DensePolynomial.eval]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem degreeSevenStageFiveCriticalSignWitnesses_valid :
    degreeSevenStageFiveCriticalSignWitnesses.Forall
      DegreeSevenStageFiveCriticalSignWitness.Valid := by
  norm_num [degreeSevenStageFiveCriticalSignWitnesses,
    DegreeSevenStageFiveCriticalSignWitness.Valid,
    DegreeSevenStageFiveCriticalSignWitness.criticalValueRange,
    DegreeSevenStageFiveCriticalSignWitness.coefficients,
    DegreeSevenStageFiveCriticalPoint.interval,
    DegreeSevenStageFourEntry.Valid,
    DegreeSevenStageFourEntry.derivativeCoefficients,
    DegreeSevenStageFourEntry.rootIntervals,
    GeneralRationalRootIntervalCertificate.Valid,
    integerPolynomialRationalEval,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4,
    DensePolynomial.eval, min_def, max_def]

end

end TraceEuclidean
"""


def render_umbrella(
    entry_parts: list[list[StageFiveEntry]],
    coverage_parts: list[list[Coverage]],
) -> str:
    coverage_names = [
        coverage_chunk_name(index) for index in range(len(coverage_parts))
    ]
    link_names = [link_chunk_name(index) for index in range(len(coverage_parts))]
    imports = [
        "import TraceEuclidean.DegreeSevenRolleStageFourCompleteness",
        "import TraceEuclidean.DegreeSevenRolleStageFiveRejected",
    ]
    imports.extend(
        "import TraceEuclidean.DegreeSevenRolleStageFiveLinks."
        + name
        for name in link_names
    )
    appended_entries = " ++\n    ".join(
        f"degreeSevenStageFiveAlignedEntries{name}" for name in link_names
    )
    appended_coverages = " ++\n    ".join(
        f"degreeSevenStageFiveCoverages{name}" for name in coverage_names
    )
    entry_valid = nested_forall_chain(
        [
            f"degreeSevenStageFiveAlignedEntries{name}_valid"
            for name in link_names
        ]
    )
    coverage_valid = nested_forall_chain(
        [
            f"degreeSevenStageFiveCoverages{name}_valid"
            for name in coverage_names
        ]
    )
    top_checked = ", ".join(
        f"degreeSevenStageFiveAlignedEntries{name}_top_checked"
        for name in link_names
    )
    aligned_lengths = ", ".join(
        f"degreeSevenStageFiveAlignedEntries{name}_length"
        for name in link_names
    )
    return f"""{chr(10).join(imports)}

/-! Complete compact fifth-stage frontier for the septic Rolle search. -/

namespace TraceEuclidean

noncomputable section

def degreeSevenStageFiveEntries :
    List DegreeSevenStageFiveDyadicEntry :=
  {appended_entries}

def degreeSevenStageFiveCoverages :
    List DegreeSevenStageFiveCoverage :=
  {appended_coverages}

def degreeSevenStageFiveTopQuadruples :
    List (ℤ × ℤ × ℤ × ℤ) :=
  degreeSevenStageFiveCoverages.flatMap
    DegreeSevenStageFiveCoverage.topQuadruples

def degreeSevenStageFiveMultipleRootQuadruples :
    List (ℤ × ℤ × ℤ × ℤ) :=
  degreeSevenStageFiveCoverages.flatMap
    DegreeSevenStageFiveCoverage.multipleRootQuadruples

def degreeSevenStageFiveCriticalSignQuadruples :
    List (ℤ × ℤ × ℤ × ℤ) :=
  degreeSevenStageFiveCoverages.flatMap
    DegreeSevenStageFiveCoverage.criticalSignQuadruples

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveCoverage_parents_checked :
    degreeSevenStageFiveCoverages.map
        DegreeSevenStageFiveCoverage.parent =
      degreeSevenStageFourEntries := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveCoverageRanges_checked :
    degreeSevenStageFiveCoverages.map
        DegreeSevenStageFiveCoverage.rangeRecord =
      degreeSevenStageFourExpectedRanges := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveCoverages_valid :
    degreeSevenStageFiveCoverages.Forall
      DegreeSevenStageFiveCoverage.Valid := by
  simp only [degreeSevenStageFiveCoverages, List.forall_append]
  exact {coverage_valid}

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveEntries_valid :
    degreeSevenStageFiveEntries.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  simp only [degreeSevenStageFiveEntries, List.forall_append]
  exact {entry_valid}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem degreeSevenStageFiveTopQuadruples_checked :
    degreeSevenStageFiveEntries.map (fun entry =>
      (entry.a6, entry.a5, entry.a4, entry.a3)) =
        degreeSevenStageFiveTopQuadruples := by
  simp only [degreeSevenStageFiveEntries,
    degreeSevenStageFiveCoverages,
    degreeSevenStageFiveTopQuadruples,
    List.map_append, List.flatMap_append, {top_checked}]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem degreeSevenStageFiveMultipleRootWitnesses_checked :
    degreeSevenStageFiveCoverages.flatMap
        DegreeSevenStageFiveCoverage.multipleRootWitnesses =
      degreeSevenStageFiveMultipleRootWitnesses := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem degreeSevenStageFiveCriticalSignWitnesses_checked :
    degreeSevenStageFiveCoverages.flatMap
        DegreeSevenStageFiveCoverage.criticalSignWitnesses =
      degreeSevenStageFiveCriticalSignWitnesses := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem degreeSevenStageFive_entry_count :
    degreeSevenStageFiveEntries.length = 48594 := by
  simp only [degreeSevenStageFiveEntries, List.length_append,
    {aligned_lengths}]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem degreeSevenStageFive_multipleRoot_count :
    degreeSevenStageFiveMultipleRootWitnesses.length = 100 := by
  norm_num [degreeSevenStageFiveMultipleRootWitnesses]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem degreeSevenStageFive_criticalSign_count :
    degreeSevenStageFiveCriticalSignWitnesses.length = 16 := by
  norm_num [degreeSevenStageFiveCriticalSignWitnesses]

end

end TraceEuclidean
"""


def generated_files(
    entries: list[StageFiveEntry],
    multiple_roots: list[MultipleRootRejection],
    critical_signs: list[CriticalSignRejection],
    coverages: list[Coverage],
) -> dict[Path, str]:
    entry_parts = split_chunks(entries, ENTRY_CHUNK_SIZE)
    coverage_parts = split_chunks(coverages, COVERAGE_CHUNK_SIZE)
    files: dict[Path, str] = {
        UMBRELLA_OUTPUT: render_umbrella(entry_parts, coverage_parts),
        REJECTED_OUTPUT: render_rejected(multiple_roots, critical_signs),
    }
    for index, part in enumerate(entry_parts):
        files[
            ENTRY_CHUNK_DIR / f"{entry_chunk_name(index)}.lean"
        ] = render_entry_chunk(index, part)
    for index, part in enumerate(coverage_parts):
        files[
            COVERAGE_CHUNK_DIR / f"{coverage_chunk_name(index)}.lean"
        ] = render_coverage_chunk(index, part)
    entry_start = 0
    for index, part in enumerate(coverage_parts):
        files[
            LINK_CHUNK_DIR / f"{link_chunk_name(index)}.lean"
        ] = render_link_chunk(index, part, entry_start, entry_parts)
        entry_start += sum(len(coverage.surviving) for coverage in part)
    if entry_start != len(entries):
        raise ArithmeticError("aligned entry links do not cover the frontier")
    return files


def write_selected(
    files: dict[Path, str],
    only_entry_chunk: int | None,
    only_coverage_chunk: int | None,
) -> int:
    selected = files
    if only_entry_chunk is not None:
        target = ENTRY_CHUNK_DIR / f"{entry_chunk_name(only_entry_chunk)}.lean"
        if target not in files:
            raise SystemExit(f"entry chunk does not exist: {only_entry_chunk}")
        selected = {target: files[target]}
    elif only_coverage_chunk is not None:
        target = (
            COVERAGE_CHUNK_DIR
            / f"{coverage_chunk_name(only_coverage_chunk)}.lean"
        )
        if target not in files:
            raise SystemExit(f"coverage chunk does not exist: {only_coverage_chunk}")
        selected = {target: files[target]}

    if only_entry_chunk is None and only_coverage_chunk is None:
        expected_entry_files = {
            path for path in files if path.parent == ENTRY_CHUNK_DIR
        }
        expected_coverage_files = {
            path for path in files if path.parent == COVERAGE_CHUNK_DIR
        }
        expected_link_files = {
            path for path in files if path.parent == LINK_CHUNK_DIR
        }
        for old in ENTRY_CHUNK_DIR.glob("Chunk*.lean"):
            if old not in expected_entry_files:
                old.unlink()
        for old in COVERAGE_CHUNK_DIR.glob("Chunk*.lean"):
            if old not in expected_coverage_files:
                old.unlink()
        for old in LINK_CHUNK_DIR.glob("Chunk*.lean"):
            if old not in expected_link_files:
                old.unlink()

    written = 0
    for path, content in selected.items():
        if path.exists() and path.read_text(encoding="utf-8") == content:
            continue
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8", newline="\n")
        written += 1
    return written


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--summary", action="store_true")
    parser.add_argument("--only-entry-chunk", type=int)
    parser.add_argument("--only-coverage-chunk", type=int)
    args = parser.parse_args()
    if (
        args.only_entry_chunk is not None
        and args.only_coverage_chunk is not None
    ):
        raise SystemExit("choose at most one --only-*-chunk option")

    entries, multiple_roots, critical_signs, coverages = compute_frontier()
    total = sum(
        max(0, entry.a2_upper - entry.a2_lower + 1)
        for entry in entries
    )
    print(
        "frontier:",
        len(entries),
        "simple,",
        len(multiple_roots),
        "multiple-root,",
        len(critical_signs),
        "critical-sign,",
        total,
        "a2 prefixes",
    )
    if args.summary:
        return

    files = generated_files(entries, multiple_roots, critical_signs, coverages)
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

    count = write_selected(
        files, args.only_entry_chunk, args.only_coverage_chunk
    )
    print(f"wrote {count} generated files")


if __name__ == "__main__":
    main()
