#!/usr/bin/env python3
"""Reproduce the complete kernel-only degree-seven rows 200--299 block."""

from __future__ import annotations

import argparse
import hashlib
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / "tools"
LEAN_ROOT = ROOT / "lean" / "TraceEuclidean"
ROW_BASE = 200
CHUNK_COUNT = 10
CHUNK_SIZE = 10
MAX_A1_PER_A2 = 3
PRECISION = 24
EXPECTED_SOURCE_COUNT = 178

STAGE_SIX_DIRECTORY = (
    LEAN_ROOT / "DegreeSevenRolleStageSixPiecewiseRows200To299Chunks"
)
STAGE_SEVEN_DIRECTORY = (
    LEAN_ROOT / "DegreeSevenRolleStageSevenRows200To299Chunks"
)
CLOSURE_DIRECTORY = (
    LEAN_ROOT / "DegreeSevenRolleStageSevenRows200To299Closures"
)
REDUCTION_DIRECTORY = (
    LEAN_ROOT / "DegreeSevenRolleStageSevenRows200To299Reduction"
)
REDUCTION_PARTS_DIRECTORY = (
    LEAN_ROOT / "DegreeSevenRolleStageSevenRows200To299ReductionParts"
)
DISCRIMINANT_GROUP_DIRECTORY = (
    LEAN_ROOT / "DegreeSevenRows200To299SurvivorDiscriminantGroups"
)

SINGLETON_OUTPUTS = (
    LEAN_ROOT / "DegreeSevenRolleStageSevenRows200To299Closure.lean",
    LEAN_ROOT / "DegreeSevenRolleStageSevenRows200To299Reduction.lean",
    LEAN_ROOT / "DegreeSevenRows200To299ExceptionalDiscriminant.lean",
    LEAN_ROOT / "DegreeSevenRows200To299ExceptionalMaximalOrder.lean",
    LEAN_ROOT / "DegreeSevenRows200To299SurvivorDiscriminants.lean",
)


def generated_sources() -> list[Path]:
    directories = (
        STAGE_SIX_DIRECTORY,
        STAGE_SEVEN_DIRECTORY,
        CLOSURE_DIRECTORY,
        REDUCTION_DIRECTORY,
        REDUCTION_PARTS_DIRECTORY,
        DISCRIMINANT_GROUP_DIRECTORY,
    )
    paths = list(SINGLETON_OUTPUTS)
    for directory in directories:
        paths.extend(directory.glob("*.lean"))
    return sorted(path for path in paths if path.is_file())


def source_digest(paths: list[Path]) -> str:
    digest = hashlib.sha256()
    for path in paths:
        relative = path.relative_to(ROOT).as_posix().encode("utf-8")
        digest.update(relative)
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def run_generator(script: str, *arguments: str) -> None:
    subprocess.run(
        [sys.executable, str(TOOLS / script), *arguments],
        cwd=ROOT,
        check=True,
    )


def generate_frontier_chunks() -> None:
    for index in range(CHUNK_COUNT):
        row_start = ROW_BASE + index * CHUNK_SIZE
        chunk = f"Chunk{index:03d}"
        dataset = f"Rows200To299{chunk}"
        run_generator(
            "generate_degree_seven_rolle_stage_six_piecewise.py",
            "--row-start", str(row_start),
            "--limit", str(CHUNK_SIZE),
            "--max-a1-per-a2", str(MAX_A1_PER_A2),
            "--precision", str(PRECISION),
            "--progress-every", "0",
            "--dataset-name", dataset,
            "--output", str(STAGE_SIX_DIRECTORY / f"{chunk}.lean"),
            "--write-pilot",
        )
        run_generator(
            "generate_degree_seven_rolle_stage_seven_pilot.py",
            "--row-start", str(row_start),
            "--row-limit", str(CHUNK_SIZE),
            "--max-a1-per-a2", str(MAX_A1_PER_A2),
            "--precision", str(PRECISION),
            "--dataset-name", dataset,
            "--output", str(STAGE_SEVEN_DIRECTORY / f"{chunk}.lean"),
            "--write-pilot",
        )


def generate_derived_certificates() -> None:
    run_generator(
        "generate_degree_seven_rolle_stage_seven_prefix_closures.py",
        "--chunk-count", str(CHUNK_COUNT),
        "--chunk-size", str(CHUNK_SIZE),
        "--row-base", str(ROW_BASE),
        "--dataset-prefix", "Rows200To299",
        "--stage-six-module-directory",
        "TraceEuclidean."
        "DegreeSevenRolleStageSixPiecewiseRows200To299Chunks",
        "--stage-seven-module-directory",
        "TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Chunks",
        "--output-directory", str(CLOSURE_DIRECTORY),
    )
    run_generator(
        "generate_degree_seven_stage_seven_rows100_199_reduction.py",
        "--row-base", str(ROW_BASE),
        "--chunk-count", str(CHUNK_COUNT),
        "--dataset-prefix", "Rows200To299",
        "--stage-seven-module-directory",
        "DegreeSevenRolleStageSevenRows200To299Chunks",
        "--reduction-module-directory",
        "DegreeSevenRolleStageSevenRows200To299Reduction",
        "--reduction-parts-module-directory",
        "DegreeSevenRolleStageSevenRows200To299ReductionParts",
        "--part-size", "25",
    )
    run_generator("generate_degree_seven_rows200_299_aggregates.py")
    run_generator("generate_degree_seven_rows200_299_discriminants.py")
    run_generator("generate_degree_seven_rows200_299_exceptional_maximal_order.py")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check",
        action="store_true",
        help="regenerate and fail unless every generated source is unchanged",
    )
    args = parser.parse_args()

    before = generated_sources()
    before_digest = source_digest(before) if before else None
    generate_frontier_chunks()
    generate_derived_certificates()
    after = generated_sources()
    if len(after) != EXPECTED_SOURCE_COUNT:
        raise ArithmeticError(
            f"expected {EXPECTED_SOURCE_COUNT} generated Lean sources, "
            f"found {len(after)}"
        )
    after_digest = source_digest(after)
    if args.check and (len(before) != len(after) or before_digest != after_digest):
        raise ArithmeticError(
            "rows 200--299 deterministic replay changed the generated sources"
        )
    print(
        "degree-seven rows 200--299 full generation: PASS "
        f"({len(after)} Lean sources, sha256={after_digest})"
    )


if __name__ == "__main__":
    main()
