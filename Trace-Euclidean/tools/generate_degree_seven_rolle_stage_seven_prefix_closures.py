#!/usr/bin/env python3
"""Generate chunked Stage Six-to-Seven prefix closure modules."""

from __future__ import annotations

import argparse
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUTPUT_DIRECTORY = (
    ROOT
    / "lean"
    / "TraceEuclidean"
    / "DegreeSevenRolleStageSevenPrefix100Closures"
)


def render_chunk(
    index: int,
    chunk_size: int,
    row_base: int,
    dataset_prefix: str,
    stage_six_module_directory: str,
    stage_seven_module_directory: str,
) -> str:
    chunk = f"Chunk{index:03d}"
    dataset = f"{dataset_prefix}{chunk}"
    row_start = row_base + index * chunk_size
    row_end = row_start + chunk_size - 1
    return f"""import {stage_six_module_directory}.{chunk}
import TraceEuclidean.DegreeSevenRolleStageSevenPrefixBridge
import {stage_seven_module_directory}.{chunk}

/-! Stage Seven classification closure for Stage Five rows {row_start} through {row_end}. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSixPrefixes{dataset} :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSixPrefixes
    degreeSevenStageSixPiecewise{dataset}

def degreeSevenStageSevenClassifiedPrefixes{dataset} :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSevenClassifiedPrefixes
    degreeSevenStageSevenScaled{dataset}
    degreeSevenStageSevenMultipleRoot{dataset}
    degreeSevenStageSevenScaledCriticalSign{dataset}

set_option maxHeartbeats 0 in
-- Cleared-denominator integer reduction links Stage Six to Stage Seven.
theorem degreeSevenStageSeven{dataset}_keyLists_eq :
    degreeSevenStageSixPrefixes{dataset} =
      degreeSevenStageSevenClassifications{dataset}.map
        DegreeSevenStageSevenClassification.toPrefix := by
  norm_num (config := {{ maxSteps := 2000000 }})
    [degreeSevenStageSixPrefixes{dataset},
    degreeSevenStageSixPrefixes,
    degreeSevenStageSixPiecewise{dataset},
    DegreeSevenStageSixScaledFamily.toFamily,
    DegreeSevenStageSixFamily.a2Candidates,
    DegreeSevenStageSixScaledFamily.scaledA1Candidates,
    integerIccList, Int.toNat_of_nonpos, List.range_succ,
    degreeSevenStageSevenClassifications{dataset},
    DegreeSevenStageSevenClassification.toPrefix,
    DegreeSevenStageSevenPrefix.ofScaledEntry,
    DegreeSevenStageSevenPrefix.ofMultipleRootWitness,
    DegreeSevenStageSevenPrefix.ofScaledCriticalSignWitness]
  simp (config := {{ dsimp := true, maxSteps := 2000000 }})
    [Int.toNat, List.range_succ] <;> rfl

theorem degreeSevenStageSeven{dataset}_keyFinsets_eq :
    degreeSevenStageSixPrefixes{dataset}.toFinset =
      degreeSevenStageSevenClassifiedPrefixes{dataset}.toFinset := by
  rw [degreeSevenStageSeven{dataset}_keyLists_eq]
  simpa [degreeSevenStageSevenClassifiedPrefixes{dataset},
    degreeSevenStageSevenScaled{dataset},
    degreeSevenStageSevenMultipleRoot{dataset},
    degreeSevenStageSevenScaledCriticalSign{dataset}] using
    (degreeSevenStageSevenClassification_prefixes_toFinset
      degreeSevenStageSevenClassifications{dataset})

end

end TraceEuclidean
"""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--chunk-count", type=int, default=10)
    parser.add_argument("--chunk-size", type=int, default=10)
    parser.add_argument("--row-base", type=int, default=0)
    parser.add_argument("--dataset-prefix", default="Prefix100")
    parser.add_argument(
        "--stage-six-module-directory",
        default=(
            "TraceEuclidean."
            "DegreeSevenRolleStageSixPiecewisePrefix100Chunks"
        ),
    )
    parser.add_argument(
        "--stage-seven-module-directory",
        default=(
            "TraceEuclidean."
            "DegreeSevenRolleStageSevenPrefix100Chunks"
        ),
    )
    parser.add_argument("--output-directory", type=Path, default=OUTPUT_DIRECTORY)
    args = parser.parse_args()
    if args.chunk_count <= 0:
        raise ValueError("--chunk-count must be positive")
    if args.chunk_size <= 0:
        raise ValueError("--chunk-size must be positive")
    if args.row_base < 0:
        raise ValueError("--row-base must be nonnegative")
    if not args.dataset_prefix.isalnum() or not args.dataset_prefix[0].isalpha():
        raise ValueError("--dataset-prefix must be a nonempty alphanumeric Lean suffix")
    output_directory = args.output_directory
    if not output_directory.is_absolute():
        output_directory = ROOT / output_directory
    output_directory.mkdir(parents=True, exist_ok=True)
    for index in range(args.chunk_count):
        output = output_directory / f"Chunk{index:03d}.lean"
        output.write_text(
            render_chunk(
                index,
                args.chunk_size,
                args.row_base,
                args.dataset_prefix,
                args.stage_six_module_directory,
                args.stage_seven_module_directory,
            ),
            encoding="utf-8",
            newline="\n",
        )
        print(f"wrote {output}")


if __name__ == "__main__":
    main()
