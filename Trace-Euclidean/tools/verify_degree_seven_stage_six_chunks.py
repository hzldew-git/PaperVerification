#!/usr/bin/env python3
"""Compile generated compact Stage Six chunks with bounded parallelism."""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import os
from pathlib import Path
import subprocess
import time


ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "lean"
SOURCE_DIR = (
    LEAN_ROOT / "TraceEuclidean" /
    "DegreeSevenRolleStageSixStrongCompactCoverages"
)
BUILD_DIR = (
    LEAN_ROOT / ".lake" / "build" / "lib" / "lean" /
    "TraceEuclidean" /
    "DegreeSevenRolleStageSixStrongCompactCoverages"
)


def compile_chunk(path: Path) -> tuple[str, float, str]:
    relative = path.relative_to(LEAN_ROOT)
    output = BUILD_DIR / f"{path.stem}.olean"
    interface = BUILD_DIR / f"{path.stem}.ilean"
    environment = os.environ.copy()
    environment["LEAN_NUM_THREADS"] = "1"
    started = time.perf_counter()
    result = subprocess.run(
        [
            "lake", "--old", "env", "lean", str(relative),
            "-o", str(output.relative_to(LEAN_ROOT)),
            "-i", str(interface.relative_to(LEAN_ROOT)),
        ],
        cwd=LEAN_ROOT,
        env=environment,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    elapsed = time.perf_counter() - started
    if result.returncode != 0:
        raise RuntimeError(
            f"{path.name} failed after {elapsed:.1f}s\n{result.stdout}"
        )
    return path.name, elapsed, result.stdout


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--end", type=int, default=66)
    args = parser.parse_args()
    if args.workers < 1:
        raise ValueError("--workers must be positive")
    paths = [
        SOURCE_DIR / f"Chunk{index:03d}.lean"
        for index in range(args.start, args.end)
    ]
    missing = [str(path) for path in paths if not path.exists()]
    if missing:
        raise FileNotFoundError("missing chunks: " + ", ".join(missing))
    BUILD_DIR.mkdir(parents=True, exist_ok=True)
    failures: list[str] = []
    started = time.perf_counter()
    with ThreadPoolExecutor(max_workers=args.workers) as executor:
        futures = {executor.submit(compile_chunk, path): path for path in paths}
        for completed, future in enumerate(as_completed(futures), start=1):
            path = futures[future]
            try:
                name, elapsed, output = future.result()
                print(
                    f"verified {name} in {elapsed:.1f}s "
                    f"({completed}/{len(paths)})",
                    flush=True,
                )
                if output.strip():
                    print(output.rstrip(), flush=True)
            except Exception as error:
                failures.append(str(error))
                print(f"FAILED {path.name}: {error}", flush=True)
    total = time.perf_counter() - started
    print(f"completed {len(paths)} chunks in {total:.1f}s", flush=True)
    if failures:
        raise SystemExit("\n\n".join(failures))


if __name__ == "__main__":
    main()
