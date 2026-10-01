#!/usr/bin/env python3
"""Reject private paths and internal manuscript labels in a release candidate.

Run this from the exported verification tree before publication. It inspects
tracked and non-ignored untracked files, so it also catches files not yet added
to Git. A failure in the working checkout is expected until the public export
has been given stable names and reader-facing instructions.
"""

from __future__ import annotations

import argparse
import re
import subprocess
from collections import Counter
from pathlib import Path


VERSION_LABEL = re.compile(r"v(?:15|16(?:\.\d+)?)(?!\d)", re.IGNORECASE)
WINDOWS_PATH = re.compile(r"(?<![A-Za-z0-9])[A-Za-z]:[\\/]")
LOCAL_HOME = re.compile(r"Users[\\/]+" + ("hz" + "lde"), re.IGNORECASE)
PRIVATE_INPUT_NAME = re.compile(("manu" + "script") + r"[_-]?inputs", re.IGNORECASE)
PRIVATE_SOURCE_META = re.compile(
    r"source[_ -]?sha[-_ ]?256|" + ("active author" + " version") +
    r"|author source[_ -]?sha[-_ ]?256",
    re.IGNORECASE,
)
MAX_REPORTS_PER_KIND = 8


def candidate_files(root: Path) -> list[Path]:
    result = subprocess.run(
        ["git", "-C", str(root), "ls-files", "--cached", "--others", "--exclude-standard", "-z"],
        check=True,
        capture_output=True,
    )
    return [root / item.decode("utf-8") for item in result.stdout.split(b"\0") if item]


def inspect(root: Path) -> tuple[Counter[str], list[str], int]:
    counts: Counter[str] = Counter()
    reports: list[str] = []
    inspected = 0
    for path in candidate_files(root):
        relative = path.relative_to(root).as_posix()
        if not path.is_file():
            continue
        inspected += 1
        if VERSION_LABEL.search(relative):
            counts["internal version in name"] += 1
            if counts["internal version in name"] <= MAX_REPORTS_PER_KIND:
                reports.append(f"internal version in name: {relative}")
        if PRIVATE_INPUT_NAME.search(relative):
            counts["private input name"] += 1
            if counts["private input name"] <= MAX_REPORTS_PER_KIND:
                reports.append(f"private input name: {relative}")
        if WINDOWS_PATH.search(relative) or LOCAL_HOME.search(relative):
            counts["private path/name"] += 1
            if counts["private path/name"] <= MAX_REPORTS_PER_KIND:
                reports.append(f"private path/name: {relative}")
        try:
            raw = path.read_bytes()
            if b"\0" in raw:
                continue
            content = raw.decode("utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        for line_number, line in enumerate(content.splitlines(), start=1):
            for kind, pattern in (
                ("internal version in content", VERSION_LABEL),
                ("absolute local path in content", WINDOWS_PATH),
                ("author home in content", LOCAL_HOME),
                ("private source metadata in content", PRIVATE_SOURCE_META),
            ):
                if pattern.search(line):
                    counts[kind] += 1
                    if counts[kind] <= MAX_REPORTS_PER_KIND:
                        reports.append(f"{kind}: {relative}:{line_number}")
    return counts, reports, inspected


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    root = args.root.resolve()
    counts, reports, inspected = inspect(root)
    if counts:
        print(f"PUBLIC METADATA CHECK: FAIL ({inspected} files inspected)")
        for kind, count in sorted(counts.items()):
            print(f"- {kind}: {count}")
        for report in reports:
            print(f"  {report}")
        return 1
    print(f"PUBLIC METADATA CHECK: PASS ({inspected} files inspected)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
