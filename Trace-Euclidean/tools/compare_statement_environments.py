"""Compare theorem-like environments in two local TeX manuscript versions.

The manuscript files are read in place and are never copied into this package.
This checks statement text after whitespace and label normalization; a human
must review changed prose, proofs, and references separately.
"""

from __future__ import annotations

import argparse
import hashlib
import re
from pathlib import Path


ENVIRONMENTS = ("thm", "cor", "prop", "lem", "defn", "aspn", "conj", "re", "ex")
MAIN_ENVIRONMENTS = frozenset(ENVIRONMENTS) - {"re", "ex"}
ENV_PATTERN = re.compile(
    r"\\begin\{(" + "|".join(ENVIRONMENTS) + r")\}(.*?)\\end\{\1\}", re.S
)
LABEL_PATTERN = re.compile(r"\\label\{([^}]+)\}")


def extract(path: Path) -> tuple[str, dict[str, tuple[str, str, int]]]:
    data = path.read_bytes()
    source = data.decode("utf-8")
    statements: dict[str, tuple[str, str, int]] = {}
    for match in ENV_PATTERN.finditer(source):
        label_match = LABEL_PATTERN.search(match.group(2))
        if label_match is None:
            raise ValueError(f"Unlabelled {match.group(1)} at {path}:{source.count(chr(10), 0, match.start()) + 1}")
        label = label_match.group(1)
        if label in statements:
            raise ValueError(f"Duplicate label {label} in {path}")
        body = LABEL_PATTERN.sub("", match.group(2))
        normalized = " ".join(body.split())
        statements[label] = (
            match.group(1),
            normalized,
            source.count("\n", 0, match.start()) + 1,
        )
    return hashlib.sha256(data).hexdigest(), statements


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("earlier", type=Path)
    parser.add_argument("later", type=Path)
    args = parser.parse_args()
    earlier_hash, earlier = extract(args.earlier)
    later_hash, later = extract(args.later)
    if not earlier or not later:
        raise ValueError("Expected labelled theorem-like environments in both sources")
    print(f"earlier SHA-256 {earlier_hash}; environments {len(earlier)}")
    print(f"later   SHA-256 {later_hash}; environments {len(later)}")
    changes: list[tuple[str, str, str]] = []
    for label in sorted(earlier.keys() | later.keys()):
        before = earlier.get(label)
        after = later.get(label)
        if before is None:
            changes.append((label, after[0], f"added at later line {after[2]}"))
        elif after is None:
            changes.append((label, before[0], f"removed from earlier line {before[2]}"))
        elif before[:2] != after[:2]:
            changes.append((label, before[0], f"changed at lines {before[2]} -> {after[2]}"))
    if changes:
        for label, kind, description in changes:
            print(f"{kind} {label}: {description}")
    else:
        print("All theorem-like environments match after normalization.")
    main_changes = [
        label for label, _, _ in changes
        if (label in earlier and earlier[label][0] in MAIN_ENVIRONMENTS)
        or (label in later and later[label][0] in MAIN_ENVIRONMENTS)
    ]
    main_count = sum(kind in MAIN_ENVIRONMENTS for kind, _, _ in earlier.values())
    print(f"Main mathematical statements: {main_count}; changed: {len(main_changes)}")
    return 1 if main_changes else 0


if __name__ == "__main__":
    raise SystemExit(main())
