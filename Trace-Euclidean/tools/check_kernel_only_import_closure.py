#!/usr/bin/env python3
"""Reject native evaluation in the formal main-theorem import closure."""

from __future__ import annotations

import argparse
import re
from pathlib import Path


IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.]+)\s*$")
FORBIDDEN = ("native_decide", "Lean.ofReduceBool")
LOCAL_PREFIXES = (
    "TraceEuclidean",
    "LeanCert",
    "DedekindZeta",
    "IdealArithmetic",
)
DEFAULT_ROOTS = (
    "TraceEuclideanKernel",
)


def module_path(lean_root: Path, module: str) -> Path:
    return lean_root.joinpath(*module.split(".")).with_suffix(".lean")


def project_imports(path: Path) -> list[str]:
    imports: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = IMPORT_RE.match(line)
        if match:
            module = match.group(1)
            if module == "TraceEuclideanKernel" or any(
                module == prefix or module.startswith(prefix + ".")
                for prefix in LOCAL_PREFIXES
            ):
                imports.append(module)
    return imports


def without_comments(source: str) -> str:
    """Remove nested Lean block comments and line comments."""
    result: list[str] = []
    index = 0
    depth = 0
    in_string = False
    while index < len(source):
        pair = source[index : index + 2]
        char = source[index]
        if depth:
            if pair == "/-":
                depth += 1
                index += 2
            elif pair == "-/":
                depth -= 1
                index += 2
            else:
                index += 1
            continue
        if in_string:
            result.append(char)
            if char == "\\" and index + 1 < len(source):
                result.append(source[index + 1])
                index += 2
                continue
            if char == '"':
                in_string = False
            index += 1
            continue
        if pair == "/-":
            depth = 1
            index += 2
        elif pair == "--":
            newline = source.find("\n", index + 2)
            index = len(source) if newline < 0 else newline
        else:
            result.append(char)
            if char == '"':
                in_string = True
            index += 1
    return "".join(result)


def closure(lean_root: Path, roots: tuple[str, ...]) -> dict[str, Path]:
    pending = list(roots)
    seen: dict[str, Path] = {}
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        path = module_path(lean_root, module)
        if not path.is_file():
            raise FileNotFoundError(f"missing project module {module}: {path}")
        seen[module] = path
        pending.extend(project_imports(path))
    return seen


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--lean-root",
        type=Path,
        default=Path(__file__).resolve().parents[1] / "lean",
    )
    parser.add_argument("modules", nargs="*", default=DEFAULT_ROOTS)
    args = parser.parse_args()

    modules = closure(args.lean_root.resolve(), tuple(args.modules))
    failures: list[tuple[str, str]] = []
    for module, path in sorted(modules.items()):
        text = without_comments(path.read_text(encoding="utf-8"))
        for token in FORBIDDEN:
            if token in text:
                failures.append((module, token))

    if failures:
        for module, token in failures:
            print(f"FAIL {module}: contains {token}")
        return 1

    print(
        "PASS kernel-only import closure: "
        f"{len(modules)} project modules reachable from {len(args.modules)} roots"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
