from __future__ import annotations

import argparse
import subprocess
from pathlib import Path


DOCUMENT_SUFFIXES = {".tex", ".pdf"}
ARCHIVE_SUFFIXES = {".zip", ".tar", ".tgz", ".gz", ".7z", ".rar"}
FORBIDDEN_PARTS = {"source_snapshot", "manuscript", "manuscripts"}


def repository_files(root: Path) -> list[Path]:
    command = [
        "git",
        "-C",
        str(root),
        "ls-files",
        "--cached",
        "--others",
        "--exclude-standard",
        "-z",
    ]
    completed = subprocess.run(command, check=True, capture_output=True)
    return [root / item.decode("utf-8") for item in completed.stdout.split(b"\0") if item]


def read_allowlist(root: Path) -> set[str]:
    path = root / ".verification-document-allowlist"
    entries: set[str] = set()
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if line and not line.startswith("#"):
            entries.add(Path(line).as_posix())
    return entries


def looks_like_tex_document(path: Path) -> bool:
    if path.stat().st_size > 10 * 1024 * 1024:
        return False
    try:
        text = path.read_text(encoding="utf-8")
    except (UnicodeDecodeError, OSError):
        return False
    documentclass = "\\" + "documentclass"
    begin_document = "\\" + "begin{document}"
    return documentclass in text and begin_document in text


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Reject manuscript sources, manuscript PDFs, and opaque archives."
    )
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    root = args.root.resolve()
    allowlist = read_allowlist(root)
    files = repository_files(root)
    errors: list[str] = []
    seen_documents: set[str] = set()

    for path in files:
        relative = path.relative_to(root).as_posix()
        lowered_parts = {part.lower() for part in Path(relative).parts}
        suffix = path.suffix.lower()

        if lowered_parts & FORBIDDEN_PARTS:
            errors.append(f"forbidden private-work directory: {relative}")
            continue

        if suffix in ARCHIVE_SUFFIXES or relative.lower().endswith(".tar.gz"):
            errors.append(f"opaque archive is not permitted: {relative}")
            continue

        if suffix in DOCUMENT_SUFFIXES:
            seen_documents.add(relative)
            if relative not in allowlist:
                errors.append(f"unapproved TeX/PDF document: {relative}")

        if path.is_file():
            try:
                header = path.read_bytes()[:5]
            except OSError as exc:
                errors.append(f"cannot inspect {relative}: {exc}")
                continue
            if header == b"%PDF-" and relative not in allowlist:
                errors.append(f"unapproved PDF content: {relative}")
            if looks_like_tex_document(path) and relative not in allowlist:
                errors.append(f"unapproved complete TeX document: {relative}")

    missing = sorted(allowlist - seen_documents)
    errors.extend(f"allowlisted verification document is missing: {path}" for path in missing)

    if errors:
        print("MANUSCRIPT POLICY CHECK: FAIL")
        for error in errors:
            print(f"- {error}")
        return 1

    print(
        "MANUSCRIPT POLICY CHECK: PASS "
        f"({len(files)} files inspected; {len(seen_documents)} approved TeX/PDF documents)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
