#!/usr/bin/env python3
"""Check the selected source package, build it, and audit exact declarations."""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

from lean_code_scan import code_without_comments, violations

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
PINS = {
    'mathlib': '520045ab14e26149ee970e2e617ca04b09bde5d6',
    'BongTheory': 'a1343b6e471cbf417cab0e09dc5876b74358260a',
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def package_files() -> list[Path]:
    result = []
    for directory, dirs, files in os.walk(ROOT):
        dirs[:] = [n for n in dirs if n not in {'.lake', '.git', '.elan', '__pycache__'}]
        result.extend(Path(directory) / n for n in files)
    return result


def static_checks() -> dict:
    manifest = json.loads((ROOT / 'proof_manifest.json').read_text(encoding='utf-8'))
    registry = json.loads((ROOT / 'declarations.json').read_text(encoding='utf-8'))
    rows = manifest['proof_files']
    names = [r['declaration'] for r in registry['declarations']]
    require(len(names) == len(set(names)) and bool(names), 'Duplicate or empty declaration registry')
    paths = [r['path'] for r in rows]
    modules = {r['module']: r['path'] for r in rows}
    require(len(paths) == len(set(paths)) == len(modules) == manifest['local_module_count'],
            'Duplicate module/path or incorrect manifest count')
    require((LEAN / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.32.1',
            'Toolchain pin changed')
    locked = json.loads((LEAN / 'lake-manifest.json').read_text(encoding='utf-8'))
    locked_pins = {p['name']: p['rev'] for p in locked['packages']}
    require(all(locked_pins.get(k) == v for k, v in PINS.items()), 'Dependency pin changed')
    config = (LEAN / 'lakefile.toml').read_text(encoding='utf-8')
    import tomllib
    parsed_config = tomllib.loads(config)
    requires = {p['name']: p for p in parsed_config['require']}
    require(requires['mathlib']['rev'] == 'v4.32.1' and
            requires['BongTheory']['rev'] == PINS['BongTheory'], 'Lake requirement changed')

    for row in rows:
        path = LEAN / row['path']
        require(path.resolve().is_relative_to(LEAN), 'Manifest path escapes package')
        require(path.is_file() and digest(path) == row['sha256'], 'Proof hash mismatch: ' + row['path'])
    actual_paths = {p.relative_to(LEAN).as_posix() for folder in
                    [LEAN / 'NormEuclidean', LEAN / 'ArithmeticClassFields']
                    for p in folder.rglob('*.lean')}
    require(actual_paths == set(paths), 'Unregistered or missing local proof sources')
    modules['NormEuclidean'] = 'NormEuclidean.lean'
    root_imports = []
    source_count = 0
    for path in [LEAN / p for p in paths] + [LEAN / 'NormEuclidean.lean', LEAN / 'validation/Core.lean']:
        source_count += 1
        source = path.read_text(encoding='utf-8')
        require(not violations(source), 'Unfinished/custom-axiom construct: ' + path.name)
        code = code_without_comments(source)
        forbidden = r'\bnative_decide\b|\brun_tac\b|\bimplemented_by\b|^\s*(?:unsafe|extern)\b|debug\.skipKernelTC'
        require(not re.search(forbidden, code, re.M), 'Kernel-bypass construct: ' + path.name)
        imports = []
        for match in re.finditer(r'(?m)^\s*(?:public\s+)?import\s+([^\n]+)', code):
            imports.extend(match[1].split())
        if path == LEAN / 'NormEuclidean.lean':
            root_imports = imports
        for name in imports:
            require(name in modules or name.startswith(('Mathlib.', 'Bong.')),
                    'Unresolved import: ' + name)
    require(root_imports == manifest['entry_modules'], 'Release aggregator differs from manifest')

    probe = (LEAN / 'validation/Core.lean').read_text(encoding='utf-8')
    checks = re.findall(r'^#check\s+@(\S+)', probe, re.M)
    axioms = re.findall(r'^#print axioms\s+(\S+)', probe, re.M)
    require(checks == names and axioms == names, 'Probe does not match declaration registry')

    local_path = re.compile(r'(?<![A-Za-z0-9])[A-Za-z]:[\\/]')
    private_meta = re.compile(r'(?:author|manuscript)[_ -]?(?:source[_ -]?)?sha[-_ ]?256', re.I)
    internal_label = re.compile(r'\bv[23]\.\d+(?:\.\d+)?\b', re.I)
    files = package_files()
    forbidden_suffixes = {'.tex', '.pdf', '.zip', '.tar', '.gz', '.tgz', '.7z', '.rar',
                          '.olean', '.ilean', '.dll', '.exe', '.so', '.o', '.a', '.pyc'}
    for path in files:
        relative = path.relative_to(ROOT).as_posix()
        require(path.suffix.lower() not in forbidden_suffixes, 'Private/build artifact: ' + relative)
        require(not re.search(r'\bv\d+\.\d+', relative, re.I), 'Versioned filename: ' + relative)
        require(not ({'source_snapshot', 'manuscript', 'manuscripts'} &
                     {part.lower() for part in path.relative_to(ROOT).parts}),
                'Private directory: ' + relative)
        raw = path.read_bytes()
        require(not raw.startswith(b'%PDF-'), 'PDF content: ' + relative)
        text = raw.decode('utf-8')
        require(not local_path.search(text), 'Absolute local path: ' + relative)
        require(not private_meta.search(text), 'Private manuscript metadata: ' + relative)
        require(not internal_label.search(text), 'Internal manuscript label: ' + relative)
        require(not ('\\' + 'documentclass' in text and '\\' + 'begin{document}' in text),
                'Complete document content: ' + relative)
    return {'status': 'PASS', 'package_files': len(files), 'local_proof_modules': len(rows),
            'lean_files_checked': source_count, 'registered_declarations': len(names),
            'proof_manifest_sha256': digest(ROOT / 'proof_manifest.json'),
            'dependency_lock_sha256': digest(LEAN / 'lake-manifest.json')}


def run_logged(command: list[str], log: Path) -> str:
    environment = dict(os.environ)
    environment.setdefault('LEAN_NUM_THREADS', '1')
    with log.open('w', encoding='utf-8', newline='\n') as output:
        process = subprocess.run(command, cwd=LEAN, env=environment,
                                 stdout=output, stderr=subprocess.STDOUT)
    text = log.read_text(encoding='utf-8', errors='replace')
    if process.returncode:
        print('\n'.join(text.splitlines()[-35:]), file=sys.stderr)
        raise RuntimeError('Command failed: ' + ' '.join(command[1:]))
    require('declaration uses ' + "'sorry'" not in text, 'Lean reported an unfinished declaration')
    return text


def write_json(path: Path, data: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2) + '\n', encoding='utf-8', newline='\n')


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--static-only', action='store_true')
    parser.add_argument('--skip-build', action='store_true')
    parser.add_argument('--report', type=Path)
    parser.add_argument('--statements', type=Path)
    args = parser.parse_args()
    require(not (args.static_only and args.skip_build), 'Choose only one abbreviated mode')
    static = static_checks()
    print(f"STATIC CHECK: PASS ({static['local_proof_modules']} modules; "
          f"{static['registered_declarations']} registered declarations)", flush=True)
    report = {'status': 'PASS', 'scope': 'selected core results', 'static': static,
              'correspondence_status': 'PROVISIONAL_MATCH', 'paper_wide_certificate': False,
              'hosted_ci_claimed': False, 'build': 'not_run', 'declaration_audit': 'not_run'}
    if not args.static_only:
        lake = shutil.which('lake')
        require(lake is not None, 'Elan/lake is not available on PATH')
        logs = LEAN / '.lake/release-audit'
        logs.mkdir(parents=True, exist_ok=True)
        if not args.skip_build:
            print('Building selected core sources...', flush=True)
            run_logged([lake, '-Kjobs=1', 'build', 'NormEuclidean'], logs / 'build.log')
            report['build'] = 'PASS'
            print('BUILD: PASS', flush=True)
        text = run_logged([lake, 'env', 'lean', 'validation/Core.lean'], logs / 'declarations.log')
        names = [r['declaration'] for r in json.loads(
            (ROOT / 'declarations.json').read_text(encoding='utf-8'))['declarations']]
        entries = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", ' '.join(text.split()))
        require(Counter(name for name, _ in entries) == Counter(names), 'Incomplete or duplicate axiom reports')
        checked = []
        for name, raw in entries:
            used = {v.strip() for v in raw.split(',') if v.strip()}
            require(used <= STANDARD, 'Unexpected axioms for ' + name + ': ' + repr(sorted(used)))
            statement_head = r'^@?' + re.escape(name) + r'(?:\.\{[^}\r\n]*\})?\s*:'
            require(re.search(statement_head, text, re.M) is not None,
                    'Missing elaborated statement for ' + name)
            checked.append({'declaration': name, 'axioms': sorted(used)})
        report['declaration_audit'] = 'PASS'
        report['checked_declarations'] = checked
        report['checked_at_utc'] = datetime.now(timezone.utc).isoformat()
        if args.statements:
            # Keep actual declarations and axiom reports; machine path warnings are internal logs.
            cleaned = '\n'.join(line for line in text.splitlines()
                                if not line.startswith('warning: could not canonicalize path:')) + '\n'
            require(not re.search(r'(?<![A-Za-z0-9])[A-Za-z]:[\\/]', cleaned),
                    'Diagnostic output contains local paths; inspect the private log')
            args.statements.parent.mkdir(parents=True, exist_ok=True)
            args.statements.write_text(cleaned, encoding='utf-8', newline='\n')
        print(f'DECLARATION AUDIT: PASS ({len(checked)} statements; standard axioms only)', flush=True)
    if args.report:
        write_json(args.report, report)
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (RuntimeError, OSError, ValueError, KeyError) as exc:
        print('VERIFICATION FAILED: ' + str(exc), file=sys.stderr)
        raise SystemExit(1)
