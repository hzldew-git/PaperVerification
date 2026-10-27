# Reproducing the core package

Use Python 3.11 or newer and Elan with `lake` on PATH. The toolchain file selects
Lean 4.32.1 automatically. The same commands work on Windows and Linux.

From a fresh checkout at the intended fixed revision:

```text
python Norm-Euclidean/tools/verify_public.py
python tools/check_no_manuscripts.py --root .
```

The first command checks the manifest and public boundary, runs
`lake -Kjobs=1 build NormEuclidean` inside `Norm-Euclidean/lean`, and runs the
registered statement/axiom audit. It stops on a failed step. Network access may
be needed to obtain the pinned toolchain and Git dependencies. No `lake update`
is required or recommended.

Optional mathlib cache setup, from `Norm-Euclidean/lean`:

```text
lake exe cache get
```

Only fixed external dependency caches are used in the release validation. A
clean-source check starts with no `Norm-Euclidean/lean/.lake/build` directory.
After that initial build, repeated verification may use its locally produced
objects. The manifest guards the proof sources, independent of cached objects.

To run only the inexpensive source and metadata gates:

```text
python Norm-Euclidean/tools/verify_public.py --static-only
```

To record a full result and readable types:

```text
python Norm-Euclidean/tools/verify_public.py --report Norm-Euclidean/results/verification.json --statements Norm-Euclidean/results/statement_types.txt
```

`--skip-build` is available for CI after a successful explicit build. Its report
records that the driver did not run the build itself; it is not equivalent to
a fresh-source build. Local build and diagnostic logs stay under `lean/.lake`
and are not part of the public package.

## Expected evidence

- Every selected source hash and import resolves against the manifest or a
  pinned external dependency.
- No unfinished/custom-axiom or kernel-bypass construct occurs in exported
  Lean code outside comments and strings.
- The root build and all registered declaration probes exit successfully.
- Each declaration has exactly one transitive axiom report, using only the
  three permitted standard axioms.
- No manuscript, opaque archive, compiled artifact, absolute local path or
  private manuscript metadata is included in the release payload.

The root repository manuscript-exclusion check also protects other packages.
The new package's workflow leaves the existing Trace-Euclidean checks intact.
Warnings about unused arguments and deprecated tactic spellings are reported
by Lean but do not establish a proof gap; errors and `sorry` are failures.
