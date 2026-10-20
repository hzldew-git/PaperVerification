# Mathematica computational supplement

- [TraceEuclideanVerification.m](TraceEuclideanVerification.m): complete,
  reusable Wolfram Language source.
- [TraceEuclideanVerification.pdf](TraceEuclideanVerification.pdf): mathematical
  explanations, all four Section 4 tables, classification outputs, all 115
  classification check outcomes, and the complete `.m` source.
- `results/`: actual JSON results, four complete CSV tables, and a SHA-256
  manifest binding the report to the code and public inputs.

Use this directory together with the parent `inputs/` directory from the
same repository revision. The package needs Mathematica or a licensed Wolfram
Engine; the recorded run used Mathematica 15.0.0.

## Run the computations

From the `Trace-Euclidean` directory:

```text
wolframscript -file mathematica/run.wls
wolframscript -file mathematica/run_voight.wls
```

The first command runs the core checks:

- 17 Section 4 assertions;
- 952 grid decisions, all separated by exact rational intervals;
- 24 classic-integral and 63 integral retained pairs;
- all 87 displayed volume upper bounds, with upward rounding;
- the original 115 exact classification assertions, with zero failures.

The second, optional command checks all 2,773 archived Voight rows.
It verifies each polynomial's irreducibility, total reality, index-square
identity and actual field discriminant. This extension has also been run
for the supplied report. Individual outcomes follow the archived row order
in `results/voight-rows-5.json` through `voight-rows-10.json`.
Counts of rows must not be interpreted as counts of distinct isomorphism classes.

Both wrappers return a nonzero exit status on failure. The `.m` package can
also be used interactively:

```mathematica
Get["mathematica/TraceEuclideanVerification.m"];
TraceEuclideanVerification`RunVerification[]
TraceEuclideanVerification`RunVoightIntegrity[]
```

An output directory may be supplied as the argument to either function.
Loading the file does not start a check, clear user symbols, change the
working directory, or terminate the Mathematica kernel.

## Regenerate and check the PDF

After running both computation commands:

```text
python -m pip install -r mathematica/requirements-report.txt
python mathematica/build_report.py
python tools/check_computational_report.py
python tools/check_no_manuscripts.py
python tools/check_public_metadata.py
```

The PDF builder reads the exact `.m` file and its JSON outputs. It rejects
missing results, unsuccessful checks, and mismatched code or public-input
hashes. The report checker also inspects PDF text, metadata, attachments,
and the result manifest. The code and public-input SHA-256 digests appear
on the cover; the PDF digest appears in the manifest. Regenerating a PDF
may change its binary digest through PDF creation metadata.
The builder normalizes generated JSON and CSV line endings to LF before
hashing, so the recorded digests also hold for a fresh Git checkout.

The existing independent implementation can be run with:

```text
python tools/verify_public.py
```

Its expected result remains 1,156 PASS. The original Mathematica scripts
under `checks/` remain available as independent comparison entry points.

## How to interpret the results

The grid's retention decisions and volume rounding use rational interval
endpoints. The displayed logarithmic values and the additional finite Gamma
checks use high-precision numerical evaluation. Retained pairs satisfy
necessary numerical conditions; existence is not asserted.

These computations trust Mathematica's implementation. They do not replace
the general mathematical proofs or the Lean kernel checks. In particular,
the field-list completeness input and the general Clark--Jagy
rational-farthest-point input remain governed by [TRUST.md](../TRUST.md).
The separately disclosed Lean `native_decide` dependency is unchanged.

## Troubleshooting

- **Wolfram executable or license missing:** install/activate Mathematica or
  Wolfram Engine, then check that `wolframscript` is available.
- **Input missing:** restore the parent `inputs/` directory from the same
  revision. File paths are resolved relative to the `.m` file.
- **Hash mismatch or stale report:** rerun both computation commands, then
  regenerate the PDF. Do not mix output files from different source revisions.
- **Failed check, message, or incomplete output:** preserve the local log
  and investigate the named check. Do not treat a partial output as a pass.
- **Report-library error:** install the pinned report requirements. These
  libraries format and inspect the report; Mathematica performs the computations.

No manuscript file, private manuscript identifier, or machine-specific path
is required to reproduce this supplement.
