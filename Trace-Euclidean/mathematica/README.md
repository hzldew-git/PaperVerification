# Mathematica computational supplement

- [TraceEuclideanVerification.m](TraceEuclideanVerification.m): complete,
  reusable Wolfram Language source.
- `results/`: archived JSON results, four complete CSV tables, and a SHA-256
  manifest binding the results to the code and public inputs.

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
for the archived results. Individual outcomes follow the archived row order
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

## Check the archived results

From the `Trace-Euclidean` directory, run:

```text
python tools/check_computational_results.py
python tools/check_no_manuscripts.py
python tools/check_public_metadata.py
```

The result checker uses the Python standard library. It checks the code and
public-input SHA-256 digests, all 18 result-file digests, recorded check
outcomes, and the archived Voight row results. Use files from one repository
revision together. New computation outputs can be inspected separately;
their hashes must be checked and the result manifest refreshed before they
replace the archived results.

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
- **Hash mismatch:** restore the code, inputs and archived results from the
  same revision. Do not mix output files from different source revisions.
- **Failed check, message, or incomplete output:** preserve the local log
  and investigate the named check. Do not treat a partial output as a pass.

No manuscript file, private manuscript identifier, or machine-specific path
is required to reproduce this supplement.
