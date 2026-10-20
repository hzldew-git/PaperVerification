# Mathematica computational supplement

- [TraceEuclideanVerification.m](TraceEuclideanVerification.m): complete,
  reusable Wolfram Language source.
- [TraceEuclideanVerification.tex](TraceEuclideanVerification.tex): editable
  LaTeX report, including all result tables and a direct inclusion of the
  sibling `.m` file.
- [TraceEuclideanVerification.pdf](TraceEuclideanVerification.pdf): mathematical
  explanations, all four Section 4 tables, classification outputs, all 115
  classification check outcomes, and the complete `.m` source.
- `results/`: actual JSON results, four complete CSV tables, and a SHA-256
  manifest binding the report to the code and public inputs.

The `.m`, `.tex` and `.pdf` files share the same basename. The PDF is compiled
from the TeX source using XeLaTeX; no screenshots of code or results are used.

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

## Compile the supplied TeX

For a PDF-only rebuild, download the `.tex` and `.m` files into the same
directory. A TeX installation with XeLaTeX, `latexmk`, the Latin Modern fonts,
and the packages listed in the TeX preamble is required. Run in that directory:

```text
latexmk -xelatex -halt-on-error TraceEuclideanVerification.tex
```

Neither Mathematica nor the result JSON files are needed for this command.
The supplied numeric content is already included in the TeX source.
The released PDF was compiled with XeTeX from TeX Live 2025; the exact
compiler identification is recorded in the artifact manifest.

## Refresh numerical content and check the report

After computing new results, or to refresh the report from the supplied
checked results, run from the `Trace-Euclidean` directory:

```text
python -m pip install -r mathematica/requirements-report.txt
python mathematica/build_report.py
python tools/check_computational_report.py
python tools/check_no_manuscripts.py
python tools/check_public_metadata.py
```

The report builder reads the exact `.m` file and its JSON outputs. It rejects
missing results, unsuccessful checks, and mismatched code or public-input
hashes. It refreshes only the `% BEGIN GENERATED:` / `% END GENERATED:` blocks
in the TeX file and then compiles the PDF. Prose and layout outside those
blocks are preserved. The complete source appendix uses `\lstinputlisting`
to read the sibling `.m` file directly. TeX intermediate files go to
`mathematica/tmp/tex-build/`, which is excluded from Git.

The report checker compares all generated TeX blocks with the JSON results
and every printed code line with the `.m` source. It also inspects PDF text,
metadata, attachments, all check identifiers, and the result manifest.
The code and public-input SHA-256 digests appear in the run identification;
the TeX and PDF digests appear in the manifest. Regenerating a PDF
may change its binary digest through PDF creation metadata.
The builder normalizes generated JSON and CSV line endings to LF before
hashing, so the recorded digests also hold for a fresh Git checkout.

To edit the report, change text outside the generated blocks and run
`build_report.py` again. Changes inside those blocks will be replaced by the
checked results. `build_report.py --tex-only` updates the TeX and CSV files
without compiling; the PDF and manifest remain stale until a full build.
Formatting edits do not require rerunning Mathematica when the code, inputs
and validated JSON results are unchanged. Changes to computations or inputs
require fresh corresponding results.

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
- **TeX executable, font or package missing:** install a complete TeX Live or
  equivalent distribution and make `xelatex` and `latexmk` available. Keep the
  `.m` beside the `.tex`, and inspect the compiler log if an error remains.
- **Edited PDF does not match its manifest:** use `build_report.py` to compile
  the TeX and refresh the manifest together. A manual TeX compilation alone
  does not update the recorded PDF digest.

No manuscript file, private manuscript identifier, or machine-specific path
is required to reproduce this supplement.
