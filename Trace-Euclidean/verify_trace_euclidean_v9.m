(* ::Package:: *)
(*
  Reproducible verification of Trace-Euclidean-v9.tex.

  Interactive Mathematica:
    Get[".../verify_trace_euclidean_v9.m"]

  Batch mode with an exit code:
    wolframscript -file run_verification.wls

  The manuscript snapshot is read only. Generated files are written only to
  results/. The verification logic is divided into checks/*.wl so that a
  later manuscript change normally affects only the matching module and the
  entry in config/verification_manifest.json.
*)

ClearAll["Global`*"];
base = DirectoryName[$InputFileName];
inputDir = FileNameJoin[{base, "inputs"}];
resultDir = FileNameJoin[{base, "results"}];
snapshot = FileNameJoin[{base, "source_snapshot", "Trace-Euclidean-v9.tex"}];
inputFile = FileNameJoin[{inputDir, "manuscript_inputs.json"}];

If[!DirectoryQ[resultDir], CreateDirectory[resultDir, CreateIntermediateDirectories -> True]];
If[!FileExistsQ[inputFile],
  Print["Missing inputs/manuscript_inputs.json. Run tools/prepare_inputs.py first."];
  $VerificationExitCode = 1;
  Abort[]
];

input = Import[inputFile, "RawJSON"];
Get[FileNameJoin[{base, "lib", "verification_core.wl"}]];

say["Trace-Euclidean-v9 reproducible verification"];
say["Kernel: " <> $Version];

setVerificationContext["integrity", "package", "cryptographic version binding"];
sourceHash = input["source_sha256"];
If[FileExistsQ[snapshot] &&
    IntegerString[FileHash[snapshot, "SHA256"], 16, 64] =!= sourceHash,
  Print["The private manuscript snapshot does not match inputs/manuscript_inputs.json."];
  $VerificationExitCode = 1;
  Abort[]
];
check[
  "source-sha256-recorded",
  "integrity",
  StringQ[sourceHash] && StringLength[sourceHash] === 64 &&
    StringMatchQ[sourceHash, HexadecimalCharacter ..],
  sourceHash,
  "64 hexadecimal characters",
  "Digest produced by the private extraction step; a private maintainer build additionally checks the snapshot against it."
];

Do[
  setVerificationContext[item["module"], item["anchor"], "source-to-code binding"];
  check[
    "source-fragment-" <> item["id"],
    "source binding",
    TrueQ[item["present"]],
    item["source_line"],
    item["fragment"]
  ],
  {item, input["source_checks"]}
];

Get[FileNameJoin[{base, "checks", "analytic_bounds.wl"}]];
Get[FileNameJoin[{base, "checks", "admissible_tables.wl"}]];
Get[FileNameJoin[{base, "checks", "trace_geometry.wl"}]];
Get[FileNameJoin[{base, "checks", "gamma_diagnostics.wl"}]];

Export[FileNameJoin[{resultDir, "tests.json"}], rows, "RawJSON"];
Export[FileNameJoin[{resultDir, "tests.csv"}], Prepend[(Values /@ rows), Keys[First[rows]]], "CSV"];
Export[FileNameJoin[{resultDir, "numeric_values.json"}], numbers, "RawJSON"];
Export[FileNameJoin[{resultDir, "all_table_values.json"}], tableRows, "RawJSON"];
Export[FileNameJoin[{resultDir, "all_table_values.csv"}], Prepend[Values /@ tableRows, Keys[First[tableRows]]], "CSV"];
Export[FileNameJoin[{resultDir, "rational_certificates.json"}], certificates, "RawJSON"];
Export[FileNameJoin[{resultDir, "quadratic_fields.json"}], fieldRows, "RawJSON"];

counts = Counts[Lookup[rows, "status"]];
failures = Select[rows, #["status"] === "FAIL" &];
warnings = Select[rows, #["status"] === "WARN" &];
moduleCounts = Association @ KeyValueMap[
  #1 -> Counts[Lookup[#2, "status"]] &,
  GroupBy[rows, #["module"] &]
];
summary = <|
  "kernel" -> $Version,
  "source_sha256" -> sourceHash,
  "source_line_count" -> input["source_line_count"],
  "counts" -> counts,
  "module_counts" -> moduleCounts,
  "failures" -> Length[failures],
  "warnings" -> Length[warnings],
  "classical_pairs" -> Length[classicalPairs],
  "integral_pairs" -> Length[integralPairs],
  "quadratic_fields_tested" -> Length[fieldRows],
  "precision" -> 80,
  "interval_decimal_places" -> 40,
  "scope" -> "Exact symbolic calculations, certified rational signs, manuscript approximations, all four displayed tables, exact trace/Voronoi formulae, and square-free m up to the configured bound. General proofs and cited analytic theorems are outside the computational scope."
|>;
Export[FileNameJoin[{resultDir, "summary.json"}], summary, "RawJSON"];
say["SUMMARY " <> fmt[counts] <> "; failures=" <> ToString[Length[failures]] <> "; warnings=" <> ToString[Length[warnings]]];
Export[FileNameJoin[{resultDir, "verification_transcript.txt"}], StringRiffle[transcript, "\n"], "Text"];

$VerificationExitCode = Which[
  Length[failures] > 0, 1,
  Length[warnings] > 0, 2,
  True, 0
];

summary
