(* Independent Mathematica verification of the archived Voight rows. *)

scriptDirectory = DirectoryName[$InputFileName];
packageDirectory = DirectoryName[scriptDirectory];
inputDirectory = FileNameJoin[{packageDirectory, "inputs", "voight"}];
outputFile =
  FileNameJoin[{packageDirectory, "results", "voight-polynomial-integrity.json"}];

tableSpecifications = {
  <|"file" -> "5-17.txt", "degree" -> 5, "rows" -> 674,
    "lineRecords" -> False,
    "sha256" ->
      "7c2ce57f51de3ad34bb60ade85659689fc629406315e9699a144f737d1b34192"|>,
  <|"file" -> "6-16.txt", "degree" -> 6, "rows" -> 827,
    "lineRecords" -> False,
    "sha256" ->
      "6e6bc75b54ad2643a42a3dfdd9497347eb89735d00c5b7367e934ad32d8ae082"|>,
  <|"file" -> "7-15.5.txt", "degree" -> 7, "rows" -> 301,
    "lineRecords" -> False,
    "sha256" ->
      "95ed179560eb866445eee3da22826cf98cc5eb0bc7f5091c27f4d332dc421a3d"|>,
  <|"file" -> "8-15.txt", "degree" -> 8, "rows" -> 164,
    "lineRecords" -> False,
    "sha256" ->
      "204a0ea04e2f4079f6fea20369ad8822d4d678a718272b9aaea68cf144b83294"|>,
  <|"file" -> "9-14.5.txt", "degree" -> 9, "rows" -> 15,
    "lineRecords" -> False,
    "sha256" ->
      "9c14aa90371184020bb121c36e63ceaa5bd4ada0eb55198fd94d4df67d6d3821"|>,
  <|"file" -> "10.txt", "degree" -> 10, "rows" -> 792,
    "lineRecords" -> True,
    "sha256" ->
      "cceac525009d9ab6b947e17186a5e74df2643eace152955702d306af6defbe83"|>
};

toMathematicaExpression[text_] :=
  ToExpression[StringReplace[text, {"[" -> "{", "]" -> "}"}]];

readRows[specification_] := Module[{path, text, lines},
  path = FileNameJoin[{inputDirectory, specification["file"]}];
  text = Import[path, "Text"];
  If[TrueQ[specification["lineRecords"]],
    lines = Select[StringSplit[text, {"\r\n", "\n"}],
      StringLength[StringTrim[#]] > 0 &];
    toMathematicaExpression /@ lines,
    toMathematicaExpression[text]
  ]
];

checkRow[row_, degree_] := Module[
  {fieldDiscriminant, coefficients, polynomial, polynomialDiscriminant,
    quotient, index, irreducible, totallyReal, fieldDiscriminantComputed},
  If[! ListQ[row] || Length[row] != 2 || ! IntegerQ[row[[1]]] ||
      ! ListQ[row[[2]]] || ! And @@ (IntegerQ /@ row[[2]]) ||
      Length[row[[2]]] != degree + 1 || Last[row[[2]]] != 1,
    Return[<|"shape" -> False|>]
  ];
  fieldDiscriminant = row[[1]];
  coefficients = row[[2]];
  polynomial = Sum[coefficients[[k + 1]] x^k, {k, 0, degree}];
  polynomialDiscriminant = Discriminant[polynomial, x];
  quotient = If[Divisible[polynomialDiscriminant, fieldDiscriminant],
    Quotient[polynomialDiscriminant, fieldDiscriminant], -1];
  index = If[quotient > 0 && IntegerQ[Sqrt[quotient]], Sqrt[quotient], -1];
  irreducible = TrueQ[IrreduciblePolynomialQ[polynomial]];
  totallyReal = TrueQ[CountRoots[polynomial, {x, -Infinity, Infinity}] == degree];
  fieldDiscriminantComputed = NumberFieldDiscriminant[
    Root[Function[z, Evaluate[polynomial /. x -> z]], 1]];
  <|
    "shape" -> True,
    "irreducible" -> irreducible,
    "totallyReal" -> totallyReal,
    "indexSquare" -> (index > 0),
    "fieldDiscriminant" ->
      TrueQ[fieldDiscriminantComputed == fieldDiscriminant],
    "index" -> index
  |>
];

checkTable[specification_] := Module[
  {path, hash, rows, checks, shapePass, irreduciblePass, indexPass,
    totallyRealPass, fieldPass, indices, failures},
  path = FileNameJoin[{inputDirectory, specification["file"]}];
  hash = IntegerString[FileHash[path, "SHA256"], 16, 64];
  If[hash != specification["sha256"],
    Print["FAIL hash ", specification["file"]]; Exit[1]
  ];
  rows = readRows[specification];
  If[Length[rows] != specification["rows"],
    Print["FAIL row count ", specification["file"]]; Exit[1]
  ];
  checks = checkRow[#, specification["degree"]] & /@ rows;
  shapePass = Count[checks, association_ /; TrueQ[association["shape"]]];
  irreduciblePass =
    Count[checks, association_ /; TrueQ[association["irreducible"]]];
  totallyRealPass =
    Count[checks, association_ /; TrueQ[association["totallyReal"]]];
  indexPass = Count[checks, association_ /; TrueQ[association["indexSquare"]]];
  fieldPass =
    Count[checks, association_ /; TrueQ[association["fieldDiscriminant"]]];
  indices = Cases[checks, association_ /; IntegerQ[association["index"]] :>
    association["index"]];
  failures = Pick[Range[Length[checks]],
    Map[! (TrueQ[#["shape"]] && TrueQ[#["irreducible"]] &&
        TrueQ[#["totallyReal"]] && TrueQ[#["indexSquare"]] &&
        TrueQ[#["fieldDiscriminant"]]) &,
      checks]];
  Print[specification["file"], ": ", Length[rows], " rows, ",
    fieldPass, " field discriminants verified"];
  <|
    "file" -> specification["file"],
    "degree" -> specification["degree"],
    "sha256" -> hash,
    "rows" -> Length[rows],
    "shape_pass" -> shapePass,
    "irreducible_pass" -> irreduciblePass,
    "totally_real_pass" -> totallyRealPass,
    "polynomial_discriminant_square_index_pass" -> indexPass,
    "field_discriminant_pass" -> fieldPass,
    "maximum_index" -> Max[indices],
    "failed_rows" -> failures,
    "pass" -> (failures === {})
  |>
];

tableResults = checkTable /@ tableSpecifications;
totalRows = Total[tableResults[[All, "rows"]]];
summary = <|
  "tool" -> $Version,
  "tables" -> tableResults,
  "total_rows" -> totalRows,
  "irreducible_pass" -> Total[tableResults[[All, "irreducible_pass"]]],
  "totally_real_pass" -> Total[tableResults[[All, "totally_real_pass"]]],
  "polynomial_discriminant_square_index_pass" ->
    Total[tableResults[[All, "polynomial_discriminant_square_index_pass"]]],
  "field_discriminant_pass" ->
    Total[tableResults[[All, "field_discriminant_pass"]]],
  "pass" -> And @@ tableResults[[All, "pass"]]
|>;

Export[outputFile, summary, "RawJSON", "Compact" -> False];
If[TrueQ[summary["pass"]],
  Print["VOIGHT POLYNOMIAL INTEGRITY: PASS (", totalRows, " rows)"]; Exit[0],
  Print["VOIGHT POLYNOMIAL INTEGRITY: FAIL"]; Exit[1]
];
