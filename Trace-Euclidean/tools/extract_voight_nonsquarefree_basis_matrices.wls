(* Extract exact integral-basis matrices for archived Voight rows whose
   recorded field discriminant is not squarefree.  These matrices are
   certificate discovery data for the local maximality stage. *)

scriptDirectory = DirectoryName[$InputFileName];
packageDirectory = DirectoryName[scriptDirectory];
inputDirectory = FileNameJoin[{packageDirectory, "inputs", "voight"}];
outputFile = FileNameJoin[{packageDirectory, "results",
  "voight-nonsquarefree-basis-matrices.json"}];

tableSpecifications = {
  <|"file" -> "5-17.txt", "degree" -> 5, "lineRecords" -> False|>,
  <|"file" -> "6-16.txt", "degree" -> 6, "lineRecords" -> False|>,
  <|"file" -> "7-15.5.txt", "degree" -> 7, "lineRecords" -> False|>,
  <|"file" -> "8-15.txt", "degree" -> 8, "lineRecords" -> False|>,
  <|"file" -> "9-14.5.txt", "degree" -> 9, "lineRecords" -> False|>,
  <|"file" -> "10.txt", "degree" -> 10, "lineRecords" -> True|>
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

rationalPair[value_] := Module[{q = Together[value]},
  {Numerator[q], Denominator[q]}
];

extractRow[row_, degree_, rowNumber_] := Module[
  {fieldDiscriminant, coefficients, polynomial, polynomialDiscriminant,
    quotientDiscriminant, index, alpha, basis, basisPolynomials, matrix},
  fieldDiscriminant = row[[1]];
  coefficients = row[[2]];
  If[TrueQ[SquareFreeQ[fieldDiscriminant]], Return[Nothing]];

  polynomial = Sum[coefficients[[k + 1]] x^k, {k, 0, degree}];
  polynomialDiscriminant = Discriminant[polynomial, x];
  quotientDiscriminant = Quotient[polynomialDiscriminant,
    fieldDiscriminant];
  index = Sqrt[quotientDiscriminant];
  If[! TrueQ[IntegerQ[index] && index > 0],
    Print["FAIL index degree ", degree, " row ", rowNumber];
    Exit[1]
  ];

  alpha = Root[Function[{t}, Evaluate[polynomial /. x -> t]], 1];
  basis = NumberFieldIntegralBasis[alpha];
  basisPolynomials = Expand[AlgebraicNumberPolynomial[#, x]] & /@ basis;
  If[Length[basisPolynomials] != degree,
    Print["FAIL basis length degree ", degree, " row ", rowNumber];
    Exit[1]
  ];
  matrix = Transpose[
    PadRight[CoefficientList[#, x], degree] & /@ basisPolynomials];
  If[! TrueQ[Abs[Det[matrix]] == 1/index],
    Print["FAIL determinant degree ", degree, " row ", rowNumber];
    Exit[1]
  ];

  <|
    "degree" -> degree,
    "row_number" -> rowNumber,
    "field_discriminant" -> fieldDiscriminant,
    "coefficients" -> coefficients,
    "index" -> index,
    "matrix" -> Map[rationalPair, matrix, {2}]
  |>
];

records = Flatten[Table[
  specification = tableSpecifications[[tableIndex]];
  rows = readRows[specification];
  Print["Scanning degree ", specification["degree"], " (",
    Length[rows], " rows)"];
  DeleteCases[
    MapIndexed[
      extractRow[#1, specification["degree"], First[#2]] &,
      rows], Nothing],
  {tableIndex, Length[tableSpecifications]}]];

If[Length[records] != 1509,
  Print["FAIL expected 1509 records, found ", Length[records]];
  Exit[1]
];

Export[outputFile,
  <|"tool" -> $Version, "record_count" -> Length[records],
    "records" -> records|>,
  "RawJSON", "Compact" -> False];
Print["VOIGHT NONSQUAREFREE BASIS MATRICES: PASS (",
  Length[records], " records)"];
Exit[0];
