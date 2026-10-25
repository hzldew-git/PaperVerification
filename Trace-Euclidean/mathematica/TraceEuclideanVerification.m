(* Trace-Euclidean: reproducible Mathematica computations.
   Load this file with Get, then call RunVerification[].
   RunVoightIntegrity[] is the separate, longer archived-row check.
   All paths are relative to this file. Loading it does not run checks,
   change the working directory, or clear the user's symbols.
   Archived JSON and CSV results record runs of this exact source file. *)
BeginPackage["TraceEuclideanVerification`"];
RunVerification::usage =
  "RunVerification[outputDirectory] checks Section 4 and the classification.";
RunVoightIntegrity::usage =
  "RunVoightIntegrity[outputDirectory] checks all 2773 archived Voight rows.";
Begin["`Private`"];
baseDirectory = DirectoryName[$InputFileName];
packageDirectory = ParentDirectory[baseDirectory];
codeFile = FileNameJoin[{baseDirectory, "TraceEuclideanVerification.m"}];
inputFile = FileNameJoin[{packageDirectory, "inputs", "verification_inputs.json"}];
sha[path_] := IntegerString[FileHash[path, "SHA256"], 16, 64];
text[x_] := ToString[x, InputForm];
fail[name_] := Throw[Failure["Verification", <|"check" -> name|>], failureTag];
prepare[dir_] := (
  outputDirectory = If[dir === Automatic,
    FileNameJoin[{baseDirectory, "results"}], ExpandFileName[dir]];
  If[!DirectoryQ[outputDirectory],
    CreateDirectory[outputDirectory, CreateIntermediateDirectories -> True]];
  If[!DirectoryQ[outputDirectory], fail["output_directory"]];
);
writeJSON[name_, data_] := If[
  Export[FileNameJoin[{outputDirectory, name}], data, "RawJSON"] === $Failed,
  fail["export_" <> name]];
provenance[] := <|"tool" -> $Version, "code_sha256" -> sha[codeFile],
  "input_sha256" -> sha[inputFile],
  "run_utc" -> DateString[Now, {"ISODate", "T", "Time", "Z"}, TimeZone -> 0]|>;

(* Section 4: numerical evaluation and exact rational sign certificates.
   beta(d) is an arithmetic input. These computations do not prove its
   number-field lower-bound interpretation or the existence of retained pairs. *)
minDiscriminants =
  {1, 5, 49, 725, 14641, 300125, 20134393, 282300416, 9685993193};
beta[d_Integer] := Which[
  d <= 9, minDiscriminants[[d]]^(1/d), d == 10, 14,
  d == 11, 14083/1000, True, (36347/1000) Exp[-10667/(1000 d)]];
logVolume[n_Integer, d_Integer] :=
  n d Log[Pi d] - 2 LogGamma[n d/2 + 1] - n d Log[beta[d]];
effectiveC[case_, n_Integer] := If[case == "classic" || n == 1, 1, 2];
decimalString[x_] := text[N[x, 60]];
(* Only integer/rational strings from the public JSON input are accepted. *)
readRational[s_String] := Module[{parts},
  If[!StringMatchQ[s, RegularExpression["-?[0-9]+(/[0-9]+)?"]],
    fail["rational_input"]];
  parts = FromDigits /@ StringSplit[StringTrim[s, "-"], "/"];
  If[StringStartsQ[s, "-"], -1, 1] *
    If[Length[parts] == 1, First[parts], parts[[1]]/parts[[2]]]
];
snap[{lo_, hi_}] := {Floor[10^85 lo], Ceiling[10^85 hi]}/10^85;
atanBounds[q_] := Module[{lo},
  lo = Sum[(-1)^j/((2 j + 1) q^(2 j + 1)), {j, 0, 79}];
  {lo, lo + 1/(161 q^161)}
];
expBounds[x_] := Module[{s = 1, t = 1, j},
  If[!TrueQ[0 <= x < 182], fail["exponential_domain"]];
  Do[t = t x/j; s += t, {j, 1, 180}];
  snap[{s, s + (t x/181)/(1 - x/182)}]
];
(* Alternating arctangent bounds and Machin's identity enclose pi.
   The exponential tail is bounded by a geometric series after term 180.
   Every operation in these interval routines is rational arithmetic. *)
initializeIntervals[] := Module[{p = atanBounds[5], q = atanBounds[239]},
  piBounds = snap[{16 p[[1]] - 4 q[[2]], 16 p[[2]] - 4 q[[1]]}];
  eBounds = expBounds[1];
  expBoundsMain = expBounds[10667/1000];
  expBoundsCutoff = expBounds[10667/15000];
];
volumeInterval[n_, d_] := Module[{m = n d, k, coefficient, power},
  k = Floor[m/2];
  If[EvenQ[m],
    coefficient = d^m/(k!)^2; power = m,
    coefficient = d^m 16^(k + 1) ((k + 1)!)^2/((2 k + 2)!)^2;
    power = m - 1];
  coefficient /= Which[d <= 9, minDiscriminants[[d]]^n,
    d == 10, 14^m, d == 11, (14083/1000)^m,
    True, (36347/1000)^m];
  coefficient piBounds^power If[d >= 12, expBoundsMain^n, {1, 1}]
];
upperSix[x_] := Module[{k, unit},
  k = IntegerLength[Numerator[x]] - IntegerLength[Denominator[x]];
  If[x < 10^k, k--];
  unit = 10^(k - 5);
  Ceiling[x/unit] unit
];
sectionFour[] := Module[
  {workingPrecision = 90, rows = {}, grid = {}, certs = {}, summary,
   checks, n, d, case, c, lv, margin, keep, row, caseRows, bounds,
   threshold, decision, upper, published, selected, data, certificate},
  initializeIntervals[];
  Do[
    c = effectiveC[case, n];
    lv = N[logVolume[n, d], workingPrecision];
    margin = N[logVolume[n, d] + n d Log[c], workingPrecision];
    keep = TrueQ[margin >= 0];
    bounds = volumeInterval[n, d];
    threshold = If[case == "classic" || n == 1, 1, 2^(-n d)];
    decision = Which[bounds[[1]] >= threshold, True,
      bounds[[2]] < threshold, False, True, fail["unresolved_interval"]];
    If[decision =!= keep, fail["numeric_interval_disagreement"]];
    row = <|"case" -> case, "n" -> n, "d" -> d,
      "log_volume_bound" -> decimalString[lv],
      "h_new" -> decimalString[lv/n + If[case == "integral", d Log[2], 0]],
      "volume_bound" -> decimalString[Exp[lv]],
      "beta" -> decimalString[beta[d]],
      "log_feasibility_margin" -> decimalString[margin], "retained" -> keep|>;
    AppendTo[grid, row];
    AppendTo[certs, <|"case" -> case, "n" -> n, "d" -> d,
      "retained" -> decision, "separated" -> True|>];
    If[keep,
      upper = upperSix[bounds[[2]]];
      AssociateTo[row, "upper_six_rational" -> text[upper]];
      AppendTo[rows, row]],
    {case, {"classic", "integral"}}, {d, 1, 14}, {n, 1, 34}];
  summary = Association@Table[
    caseRows = Select[rows, #["case"] == case &];
    case -> <|"count" -> Length[caseRows],
      "N_d" -> Table[Max[Prepend[
        (#["n"] & /@ Select[caseRows, #["d"] == d &]), 0]], {d, 1, 14}],
      "D_n" -> Table[Max[Prepend[
        (#["d"] & /@ Select[caseRows, #["n"] == n &]), 0]], {n, 1, 34}]|>,
    {case, {"classic", "integral"}}];
  checks = <|
    "summary_complete" -> FreeQ[summary, _Missing],
    "coarse_degree_cutoff_exact" ->
      ((36347/1000)/expBoundsCutoff[[2]] > 2 piBounds[[2]] eBounds[[2]]),
    "coarse_rank_cutoff_exact" -> (4 piBounds[[2]] eBounds[[2]] < 35),
    "all_952_comparisons_separated" -> (Length[certs] == 952),
    "expected_counts" -> (summary["classic"]["count"] == 24 &&
      summary["integral"]["count"] == 63),
    "gamma_batir_lower_bound_on_grid_numeric" -> And @@ Table[TrueQ[
      N[LogGamma[m/2+1] -
        (Log[2]/2-m/2+(m/2+1/2) Log[m/2+1/2]), 70] >= 0], {m, 1, 476}],
    "gamma_strict_consequence_on_grid_numeric" -> And @@ Table[TrueQ[
      N[Log[m+1]/2+(m/2) Log[1+1/m], 70] > 0], {m, 1, 476}]|>;
  Do[
    selected = Select[rows, #["case"] == case &];
    published = publicInput["table_rows"][case];
    AssociateTo[checks, {
      case <> "_published_pairs" ->
        (Lookup[selected, {"n", "d"}] == Lookup[published, {"n", "d"}]),
      case <> "_published_rank_bounds" ->
        (summary[case]["N_d"] == publicInput["rank_bounds_by_degree"][case]),
      case <> "_published_degree_bounds" ->
        (summary[case]["D_n"] == publicInput["degree_bounds_by_rank"][case]),
      case <> "_published_h_numeric_rounding" -> And @@ MapThread[
        (Abs[ToExpression[#1["h_new"]] -
          readRational[#2["h_display"]]] <= 1/2000000) &,
        {selected, published}],
      case <> "_published_volume_upper_exact" -> And @@ MapThread[
        (readRational[#1["upper_six_rational"]] ==
          readRational[#2["volume_upper_display"]]) &, {selected, published}]}],
    {case, {"classic", "integral"}}];
  certificate = <|
    "method" -> "Rational intervals; Machin identity; series tail bounds; half-integer Gamma values.",
    "pi_interval" -> (text /@ piBounds),
    "e_interval" -> (text /@ eBounds),
    "exp_main_interval" -> (text /@ expBoundsMain),
    "exp_cutoff_interval" -> (text /@ expBoundsCutoff),
    "comparisons" -> Length[certs], "unresolved_comparisons" -> 0,
    "classic_retained" -> summary["classic"]["count"],
    "integral_retained" -> summary["integral"]["count"],
    "upward_rounded_values" -> Length[rows], "decisions" -> certs|>;
  data = <|"provenance" -> provenance[],
    "working_precision" -> workingPrecision,
    "minimal_discriminants" -> minDiscriminants,
    "summary" -> summary, "checks" -> checks, "rows" -> rows, "grid" -> grid,
    "all_passed" -> And @@ (TrueQ /@ Values[checks])|>;
  writeJSON["section4_tables.json", data];
  writeJSON["rational_certificate.json", certificate];
  KeyValueMap[Print[If[TrueQ[#2], "PASS: ", "FAIL: "], #1] &, checks];
  If[!TrueQ[data["all_passed"]], fail["section4_checks"]];
  Print["SECTION 4: 952 certified decisions; 24 / 63 retained pairs."];
  data
];

(* The following classification calculations preserve the released
   115 assertions and the independent finite Voronoi computation. *)
classification[] := Module[{},
checks = <||>;
checkRecords = {};
truth[x_] := TrueQ[FullSimplify[x]];
SetAttributes[check, HoldRest];
check[name_, statement_] := Module[{value = truth[statement]},
  AssociateTo[checks, name -> value];
  AppendTo[checkRecords,
    <|"id" -> name, "expected" -> True, "actual" -> value, "pass" -> value|>]
];
squareFreeIntegerQ[k_Integer] := And @@ (Last[#] == 1 & /@ FactorInteger[k]);
fundamentalDiscriminant[d_] := If[Mod[d, 4] == 1, d, 4 d];
omega[d_] := If[Mod[d, 4] == 1, (1 + Sqrt[d])/2, Sqrt[d]];
conjugate[d_, x_] := FullSimplify[x /.
  ((Power[base_Integer, exponent_Rational] /; base == d && Denominator[exponent] == 2) :>
    -base^exponent)];
fieldTrace[d_, x_] := FullSimplify[x + conjugate[d, x]];
fieldNorm[d_, x_] := FullSimplify[x conjugate[d, x]];
gram[t_] := {{t[[1]], t[[2]]}, {t[[2]], t[[3]]}};
canonicalGram[t_] := {Min[t[[1]], t[[3]]], t[[2]], Max[t[[1]], t[[3]]]} ;
rho[t_] := With[{a0 = t[[1]], b0 = t[[2]], c0 = t[[3]]},
  a0 c0 (a0 + c0 - 2 b0)/(4 (a0 c0 - b0^2))];
cjE[a0_, b0_, c0_] := a0 c0 (a0 - b0 + c0)/(4 a0 c0 - b0^2);
check["CJ_coefficient_order_and_formula", cjE[cc, 2 bb, aa] == rho[{aa, bb, cc}]];
check["CJ_lower_bound_identity", rho[{aa, bb, cc}] - aa/4 == aa (cc - bb)^2/(4 (aa cc - bb^2))];
check["CJ_polarization_normalization",
  Expand[({x1+y1,x2+y2}.{{aa,bb},{bb,cc}}.{x1+y1,x2+y2}) -
    ({x1,x2}.{{aa,bb},{bb,cc}}.{x1,x2}) - ({y1,y2}.{{aa,bb},{bb,cc}}.{y1,y2})] ==
    2 {x1,x2}.{{aa,bb},{bb,cc}}.{y1,y2}];
check["integer_upper_bound_A_7", Reduce[aa >= 2 && aa/4 < 2, aa, Integers] ==
  (aa == 2 || aa == 3 || aa == 4 || aa == 5 || aa == 6 || aa == 7)];
check["ideal_index_norm_algebra", na nb^2 == (na ni^2) (nb/ni)^2];
check["quadratic_trace_norm_algebra",
  ((cc + hh Sqrt[dd])/2) ((cc - hh Sqrt[dd])/2) == (cc^2 - dd hh^2)/4];
(* Independent exact Voronoi computation. The constraints from +/-e_i
   enclose the cell in a parallelogram on which q <= boundRadius.
   Cauchy-Schwarz excludes any further constraint q(v)>4*boundRadius.
   For 2x2 positive definite g, lambda_min(g) >= det(g)/tr(g), so the
   integer-vector search below includes every vector that can matter. *)
certifiedVoronoi[g_] := Module[
  {corners, boundRadius, coordinateBound, vectors, rows, bounds, candidates, vertex, ids, vertices},
  corners = LinearSolve[g, # Diagonal[g]/2] & /@ Tuples[{-1, 1}, 2];
  boundRadius = Max[(# . g . #) & /@ corners];
  coordinateBound = Ceiling[Sqrt[4 boundRadius Tr[g]/Det[g]]];
  vectors = Select[Tuples[Range[-coordinateBound, coordinateBound], 2],
    0 < # . g . # <= 4 boundRadius &];
  rows = (# . g) & /@ vectors;
  bounds = (# . g . #/2) & /@ vectors;
  candidates = Reap[
    Do[
      If[Det[rows[[ids]]] != 0,
        vertex = LinearSolve[rows[[ids]], bounds[[ids]]];
        If[And @@ Thread[rows . vertex <= bounds], Sow[vertex]]
      ],
      {ids, Subsets[Range[Length[vectors]], {2}]}
    ]
  ][[2]];
  vertices = DeleteDuplicates[First[candidates]];
  <|"gram" -> g, "constraint_norm_bound" -> 4 boundRadius,
    "coordinate_bound" -> coordinateBound, "constraint_count" -> Length[vectors],
    "vertices" -> vertices,
    "maximum" -> Max[(# . g . #) & /@ vertices]|>
];

(* Exhaustive reduced integral Gram matrices under the proven A <= 7 bound. *)
gramTriples = Reap[Do[
  If[a0 c0 (a0+c0-2 b0) < 8 (a0 c0-b0^2), Sow[{a0,b0,c0}]],
  {a0,2,7}, {c0,2,a0}, {b0,0,Floor[c0/2]}]][[2,1]];
check["exactly_22_reduced_Gram_triples", Length[gramTriples] == 22];
check["published_22_reduced_Gram_triples",
  Sort[canonicalGram /@ gramTriples] ==
    Sort[publicInput["reduced_gram_triples"]]];
check["maximum_determinant_is_21", Max[Det[gram[#]] & /@ gramTriples] == 21];
gramCertificates = Association @ Table[With[{t = gramTriples[[i]]},
  Print["Independent Voronoi computation ", i, "/22: ", t];
  ToString[i] -> certifiedVoronoi[gram[t]]], {i,Length[gramTriples]}];
Do[With[{data = gramCertificates[ToString[i]], t = gramTriples[[i]]},
  check["Gram_" <> ToString[i] <> "_exact_Voronoi", data["maximum"] == rho[t]];
  check["Gram_" <> ToString[i] <> "_rational_deep_holes", MatrixQ[data["vertices"],
    (IntegerQ[#] || Head[#] === Rational) &]];
], {i,Length[gramTriples]}];

fieldRows = Reap[Do[With[{delta = fundamentalDiscriminant[d], det = Det[gram[t]]},
  If[squareFreeIntegerQ[d] && Mod[det,delta] == 0 &&
     (Mod[d,4] == 1 || And @@ (EvenQ /@ t)),
    Sow[{d,t,det/delta,rho[t]}]]],
  {t,gramTriples}, {d,2,Det[gram[t]]}]][[2,1]];
fieldRows = SortBy[fieldRows, {#[[1]],#[[3]],#[[2]]} &];
check["published_nine_field_Gram_candidates",
  Sort[(Join[{#[[1]]}, canonicalGram[#[[2]]], {#[[3]]}] & /@ fieldRows)] ==
    Sort[publicInput["field_gram_candidates"]]];
expectedRows = {
  {2,{4,0,2},1,3/2}, {3,{4,2,4},1,4/3},
  {5,{3,1,2},1,9/10}, {5,{5,0,2},2,7/4},
  {5,{4,1,4},3,8/5}, {5,{6,2,4},4,9/5},
  {13,{7,1,2},1,49/26}, {17,{6,1,3},1,63/34},
  {21,{5,2,5},1,25/14}
};
check["exactly_nine_field_Gram_candidates", fieldRows == expectedRows];
check["all_fundamental_discriminants_are_exhausted",
  DeleteDuplicates[fundamentalDiscriminant /@ fieldRows[[All,1]]] == {8,12,5,13,17,21}];
traceNormSolutions[row_] := Module[
  {d = row[[1]], c0 = row[[2,3]], n0 = row[[3]], delta, hmax, kmax},
  delta = fundamentalDiscriminant[d];
  hmax = Floor[Sqrt[c0^2/delta]]; kmax = Floor[Sqrt[c0^2/(4 n0)]];
  Select[Tuples[{Range[-hmax,hmax], Range[1,kmax]}],
    Mod[c0-delta #[[1]],2] == 0 && c0^2-delta #[[1]]^2 == 4 n0 #[[2]]^2 &]
];
solutions = traceNormSolutions /@ fieldRows;
expectedSolutions = {{{0,1}}, {{-1,1},{0,2},{1,1}}, {{0,1}}, {}, {},
  {{0,1}}, {{0,1}}, {}, {{-1,1},{1,1}}};
Do[check["candidate_" <> ToString[i] <> "_all_trace_norm_index_solutions",
  solutions[[i]] == expectedSolutions[[i]]], {i,Length[fieldRows]}];
possibleCoefficients = MapThread[Function[{row, sol},
  FullSimplify[(row[[2,3]]+#[[1]] Sqrt[fundamentalDiscriminant[row[[1]]]])/2] & /@ sol],
  {fieldRows,solutions}];
expectedCoefficients = {{1},{2-Sqrt[3],2,2+Sqrt[3]},{1},{},{},{2},{1},{},
  {(5-Sqrt[21])/2,(5+Sqrt[21])/2}};
check["all_possible_b2_values", possibleCoefficients == expectedCoefficients];
check["three_empty_rows_are_excluded", Flatten[Position[solutions,{},1]] == {4,5,8}];
survivingRows = Pick[fieldRows, (Length[#] > 0 & /@ solutions), True];
check["six_Gram_candidates_survive", Length[survivingRows] == 6];
check["all_survivors_except_m3_have_index_one",
  And @@ Flatten[MapThread[Function[{row,sol},
    If[row[[1]] == 3, {True}, (#[[2]] == 1 & /@ sol)]], {fieldRows,solutions}]]];
check["m3_both_values_two_force_cross_term_plus_or_minus_two",
  Reduce[tt^2 == 4,tt,Reals] == (tt == -2 || tt == 2)];
check["m3_forced_cross_traces_contradict_B_2",
  (fieldTrace[3,#] & /@ {-2,2}) == {-4,4} &&
  FreeQ[fieldTrace[3,#] & /@ {-2,2},2]];
check["m3_other_b_values_have_norm_one", fieldNorm[3,2-Sqrt[3]] == 1 &&
  fieldNorm[3,2+Sqrt[3]] == 1];
Do[With[{b = If[d == 3,2+Sqrt[3],(5+Sqrt[21])/2]},
  check["m" <> ToString[d] <> "_conjugate_coefficients_are_unit_square_equivalent",
    fieldNorm[d,b] == 1 && conjugate[d,b] == b conjugate[d,b]^2]],
  {d,{3,21}}];

(* Construct the six F-isometry representatives, independently of enumeration. *)
representatives = {
  {2,1,{Sqrt[2],1},{4,0,2},3/2},
  {3,2+Sqrt[3],{1,Sqrt[3]-1},{4,2,4},4/3},
  {5,1,{omega[5],1},{3,1,2},9/10},
  {5,2,{omega[5],1},{6,2,4},9/5},
  {13,1,{omega[13],1},{7,1,2},49/26},
  {21,(5+Sqrt[21])/2,{3-omega[21],1},{5,2,5},25/14}
};
check["published_six_representative_Gram_and_radius_records",
  Sort[({#[[1]], canonicalGram[#[[4]]], ToString[#[[5]], InputForm]} & /@
      representatives)] ==
    Sort[({#["m"], canonicalGram[#["gram"]], #["radius"]} & /@
      publicInput["representatives"])]];
Do[Module[{d = row[[1]], a0 = row[[2]], beta = row[[3]], u, g, tag},
  tag = "representative_" <> ToString[i];
  u = Transpose[Table[With[{q0 = FullSimplify[(x-conjugate[d,x])/(omega[d]-conjugate[d,omega[d]])]},
    {FullSimplify[x-q0 omega[d]],q0}], {x,beta}]];
  g = Table[fieldTrace[d,a0 x y], {x,beta}, {y,beta}];
  check[tag <> "_unimodular_integral_basis", MatrixQ[u,IntegerQ] && Abs[Det[u]] == 1];
  check[tag <> "_positive_integral_coefficient", a0 > 0 && conjugate[d,a0] > 0 &&
    IntegerQ[fieldTrace[d,a0]] && IntegerQ[fieldNorm[d,a0]]];
  check[tag <> "_trace_Gram", g == gram[row[[4]]]];
  check[tag <> "_determinant_identity", Det[g] == fundamentalDiscriminant[d] fieldNorm[d,a0]];
  check[tag <> "_exact_covering_radius", rho[row[[4]]] == row[[5]]];
  check[tag <> "_strict_threshold", row[[5]] < 2];
], {i,Length[representatives]}, {row,{representatives[[i]]}}];
check["constructed_Gram_matrices_are_exactly_the_six_survivors",
  ({#[[1]],#[[4]],fieldNorm[#[[1]],#[[2]]],#[[5]]} & /@ representatives) == survivingRows];
check["m5_two_F_isometry_classes_are_distinct", fieldNorm[5,1] == 1 && fieldNorm[5,2] == 4];
check["Corollary_1_9_fields", Select[{2,3,5,13,21},
  If[Mod[#,4] == 1,(#+1)^2/(8 #),(#+1)/2] < 2 &] == {2,5,13}];
check["m3_twisted_and_standard_radii", rho[{4,2,4}] == 4/3 && rho[{6,0,2}] == 2];

jsonData = MapThread[Function[{row,sol,coeff},
  <|"m" -> row[[1]],"triple" -> row[[2]],"norm" -> row[[3]],
    "rho" -> ToString[row[[4]],InputForm],"h_k_solutions" -> sol,
    "possible_b2" -> (ToString[#,InputForm] & /@ coeff)|>],
  {fieldRows,solutions,possibleCoefficients}];
writeJSON["gram_candidates.json", <|"all_22_triples" -> gramTriples,
  "maximum_determinant" -> Max[Det[gram[#]] & /@ gramTriples],
  "nine_field_candidates" -> jsonData|>];
writeJSON["classification_table.json", Map[ToString[#,InputForm] &, representatives,{2}]];
writeJSON["voronoi_certificates.json", Map[Function[data,Map[ToString[#,InputForm] &,data]],gramCertificates]];
KeyValueMap[Print[If[TrueQ[#2],"PASS: ","FAIL: "],#1] &,checks];
allPassed = And @@ (TrueQ /@ Values[checks]);
writeJSON["section6_exact_checks.json", <|"Mathematica_version" -> $Version,"arithmetic" -> "Exact symbolic, integer and rational arithmetic.",
  "scope" -> "Clark-Jagy normalization and lower-bound algebra; exhaustive reduced Gram matrices under A<=7; fundamental discriminant and trace-parity filters; trace/norm/index solutions; six constructions; independent finite Voronoi certificates. Rational attainment and the general ideal-index identity are justified in the paper and source audit, not inferred from tests.",
  "provenance" -> provenance[], "check_records" -> checkRecords,
  "checks" -> checks,"all_passed" -> allPassed|>];
Print["SUMMARY: ",Count[Values[checks],True]," PASS / ",Count[Values[checks],Except[True]]," FAIL"];
If[!allPassed || Length[checks] != 115, fail["classification_checks"]];
<|"count" -> Length[checks], "all_passed" -> allPassed|>
];


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
  If[!StringMatchQ[text, RegularExpression["[0-9,\\[\\]\\s-]+"]],
    fail["voight_input_characters"]];
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
    fail["voight_input_hash"]
  ];
  rows = readRows[specification];
  If[Length[rows] != specification["rows"],
    fail["voight_row_count"]
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
  writeJSON["voight-rows-" <> ToString[specification["degree"]] <> ".json", checks];
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


RunVerification[dir_: Automatic] := Catch[Block[{$HistoryLength = 0},
  prepare[dir];
  publicInput = Import[inputFile, "RawJSON"];
  If[!AssociationQ[publicInput] || publicInput["schema_version"] =!= 3,
    fail["public_input_schema"]];
  Print["Mathematica: ", $Version];
  sectionFourResult = sectionFour[];
  classificationResult = classification[];
  runResult = <|"provenance" -> provenance[],
    "section4_checks" -> Length[sectionFourResult["checks"]],
    "grid_comparisons" -> 952, "upward_rounded_values" -> 87,
    "classification_checks" -> classificationResult["count"],
    "all_passed" -> (TrueQ[sectionFourResult["all_passed"]] &&
      TrueQ[classificationResult["all_passed"]])|>;
  writeJSON["verification_summary.json", runResult];
  runResult
], failureTag];

(* Optional archived-row integrity check. No completeness or uniqueness
   of the field lists is inferred from these finite computations. *)
RunVoightIntegrity[dir_: Automatic] := Catch[Block[{$HistoryLength = 0},
  prepare[dir];
  inputDirectory = FileNameJoin[{packageDirectory, "inputs", "voight"}];
  tableResults = checkTable /@ tableSpecifications;
  voightResult = <|"provenance" -> provenance[], "tables" -> tableResults,
    "total_rows" -> Total[Lookup[tableResults, "rows"]],
    "irreducible_pass" -> Total[Lookup[tableResults, "irreducible_pass"]],
    "totally_real_pass" -> Total[Lookup[tableResults, "totally_real_pass"]],
    "polynomial_discriminant_square_index_pass" ->
      Total[Lookup[tableResults, "polynomial_discriminant_square_index_pass"]],
    "field_discriminant_pass" ->
      Total[Lookup[tableResults, "field_discriminant_pass"]],
    "pass" -> And @@ Lookup[tableResults, "pass"]|>;
  writeJSON["voight_integrity.json", voightResult];
  If[!TrueQ[voightResult["pass"]], fail["voight_checks"]];
  Print["VOIGHT: ", voightResult["total_rows"], " rows verified."];
  voightResult
], failureTag];
End[];
EndPackage[];
