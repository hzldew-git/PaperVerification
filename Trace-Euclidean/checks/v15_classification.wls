(* Exact Theorem 1.7 calculations against the published v15 extracted input.
   The private maintainer build binds that input to the manuscript SHA-256.
   The index-to-ideal and general covering theorems are separate obligations. *)
packageRoot = ParentDirectory[DirectoryName[$InputFileName]];
publicInput = Import[FileNameJoin[{packageRoot, "inputs", "manuscript_inputs_v15.json"}],
  "RawJSON"];
If[!AssociationQ[publicInput] || publicInput["manuscript", "version"] =!= "v15",
  Print["Missing or invalid v15 extracted input."]; Exit[1]];
SetDirectory[FileNameJoin[{packageRoot, "results"}]];
Print["Mathematica: ", $Version];
sourceHash = publicInput["manuscript", "sha256"];
checks = <||>;
truth[x_] := TrueQ[FullSimplify[x]];
check[name_, statement_] := AssociateTo[checks, name -> truth[statement]];
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
Export["gram_candidates.json", <|"all_22_triples" -> gramTriples,
  "maximum_determinant" -> Max[Det[gram[#]] & /@ gramTriples],
  "nine_field_candidates" -> jsonData|>, "RawJSON"];
Export["classification_table.json", Map[ToString[#,InputForm] &, representatives,{2}], "RawJSON"];
Export["voronoi_certificates.json", Map[Function[data,Map[ToString[#,InputForm] &,data]],gramCertificates],"RawJSON"];
KeyValueMap[Print[If[TrueQ[#2],"PASS: ","FAIL: "],#1] &,checks];
allPassed = And @@ (TrueQ /@ Values[checks]);
Export["section6_exact_checks.json", <|"manuscript_version" -> "v15",
  "source_sha256" -> sourceHash,
  "Mathematica_version" -> $Version,"arithmetic" -> "Exact symbolic, integer and rational arithmetic.",
  "scope" -> "Clark-Jagy normalization and lower-bound algebra; exhaustive reduced Gram matrices under A<=7; fundamental discriminant and trace-parity filters; trace/norm/index solutions; six constructions; independent finite Voronoi certificates. Rational attainment and the general ideal-index identity are justified in the paper and source audit, not inferred from tests.",
  "checks" -> checks,"all_passed" -> allPassed|>,"RawJSON"];
Print["SUMMARY: ",Count[Values[checks],True]," PASS / ",Count[Values[checks],Except[True]]," FAIL"];
If[!allPassed,Exit[1]];
