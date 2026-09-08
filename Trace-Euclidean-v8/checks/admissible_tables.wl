(* Checks corresponding to the four tables listed in the manifest. *)

setVerificationContext["admissible_tables", "tab:admissible-classical", "certified finite enumeration"];
say["[admissible_tables] Certifying admissible pairs and excluded tails."];
classicalRange = input["enumeration"]["classical"];
integralRange = input["enumeration"]["integral"];
classicalPairs = {};
integralPairs = {};

Do[
  iv = gsI[n, d];
  check[
    "sign-classical-" <> ToString[n] <> "-" <> ToString[d],
    "finite enumeration",
    iv[[1]] iv[[2]] > 0,
    N[iv, 14],
    "certified interval excludes zero"
  ];
  If[iv[[1]] > 0, AppendTo[classicalPairs, {n, d}]],
  {n, classicalRange["rank_min"], classicalRange["rank_max"]},
  {d, classicalRange["degree_min"], classicalRange["degree_max"]}
];

setVerificationContext["admissible_tables", "tab:admissible-norm", "certified finite enumeration"];
Do[
  iv = gnI[n, d];
  check[
    "sign-integral-" <> ToString[n] <> "-" <> ToString[d],
    "finite enumeration",
    iv[[1]] iv[[2]] > 0,
    N[iv, 14],
    "certified interval excludes zero"
  ];
  If[iv[[1]] > 0, AppendTo[integralPairs, {n, d}]],
  {n, integralRange["rank_min"], integralRange["rank_max"]},
  {d, integralRange["degree_min"], integralRange["degree_max"]}
];

setVerificationContext["admissible_tables", "tab:admissible-classical", "certified rational interval plus manuscript monotonicity lemma"];
signCert["classic-rank-tail", gsI[13, 1], -1];
signCert["classic-degree-tail", gsI[3, 11], -1];
signCert["classic-degree-derivative", gyI[ip[3], ip[11]], -1];
signCert["classic-rank-y-derivative", gyI[ip[13], ip[1]], -1];

setVerificationContext["admissible_tables", "tab:admissible-norm", "certified rational interval plus manuscript monotonicity lemma"];
signCert["integral-rank-tail", gnI[30, 1], -1];
signCert["integral-degree-tail", gnI[5, 58], -1];
signCert["integral-degree-derivative", gnYI[ip[5], ip[58]], -1];
signCert["integral-rank-y-derivative", gnYI[ip[30], ip[1]], -1];

claimedPairs[kind_] := Sort[DeleteDuplicates[Flatten[
  Table[Tuples[{r["ranks"], r["degrees"]}], {r, Select[input["tables"], #["kind"] === kind &]}],
  1
]]];

setVerificationContext["admissible_tables", "tab:admissible-classical", "exact comparison with parsed manuscript table"];
check[
  "table-classical-pair-set",
  "table coverage",
  Sort[classicalPairs] === claimedPairs["classical"],
  Length[classicalPairs],
  Length[claimedPairs["classical"]]
];

setVerificationContext["admissible_tables", "tab:admissible-norm", "exact comparison with parsed manuscript table"];
check[
  "table-integral-pair-set",
  "table coverage",
  Sort[integralPairs] === claimedPairs["integral"],
  Length[integralPairs],
  Length[claimedPairs["integral"]]
];

Do[
  setVerificationContext["admissible_tables", r["label"], "manuscript table value checked from exact definitions"];
  pairs = Tuples[{r["ranks"], r["degrees"]}];
  kind = r["kind"];
  hfun = If[kind === "classical", gs, gn];
  hfunI = If[kind === "classical", gsI, gnI];
  vals = (hfun @@ #) & /@ pairs;
  hintervals = (hfunI @@ #) & /@ pairs;
  low = Min[N[vals, 60]];
  high = Max[N[vals, 60]];
  shown = decimal /@ r["displayed"];
  If[
    Length[shown] == 1,
    check[
      "table-h-rounding-" <> r["row_id"],
      "table approximation",
      Abs[low - shown[[1]]] < 1/2000,
      N[low, 16],
      shown[[1]],
      "Nearest rounding to three decimal places."
    ],
    check[
      "table-h-range-" <> r["row_id"],
      "table outward interval",
      shown[[1]] <= Min[hintervals[[All, 1]]] && Max[hintervals[[All, 2]]] <= shown[[2]],
      N[{Min[hintervals[[All, 1]]], Max[hintervals[[All, 2]]]}, 16],
      shown,
      "The printed lower endpoint is rounded down and the upper endpoint is rounded up."
    ]
  ];
  Do[
    nn = pair[[1]];
    dd = pair[[2]];
    hh = hfun[nn, dd];
    vv = gt[nn, dd, dd];
    AppendTo[tableRows, <|
      "table_id" -> r["table_id"],
      "row_id" -> r["row_id"],
      "label" -> r["label"],
      "kind" -> kind,
      "n" -> nn,
      "d" -> dd,
      "h" -> fmt[N[hh, 24]],
      "G" -> fmt[N[vv, 24]],
      "h_floor_3" -> fmt[Floor[N[1000 hh, 60]]/1000],
      "h_ceil_3" -> fmt[Ceiling[N[1000 hh, 60]]/1000],
      "source_line" -> r["source_line"]
    |>],
    {pair, pairs}
  ];
  If[
    StringContainsQ[r["bound"], "<1"],
    residuals = (gI[ip[#[[1]]], ip[#[[2]]]] & /@ pairs);
    check[
      "table-G-bound-" <> r["row_id"],
      "certified table upper bound",
      Max[residuals[[All, 2]]] < 0,
      N[Max[residuals[[All, 2]]], 16],
      "log(G) < 0, hence G < 1"
    ],
    bound = decimal[r["bound"]];
    digits = If[StringContainsQ[r["bound"], "."], StringLength[Last[StringSplit[r["bound"], "."]]], 0];
    residuals = (is[gI[ip[#[[1]]], ip[#[[2]]]], il[ip[bound]]] & /@ pairs);
    warnCheck[
      "table-G-bound-" <> r["row_id"],
      "certified table upper bound",
      Max[residuals[[All, 2]]] < 0,
      N[Max[(gt[#[[1]], #[[2]], #[[2]]] & /@ pairs)], 16],
      bound,
      "A WARN means that nearest rounding went downward, so the printed number is not certified as an outward upper bound by G alone."
    ];
    check[
      "table-G-tightness-" <> r["row_id"],
      "table display precision",
      bound - Max[N[(gt[#[[1]], #[[2]], #[[2]]] & /@ pairs), 60]] <= 1/10^digits,
      N[bound - Max[N[(gt[#[[1]], #[[2]], #[[2]]] & /@ pairs), 60]], 16],
      "at most one unit in the last printed place"
    ]
  ],
  {r, input["tables"]}
];

Do[
  pairs = If[r["kind"] === "classical", classicalPairs, integralPairs];
  setVerificationContext["admissible_tables", r["label"], "exact comparison with certified admissible-pair set"];
  check[
    "max-rank-" <> r["row_id"],
    "table maxima",
    And @@ Table[Max[First /@ Select[pairs, Last[#] == dd &]] == r["maxrank"], {dd, r["degrees"]}],
    r["maxrank"],
    "maximum rank with h(n,d)>0"
  ];
  check[
    "max-degree-" <> r["row_id"],
    "table maxima",
    And @@ Table[Max[Last /@ Select[pairs, First[#] == nn &]] == r["maxdegree"], {nn, r["ranks"]}],
    r["maxdegree"],
    "maximum degree with h(n,d)>0"
  ],
  {r, input["maxima"]}
];
