(* Checks corresponding to Lemma 3.1 and the real-quadratic-field calculation. *)

setVerificationContext["trace_geometry", "lem:gram-det", "exact symbolic identity"];
say["[trace_geometry] Checking trace Gram determinants."];
symbol["scaled-volume", Det[2 {{p, r}, {r, q}}] - 2^2 Det[{{p, r}, {r, q}}]];
symbol[
  "vertex-coordinates",
  Together[({q (p - r), p (q - r)}/(2 (p q - r^2))).{{p, r}, {r, q}} - {p, q}/2]
];
vertexNorm[p_, q_, r_] := p q (p + q - 2 r)/(4 (p q - r^2));
symbol[
  "vertex-norm",
  ({q (p - r), p (q - r)}/(2 (p q - r^2))).{{p, r}, {r, q}}.
    ({q (p - r), p (q - r)}/(2 (p q - r^2))) - vertexNorm[p, q, r]
];

Do[
  m = mm;
  om = If[Mod[m, 4] == 1, (1 + zz)/2, zz];
  conj[expr_] := expr /. zz -> -zz;
  reduceq[expr_] := PolynomialRemainder[Expand[expr], zz^2 - mm, zz];
  trq[expr_] := reduceq[expr + conj[expr]];
  bz = {{3, om/10}, {om/10, mm + 3}};
  ideals = {1/2, 3};
  bas = {1, om};
  indices = Tuples[{Range[2], Range[2]}];
  GG = Table[
    trq[ideals[[u[[1]]]] bas[[u[[2]]]] bz[[u[[1]], v[[1]]]] ideals[[v[[1]]]] bas[[v[[2]]]]],
    {u, indices}, {v, indices}
  ];
  discr = If[Mod[m, 4] == 1, m, 4 m];
  nvol = reduceq[(Times @@ ideals)^4 Det[bz] conj[Det[bz]]];
  check[
    "trace-det-m" <> ToString[m],
    "exact trace Gram",
    FullSimplify[Det[GG] - discr^2 nvol] === 0,
    Det[GG],
    discr^2 nvol
  ],
  {mm, {2, 3, 5, 6, 7, 13, 17, 29}}
];

setVerificationContext["trace_geometry", "prop:trace-euclidean-quadratic", "exact Voronoi calculation"];
say["[trace_geometry] Checking exact Voronoi vertices and radius formulae."];
Clear[m];
A = (m + 1)/2;
gram = {{2, 1}, {1, A}};
normals = {{1, 0}, {0, 1}, {-1, 1}, {-1, 0}, {0, -1}, {1, -1}};
verts = Table[
  LinearSolve[
    2 {normals[[j]].gram, normals[[Mod[j, 6] + 1]].gram},
    {normals[[j]].gram.normals[[j]], normals[[Mod[j, 6] + 1]].gram.normals[[Mod[j, 6] + 1]]}
  ],
  {j, 1, 6}
];
check[
  "hex-vertex-coordinates",
  "exact Voronoi",
  FullSimplify[verts[[1]] - {A/(2 m), (A - 1)/m}, m > 1] === {0, 0},
  verts[[1]],
  {A/(2 m), (A - 1)/m}
];
Do[
  check[
    "hex-radius-v" <> ToString[j],
    "exact Voronoi",
    FullSimplify[verts[[j]].gram.verts[[j]] - (m + 1)^2/(8 m), m > 1] === 0,
    FullSimplify[verts[[j]].gram.verts[[j]]],
    (m + 1)^2/(8 m)
  ];
  check[
    "hex-six-facets-v" <> ToString[j],
    "exact Voronoi",
    TrueQ[FullSimplify[And @@ Table[2 verts[[j]].gram.w <= w.gram.w, {w, normals}], m > 1]],
    "six inequalities",
    True
  ],
  {j, 1, 6}
];

setVerificationContext["trace_geometry", "thm:trace-euclidean-quadratic", "bounded exact enumeration and finite diagnostic"];
fieldLimit = input["enumeration"]["quadratic_field_m_max"];
Do[
  gr = If[Mod[mm, 4] == 1, gram /. m -> mm, {{2, 0}, {0, 2 mm}}];
  ws = If[Mod[mm, 4] == 1, normals, {{1, 0}, {0, 1}, {-1, 0}, {0, -1}}];
  candidates = DeleteDuplicates[Table[
    If[Det[pp] == 0, Nothing, LinearSolve[2 pp.gr, (#.gr.# & /@ pp)]],
    {pp, Subsets[ws, {2}]}
  ]];
  vv = Select[candidates, Function[v, And @@ Table[2 v.gr.w <= w.gr.w, {w, ws}]]];
  rho = Max[(#.gr.# & /@ vv)];
  expected = If[Mod[mm, 4] == 1, (mm + 1)^2/(8 mm), (mm + 1)/2];
  check[
    "field-m" <> ToString[mm],
    "finite field verification",
    rho === expected && Length[vv] === If[Mod[mm, 4] == 1, 6, 4],
    rho,
    expected
  ];
  smallVectors = DeleteCases[Tuples[Range[-3, 3], 2], {0, 0}];
  check[
    "field-extra-facets-m" <> ToString[mm],
    "finite diagnostic",
    And @@ Flatten[Table[2 v.gr.w <= w.gr.w, {v, vv}, {w, smallVectors}]],
    "48 extra lattice directions",
    True
  ];
  AppendTo[fieldRows, <|
    "m" -> mm,
    "rho_squared" -> fmt[rho],
    "vertices" -> Length[vv],
    "strict_trace_euclidean" -> (rho < 2)
  |>],
  {mm, Select[Range[2, fieldLimit], SquareFreeQ]}
];

check[
  "quadratic-classification",
  "exact classification",
  Select[Range[2, 13], SquareFreeQ[#] && If[Mod[#, 4] == 1, (#+1)^2/(8 #), (#+1)/2] < 2 &] === {2, 5, 13},
  {2, 5, 13},
  {2, 5, 13},
  "All m>13 are excluded by the symbolic radius formulas; m=3 has a separate exact obstruction."
];
check["integer-gap", "exact integer proof", Reduce[0 < u < 1, u, Integers] === False, "no integer strictly between 0 and 1", False];
check[
  "m3-obstruction",
  "exact integer proof",
  Resolve[ForAll[{u, v}, Implies[(u <= 0 || u >= 1) && (v <= 0 || v >= 1), 2 (1/2 - u)^2 + 6 (1/2 - v)^2 >= 2]], Reals],
  2 (1/2 - u)^2 + 6 (1/2 - v)^2,
  ">= 2 for integers u,v"
];
check[
  "m1mod4-upper13",
  "exact inequality",
  Resolve[ForAll[m, Implies[m >= 14, (m + 1)^2/(8 m) > 2]], Reals],
  "m >= 14",
  "rho_squared > 2"
];
symbol[
  "figure-m5-v1v2",
  (verts[[1]].{{1, 1}, {(1 + Sqrt[5])/2, (1 - Sqrt[5])/2}} /. m -> 5) - {1/2 + Sqrt[5]/5, 1/2 - Sqrt[5]/5}
];
