(* Checks corresponding to Section 4 and the labels listed for analytic_bounds. *)

setVerificationContext["analytic_bounds", "eq:def-g", "exact symbolic identity"];
say["[analytic_bounds] Checking every computationally accessible step in Section 4."];
symbol[
  "section4-g-definition",
  g[nn, dd] - (nn Log[2 Pi (dd + b)] - Log[Pi (nn dd + 2 a)] + nn dd Log[2 Pi/(nn E)]),
  nn > 0 && dd > 0
];
symbol["section4-gs-definition", gs[x, y] - g[x, y]/x, x > 0 && y > 0];
symbol["section4-gn-definition", gn[x, y] - (y Log[2] + g[x, y]/x), x > 0 && y > 0];
symbol["gx", gx - (Log[2 Pi (y + b)] - y/(x y + 2 a) + y k[x] - y), x >= 1 && y >= 1];
symbol["gy", gy - (x/(y + b) - x/(x y + 2 a) + x k[x]), x >= 1 && y >= 1];
symbol["gxx", gxx - (y^2/(x y + 2 a)^2 - y/x)];
symbol["gyy", gyy - (-x/(y + b)^2 + x^2/(x y + 2 a)^2)];
symbol["gxy", gxy - (1/(y + b) - 2 a/(x y + 2 a)^2 + k[x] - 1), x >= 1];

setVerificationContext["analytic_bounds", "lem:fix-y", "exact symbolic identity and symbolic sign"];
fY[y_] := Log[2 Pi (y + b)] - y/(y + 2 a) + (Log[2 Pi] - 2) y;
hY[y_] := (y + 2 a)^3 - 4 a (y + b)^2;
symbol["gxx-factor", gxx + y ((x y)^2 + (4 a - 1) x y + 4 a^2)/(x (x y + 2 a)^2)];
symbol[
  "gxx-amgm-reduction",
  ((x y)^2 + (4 a - 1) x y + 4 a^2) - (8 a - 1) x y - (x y - 2 a)^2
];
check[
  "gxx-coefficient-positive",
  "exact inequality",
  8 a - 1 > 0,
  8 a - 1,
  "> 0"
];
check["gxx-negative", "symbolic sign", FullSimplify[gxx < 0, x >= 1 && y >= 1], gxx, "negative on x,y >= 1"];
symbol[
  "fix-y-f-definition",
  (gx /. x -> 1) - fY[y],
  y >= 1
];
symbol[
  "fix-y-f-prime",
  D[fY[y], y] - (1/(y + b) - 2 a/(y + 2 a)^2 + Log[2 Pi] - 2),
  y >= 1
];
symbol[
  "fix-y-f-second",
  D[fY[y], {y, 2}] - (-1/(y + b)^2 + 4 a/(y + 2 a)^3),
  y >= 1
];
symbol["fix-y-h-prime", D[hY[y], y] - (3 y^2 + 4 a y + 12 a^2 - 8 a b)];
symbol["fix-y-h-second", D[hY[y], {y, 2}] - (6 y + 4 a)];
check[
  "fix-y-h-second-positive",
  "symbolic sign",
  FullSimplify[D[hY[y], {y, 2}] > 0, y >= 1],
  D[hY[y], {y, 2}],
  "positive for y >= 1"
];
symbol["fix-y-constant-identity", 12 a^2 - 8 a b - (5 Pi - 2 E^2)/(3 Pi)];
symbol["fix-y-hprime-one-identity", (D[hY[y], y] /. y -> 1) - (16 Pi - 2 E^2)/(3 Pi)];
symbol["fix-y-h-one-identity", hY[1] - (64/27 - E^4/(6 Pi^2))];
symbol[
  "fix-y-fsecond-h-identity",
  D[fY[y], {y, 2}] + hY[y]/((y + 2 a)^3 (y + b)^2),
  y >= 1
];
symbol[
  "fix-y-fprime-one-identity",
  (D[fY[y], y] /. y -> 1) - (2 Pi/E^2 - 3/16 + Log[2 Pi] - 2)
];
symbol["fix-y-f-one-identity", fY[1] - (Log[2 Pi] - 3/4)];
check[
  "fix-y-f-limit",
  "symbolic limit",
  SameQ[Limit[fY[y], y -> Infinity], -Infinity],
  Limit[fY[y], y -> Infinity],
  "-Infinity"
];
symbol[
  "fix-y-gx-asymptotic",
  Limit[gx/(Log[x]), x -> Infinity, Assumptions -> y >= 1] + y,
  y >= 1
];

setVerificationContext["analytic_bounds", "lem:fix-x", "exact symbolic identity and symbolic sign"];
hX[x_, y_] := 1/(y + b) - 1/(x y + 2 a) + k[x];
fX[x_] := 1/(1 + b) - 1/(x + 2 a) + k[x];
symbol[
  "fix-x-h-definition",
  gy/x - hX[x, y],
  x >= 1 && y >= 1
];
symbol[
  "fix-x-h-y-derivative",
  D[hX[x, y], y] - (x (y + b)^2 - (x y + 2 a)^2)/((y + b)^2 (x y + 2 a)^2),
  x >= 1 && y >= 1
];
check[
  "fix-x-h-y-negative",
  "symbolic sign",
  FullSimplify[x (y + bb)^2 - (x y + 2 a)^2 < 0, x >= 1 && y >= 1 && 0 < bb < 2 a],
  x (y + bb)^2 - (x y + 2 a)^2,
  "negative for x,y >= 1 and 0 < b < 2a"
];
yCritical[z_] := (b z - 2 a)/(z^2 - z);
symbol["fix-x-critical-root", z^2 (yCritical[z] + b)^2 - (z^2 yCritical[z] + 2 a)^2, z > 1];
symbol[
  "fix-x-critical-condition",
  yCritical[z] - 1 + (z^2 - (b + 1) z + 2 a)/(z (z - 1)),
  z > 1
];
symbol["fix-x-q-prime", D[z^2 - (b + 1) z + 2 a, z] - (2 z - b - 1)];
check[
  "fix-x-quadratic-positive-after-one",
  "symbolic sign",
  FullSimplify[z^2 - (bb + 1) z + 2 a > 0, z >= 1 && 0 < bb < 1/4],
  z^2 - (bb + 1) z + 2 a,
  "positive for z >= 1 and 0 < b < 1/4"
];
symbol["fix-x-k-threshold", k[2 Pi/E]];
symbol["fix-x-k-prime", D[k[x], x] + 1/x, x > 0];
check[
  "fix-x-reciprocal-positive",
  "symbolic sign",
  FullSimplify[1/(y + bb) - 1/(y + 2 a) > 0, y >= 1 && 0 < bb < 2 a],
  1/(y + bb) - 1/(y + 2 a),
  "positive for y >= 1 and 0 < b < 2a"
];
symbol["fix-x-f-definition", hX[x, 1] - fX[x], x >= 1];
symbol["fix-x-f-prime", D[fX[x], x] - (1/(x + 2 a)^2 - 1/x), x >= 1];
check[
  "fix-x-f-prime-negative",
  "symbolic sign",
  FullSimplify[1/(x + 2 a)^2 - 1/x < 0, x >= 1],
  1/(x + 2 a)^2 - 1/x,
  "negative for x >= 1"
];
symbol[
  "fix-x-h-y-limit",
  Limit[hX[x, y], y -> Infinity, Assumptions -> x >= 1] - k[x],
  x >= 1
];
check[
  "fix-x-f-limit",
  "symbolic limit",
  SameQ[Limit[fX[x], x -> Infinity], -Infinity],
  Limit[fX[x], x -> Infinity],
  "-Infinity"
];

setVerificationContext["analytic_bounds", "lem:max-g", "exact symbolic identity and asymptotic calculation"];
fStationary[y_] := Log[2 Pi (y + b)] - y - y/(y + b);
symbol[
  "stationary-elimination",
  gx - y gy/x - fStationary[y],
  x > 0 && y > 0
];
symbol[
  "stationary-f-prime",
  D[fStationary[y], y] + (y^2 + (2 b - 1) y + b^2)/(y + b)^2,
  y > 0
];
check[
  "stationary-polynomial-positive",
  "symbolic sign",
  FullSimplify[y^2 + (2 bb - 1) y + bb^2 > 0, y >= 1 && 0 < bb < 1/4],
  y^2 + (2 bb - 1) y + bb^2,
  "positive for y >= 1 and 0 < b < 1/4"
];
symbol["stationary-f-one-identity", fStationary[1] - (1 - 2 Pi/E^2)];
check[
  "stationary-f-limit",
  "symbolic limit",
  SameQ[Limit[fStationary[y], y -> Infinity], -Infinity],
  Limit[fStationary[y], y -> Infinity],
  "-Infinity"
];
symbol[
  "max-g-boundary-x3-equation",
  (gy /. x -> 3)/3 - (1/(y + b) - 1/(3 y + 2 a) + Log[2 Pi] - Log[3] - 1),
  y >= 1
];
symbol[
  "max-g-boundary-y1-equation",
  (gx /. y -> 1) + Log[x] + 3/(3 x + 1) - Log[2 Pi],
  x >= 3
];
symbol[
  "max-g-x-asymptotic",
  Limit[g[x, y]/(x Log[x]), x -> Infinity, Assumptions -> y >= 1] + y,
  y >= 1
];
symbol[
  "max-g-y-asymptotic",
  Limit[g[x, y]/y, y -> Infinity, Assumptions -> x >= 3] - x k[x],
  x >= 3
];

setVerificationContext["analytic_bounds", "lem:gs-fix-y", "exact symbolic identity and symbolic sign"];
fS[z_] := Log[Pi z] - z + 1/(3 z) - 2/3;
symbol["gs-x-derivative", D[gs[x, y], x] - (x gx - g[x, y])/x^2, x >= 1 && y >= 1];
symbol[
  "gs-derivative-numerator",
  x gx - g[x, y] - fS[x y + 2 a],
  x >= 1 && y >= 1
];
symbol["gs-f-prime", D[fS[z], z] + (3 z^2 - 3 z + 1)/(3 z^2), z > 0];
check[
  "gs-z-lower-bound",
  "exact inequality",
  FullSimplify[x y + 2 a >= 4/3, x >= 1 && y >= 1],
  x y + 2 a,
  ">= 4/3"
];
check[
  "gs-monotonicity-polynomial",
  "symbolic sign",
  Resolve[ForAll[z, 3 z^2 - 3 z + 1 > 0], Reals],
  3 z^2 - 3 z + 1,
  "> 0 for every real z"
];

setVerificationContext["analytic_bounds", "lem:gs-fix-x", "exact symbolic identity"];
symbol["gs-y-derivative", D[gs[x, y], y] - gy/x, x > 0 && y >= 1];

setVerificationContext["analytic_bounds", "lem:gn-fix-y", "exact symbolic identity"];
symbol["gn-x-derivative", D[gn[x, y], x] - D[gs[x, y], x], x > 0 && y >= 1];

setVerificationContext["analytic_bounds", "lem:gn-fix-x", "exact symbolic identity and symbolic sign"];
fN[x_] := Log[2] + 1/(1 + b) - 1/(x + 2 a) + k[x];
symbol["gn-y-derivative", D[gn[x, y], y] - (Log[2] + gy/x), x > 0 && y >= 1];
symbol["gn-y-second", D[gn[x, y], {y, 2}] - D[hX[x, y], y], x >= 1 && y >= 1];
symbol[
  "gn-y-limit",
  Limit[D[gn[x, y], y], y -> Infinity, Assumptions -> x >= 1] - Log[4 Pi/(x E)],
  x >= 1
];
symbol[
  "gn-f-definition",
  (D[gn[x, y], y] /. y -> 1) - fN[x],
  x >= 1
];
symbol["gn-f-prime", D[fN[x], x] - (1/(x + 2 a)^2 - 1/x), x >= 1];
check[
  "gn-f-prime-negative",
  "symbolic sign",
  FullSimplify[D[fN[x], x] < 0, x >= 1],
  D[fN[x], x],
  "negative for x >= 1"
];
check[
  "gn-f-denominator-inequality",
  "exact inequality",
  FullSimplify[(x + 2 a)^2 > x, x >= 1],
  (x + 2 a)^2 - x,
  "> 0 for x >= 1"
];
check[
  "gn-f-limit",
  "symbolic limit",
  SameQ[Limit[fN[x], x -> Infinity], -Infinity],
  Limit[fN[x], x -> Infinity],
  "-Infinity"
];

setVerificationContext["analytic_bounds", "eq:def-g", "exact symbolic identity"];
symbol[
  "gamma-ratio-simplification",
  (dd^(2 nn dd) E^(-2 nn dd) (2 Pi (dd + b))^nn)/
    ((nn dd/2)^(nn dd) E^(-nn dd) 2 Pi (nn dd/2 + a)) *
    (Pi tt)^(nn dd)/dd^(2 nn dd) - gt[nn, dd, tt],
  Element[{nn, dd}, Integers] && nn > 0 && dd > 0 && tt > 0
];

say["[analytic_bounds] Constructing 40-place outward rational certificates."];
e2Interval = im[eI, eI];
e4Interval = im[e2Interval, e2Interval];
pi2Interval = im[piI, piI];
twoPiOverEInterval = idiv[isc[2, piI], eI];
fourPiOverEInterval = isc[2, twoPiOverEInterval];

setVerificationContext["analytic_bounds", "eq:def-g", "certified rational interval"];
signCert["b-positive", bI, 1];
signCert["b-less-than-2a", is[bI, ip[1/3]], -1];
signCert["b-less-than-one-quarter", is[bI, ip[1/4]], -1];

setVerificationContext["analytic_bounds", "lem:fix-y", "certified rational interval"];
signCert["fix-y-constant-positive", is[isc[5, piI], isc[2, e2Interval]], 1];
signCert[
  "fix-y-hprime-one-positive",
  idiv[is[isc[16, piI], isc[2, e2Interval]], isc[3, piI]],
  1
];
signCert[
  "fix-y-h-one-positive",
  is[ip[64/27], idiv[e4Interval, isc[6, pi2Interval]]],
  1
];
signCert[
  "fix-y-fprime-one-positive",
  ia[
    is[idiv[isc[2, piI], e2Interval], ip[3/16]],
    is[il[isc[2, piI]], ip[2]]
  ],
  1
];
signCert["fix-y-f-one-positive", is[il[isc[2, piI]], ip[3/4]], 1];
signCert["fix-y-fprime-tail-negative", is[il[isc[2, piI]], ip[2]], -1];

setVerificationContext["analytic_bounds", "lem:fix-x", "certified rational interval"];
signCert["fix-x-q-one-positive", is[ip[1/3], bI], 1];
signCert["fix-x-two-pi-over-e-above-one", is[twoPiOverEInterval, ip[1]], 1];
signCert[
  "fix-x-reciprocal-at-one-positive",
  is[idiv[ip[1], ia[ip[1], bI]], idiv[ip[1], ip[4/3]]],
  1,
  "This certifies 1/(1+b)-1/(1+2a)>0."
];
signCert[
  "fix-x-threshold-positive",
  is[
    idiv[ip[1], ia[ip[1], bI]],
    idiv[ip[1], ia[twoPiOverEInterval, ip[1/3]]]
  ],
  1,
  "This is f(2 Pi/e)>0."
];

setVerificationContext["analytic_bounds", "lem:max-g", "certified rational interval"];
signCert["stationary-f-one-positive", is[ip[1], idiv[isc[2, piI], e2Interval]], 1];
signCert["max-g-k-at-three-negative", kI[ip[3]], -1];
stationaryYBox = {141015/100000, 141016/100000};
stationaryXBox = {361110/100000, 361114/100000};
signCert["stationary-x-left", gyI[ip[stationaryXBox[[1]]], stationaryYBox], 1];
signCert["stationary-x-right", gyI[ip[stationaryXBox[[2]]], stationaryYBox], -1];
signCert[
  "stationary-hessian-negative",
  hessianI[stationaryXBox, stationaryYBox],
  -1,
  "The Hessian determinant is negative throughout a rational box containing the stationary point."
];

setVerificationContext["analytic_bounds", "lem:gs-fix-y", "certified rational interval"];
signCert["gs-f-at-4/3-negative", is[il[isc[4/3, piI]], ip[7/4]], -1];

setVerificationContext["analytic_bounds", "lem:max-gs", "certified rational interval"];
signCert["gs-threshold-order", is[ip[4374/1000], twoPiOverEInterval], 1];
signCert["gs-two-pi-below-three", is[ip[3], twoPiOverEInterval], 1];
signCert["gs-three-below-x0", gyI[ip[3], ip[1]], 1];

setVerificationContext["analytic_bounds", "lem:gn-fix-x", "certified rational interval"];
signCert[
  "gn-threshold-positive",
  is[
    idiv[ip[1], ia[ip[1], bI]],
    idiv[ip[1], ia[fourPiOverEInterval, ip[1/3]]]
  ],
  1,
  "This is f_n(4 Pi/e)>0."
];

setVerificationContext["analytic_bounds", "lem:max-gn", "certified rational interval"];
signCert["gn-four-pi-below-five", is[ip[5], fourPiOverEInterval], 1];
check["gn-five-below-xn", "exact inequality", 5 < 9802/1000, 9802/1000 - 5, "> 0"];

brackets = {
  {"lem:fix-y", "y0", Function[v, gxI[ip[1], ip[v]]], 25193/1000, 25194/1000},
  {"lem:fix-y", "y1", Function[v, fYPrimeI[ip[v]]], 565/100, 566/100},
  {"lem:fix-x", "x0", Function[v, gyI[ip[v], ip[1]]], 4374/1000, 4376/1000},
  {"lem:max-g", "x-boundary", Function[v, gxI[ip[v], ip[1]]], 5252/1000, 5254/1000},
  {"lem:max-g", "y-at-rank3", Function[v, gyI[ip[3], ip[v]]], 2346/1000, 2348/1000},
  {"lem:max-g", "stationary-y", Function[v, fi[ip[v]]], stationaryYBox[[1]], stationaryYBox[[2]]},
  {"lem:gn-fix-x", "xn", Function[v, gnYI[ip[v], ip[1]]], 9802/1000, 9804/1000},
  {"lem:max-gn", "yn-at-rank5", Function[v, gnYI[ip[5], ip[v]]], 9998/1000, 10000/1000}
};
Do[
  setVerificationContext["analytic_bounds", item[[1]], "certified rational root bracket"];
  signCert[item[[2]] <> "-left", item[[3]][item[[4]]], 1];
  signCert[item[[2]] <> "-right", item[[3]][item[[5]]], -1],
  {item, brackets}
];

yy0 = root[gx /. x -> 1, y, 25, 26];
xx0 = root[gy /. y -> 1, x, 4, 5];
xb = root[gx /. y -> 1, x, 5, 6];
yb = root[gy /. x -> 3, y, 2, 3];
yst = root[Log[2 Pi (y + b)] - y - y/(y + b), y, 1, 2];
xst = root[gy /. y -> yst, x, 3, 4];
xn = root[D[gn[x, y], y] /. y -> 1, x, 9, 10];
yn = root[D[gn[x, y], y] /. x -> 5, y, 9, 11];
yprime = root[D[gx /. x -> 1, y], y, 5, 6];
zRoots = Sort[z /. Solve[z^2 - (b + 1) z + 2 a == 0, z]];
stationaryYRoots = Sort[y /. Solve[y^2 + (2 b - 1) y + b^2 == 0, y]];

numericActuals = <|
  "b" -> b,
  "y0" -> yy0,
  "y1" -> yprime,
  "x0" -> xx0,
  "z_minus" -> zRoots[[1]],
  "z_plus" -> zRoots[[2]],
  "g_max" -> g[xb, 1],
  "x_boundary" -> xb,
  "stationary_y_small" -> stationaryYRoots[[1]],
  "stationary_y_large" -> stationaryYRoots[[2]],
  "stationary_y" -> yst,
  "stationary_x" -> xst,
  "stationary_gxx" -> (gxx /. {x -> xst, y -> yst}),
  "stationary_gyy" -> (gyy /. {x -> xst, y -> yst}),
  "stationary_gxy" -> (gxy /. {x -> xst, y -> yst}),
  "stationary_hessian" -> (gxx gyy - gxy^2 /. {x -> xst, y -> yst}),
  "y_rank3" -> yb,
  "g_rank3_max" -> g[3, yb],
  "gs_max" -> gs[3, yb],
  "two_pi_over_e" -> 2 Pi/E,
  "xn" -> xn,
  "gn_max" -> gn[5, yn],
  "yn_rank5" -> yn,
  "four_pi_over_e" -> 4 Pi/E
|>;

Do[
  setVerificationContext["analytic_bounds", claim["anchor"], "high-precision approximation checked against manuscript rounding"];
  actual = Lookup[numericActuals, claim["actual_key"], Missing["UnknownActualKey"]];
  reported = decimal[claim["reported"]];
  tolerance = 1/(2 10^claim["digits"]);
  warnCheck[
    "numeric-" <> claim["id"],
    "manuscript approximation",
    actual =!= Missing["UnknownActualKey"] && Abs[N[actual, 70] - reported] < tolerance,
    N[actual, 18],
    claim["reported"],
    "Nearest rounding to the number of digits printed in the manuscript."
  ];
  num[claim["id"], actual, claim],
  {claim, input["numeric_claims"]}
];

setVerificationContext["analytic_bounds", "lem:max-g", "certified rational interval"];
leftMax = gI[ip[3], {2346/1000, 2348/1000}];
rightAt = gI[ip[5253/1000], ip[1]];
signCert["boundary-comparison", is[rightAt, leftMax], 1, "g(5.253,1) exceeds every g(3,y) in the certified root bracket."];
signCert["boundary-left-below-3.325", is[leftMax, ip[3325/1000]], -1];
signCert["boundary-right-above-3.328", is[rightAt, ip[3328/1000]], 1];
symbol[
  "stationary-hessian-reduction",
  (gxx gyy - gxy^2) - (-gxy D[Log[2 Pi (y + b)] - y - y/(y + b), y] - gy gxy/x - gy gyy y/x^2),
  x > 0 && y > 0
];
