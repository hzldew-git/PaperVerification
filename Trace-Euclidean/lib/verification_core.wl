(* Shared verification framework and exact interval arithmetic. *)

started = AbsoluteTime[];
rows = {};
numbers = {};
tableRows = {};
certificates = {};
fieldRows = {};
transcript = {};
$verificationModule = "bootstrap";
$manuscriptAnchor = "package";
$evidenceClass = "integrity";

fmt[x_String] := x;
fmt[x_] := ToString[x, InputForm];

say[s_String] := (Print[s]; AppendTo[transcript, s]);

setVerificationContext[module_String, anchor_String, evidence_String] :=
  ($verificationModule = module; $manuscriptAnchor = anchor; $evidenceClass = evidence;);

record[id_, category_, status_, actual_, expected_, note_: ""] := Module[{r},
  r = <|
    "id" -> id,
    "module" -> $verificationModule,
    "anchor" -> $manuscriptAnchor,
    "evidence" -> $evidenceClass,
    "category" -> category,
    "status" -> status,
    "actual" -> fmt[actual],
    "expected" -> fmt[expected],
    "note" -> note
  |>;
  AppendTo[rows, r];
  If[status =!= "PASS", say[status <> " " <> id <> " : " <> fmt[actual] <> " ; " <> note]];
  status
];

check[id_, category_, test_, actual_, expected_, note_: ""] :=
  record[id, category, If[TrueQ[test], "PASS", "FAIL"], actual, expected, note];

warnCheck[id_, category_, test_, actual_, expected_, note_: ""] :=
  record[id, category, If[TrueQ[test], "PASS", "WARN"], actual, expected, note];

symbol[id_, expr_, assum_: True] := Module[{r = FullSimplify[expr, assum]},
  check[id, "exact algebra", And @@ (# === 0 & /@ Flatten[{r}]), r, "zero residual"]
];

num[id_, value_, claim_Association] := AppendTo[numbers, <|
  "id" -> id,
  "actual_key" -> claim["actual_key"],
  "value" -> fmt[N[value, 24]],
  "reported" -> claim["reported"],
  "digits" -> claim["digits"],
  "anchor" -> claim["anchor"],
  "source_line" -> claim["source_line"],
  "description" -> claim["description"]
|>];

decimal[s_String] := Module[{sign = 1, value = s, parts},
  If[StringStartsQ[value, "-"], sign = -1; value = StringDrop[value, 1]];
  parts = StringSplit[value, "."];
  sign If[Length[parts] == 1,
    ToExpression[parts[[1]]],
    ToExpression[parts[[1]]] + ToExpression[parts[[2]]]/10^StringLength[parts[[2]]]
  ]
];

(* Manuscript functions. *)
a = 1/6;
b = E^2/(2 Pi) - 1;
k[x_] := Log[2 Pi] - Log[x] - 1;
g[x_, y_] := x Log[2 Pi (y + b)] - Log[Pi (x y + 2 a)] + x y k[x];
gs[x_, y_] := g[x, y]/x;
gn[x_, y_] := y Log[2] + gs[x, y];
gt[n_, d_, t_] := (2 Pi (d + b))^n/(Pi (n d + 2 a)) (2 Pi t/(E n d))^(n d);

gx = D[g[x, y], x];
gy = D[g[x, y], y];
gxx = D[g[x, y], {x, 2}];
gyy = D[g[x, y], {y, 2}];
gxy = D[g[x, y], x, y];

root[expr_, var_, lo_, hi_] := var /. FindRoot[
  expr == 0,
  {var, N[lo, 80], N[hi, 80]},
  WorkingPrecision -> 80,
  AccuracyGoal -> 60,
  PrecisionGoal -> 60
];

(* Exact rational interval pairs {lower, upper}. *)
den = 10^40;
ir[v_List] := {Floor[v[[1]] den]/den, Ceiling[v[[2]] den]/den};
ip[v_] := {v, v};
ia[u_List, v_List] := ir[u + v];
ineg[u_List] := -Reverse[u];
is[u_List, v_List] := ia[u, ineg[v]];
im[u_List, v_List] := Module[{v4 = Flatten[Outer[Times, u, v]]}, ir[{Min[v4], Max[v4]}]];
idiv[u_List, v_List] := If[v[[1]] <= 0 <= v[[2]], Abort[], im[u, Reverse[1/v]]];
isc[c_, u_List] := im[ip[c], u];

atanBound[q_] := Module[{s, next},
  s = Sum[(-1)^j q^(2 j + 1)/(2 j + 1), {j, 0, 59}];
  next = q^121/121;
  {s, s + next}
];

piI = ir[is[isc[16, atanBound[1/5]], isc[4, atanBound[1/239]]]];
eI = ir[{
  Sum[1/j!, {j, 0, 100}],
  Sum[1/j!, {j, 0, 100}] + 1/(100 100!)
}];
bI = is[idiv[im[eI, eI], isc[2, piI]], ip[1]];

logUnit[r_] := Module[{u = (r - 1)/(r + 1), s, tail},
  s = 2 Sum[u^(2 j + 1)/(2 j + 1), {j, 0, 47}];
  tail = 2 u^97/(97 (1 - u^2));
  ir[{s, s + tail}]
];

log2I = logUnit[2];
logExact[q_] := logExact[q] = Module[{r = q, kk = 0},
  If[q <= 0, Abort[]];
  While[r < 1, r = 2 r; kk--];
  While[r > 2, r = r/2; kk++];
  ia[logUnit[r], isc[kk, log2I]]
];

il[u_List] := {logExact[u[[1]]][[1]], logExact[u[[2]]][[2]]};
kI[x_List] := is[is[il[isc[2, piI]], il[x]], ip[1]];
gI[x_List, y_List] := ia[
  is[im[x, il[im[isc[2, piI], ia[y, bI]]]], il[im[piI, ia[im[x, y], ip[1/3]]]]],
  im[im[x, y], kI[x]]
];
gsI[n_, d_] := idiv[gI[ip[n], ip[d]], ip[n]];
gnI[n_, d_] := ia[isc[d, log2I], gsI[n, d]];
gxI[x_List, y_List] := is[
  ia[is[il[im[isc[2, piI], ia[y, bI]]], idiv[y, ia[im[x, y], ip[1/3]]]], im[y, kI[x]]],
  y
];
gyI[x_List, y_List] := im[x, ia[
  is[idiv[ip[1], ia[y, bI]], idiv[ip[1], ia[im[x, y], ip[1/3]]]],
  kI[x]
]];
gnYI[x_List, y_List] := ia[log2I, idiv[gyI[x, y], x]];
fi[y_List] := is[is[il[im[isc[2, piI], ia[y, bI]]], y], idiv[y, ia[y, bI]]];
fYPrimeI[y_List] := ia[
  is[idiv[ip[1], ia[y, bI]], idiv[ip[1/3], im[ia[y, ip[1/3]], ia[y, ip[1/3]]]]],
  is[il[isc[2, piI]], ip[2]]
];
gxxI[x_List, y_List] := Module[{xy2a = ia[im[x, y], ip[1/3]]},
  is[idiv[im[y, y], im[xy2a, xy2a]], idiv[y, x]]
];
gyyI[x_List, y_List] := Module[{yb = ia[y, bI], xy2a = ia[im[x, y], ip[1/3]]},
  ia[ineg[idiv[x, im[yb, yb]]], idiv[im[x, x], im[xy2a, xy2a]]]
];
gxyI[x_List, y_List] := Module[{yb = ia[y, bI], xy2a = ia[im[x, y], ip[1/3]]},
  is[
    ia[is[idiv[ip[1], yb], idiv[ip[1/3], im[xy2a, xy2a]]], kI[x]],
    ip[1]
  ]
];
hessianI[x_List, y_List] := is[
  im[gxxI[x, y], gyyI[x, y]],
  im[gxyI[x, y], gxyI[x, y]]
];

signCert[id_, interval_, sign_, note_: ""] := Module[{ok},
  ok = If[sign == 1, interval[[1]] > 0, interval[[2]] < 0];
  AppendTo[certificates, <|
    "id" -> id,
    "module" -> $verificationModule,
    "anchor" -> $manuscriptAnchor,
    "lower" -> fmt[interval[[1]]],
    "upper" -> fmt[interval[[2]]],
    "decimal_lower" -> fmt[N[interval[[1]], 18]],
    "decimal_upper" -> fmt[N[interval[[2]], 18]],
    "sign" -> sign
  |>];
  check[id, "rational certificate", ok, N[interval, 16], If[sign == 1, "strictly positive", "strictly negative"], note]
];
