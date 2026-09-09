(* Finite diagnostics for the Gamma inequalities cited in Section 3. *)

setVerificationContext["gamma_diagnostics", "eq:gamma-lower", "finite high-precision diagnostic"];
say["[gamma_diagnostics] Running finite Gamma-function diagnostics."];
Do[
  v = N[LogGamma[z + 1] - ((Log[2 Pi (z + a)])/2 + z (Log[z] - 1)), 70];
  check["gamma-lower-" <> fmt[z], "Gamma finite sample", v > 0, N[v, 18], ">0"],
  {z, Join[{1/2}, Range[1, 40]]}
];

setVerificationContext["gamma_diagnostics", "eq:gamma-upper", "finite high-precision diagnostic"];
Do[
  v = N[(Log[2 Pi (z + b)])/2 + z (Log[z] - 1) - LogGamma[z + 1], 70];
  check[
    "gamma-upper-" <> fmt[z],
    "Gamma finite sample",
    If[z == 1, Abs[v] < 10^-60, v > 0],
    N[v, 18],
    If[z == 1, "0", ">0"]
  ],
  {z, Range[1, 40]}
];
