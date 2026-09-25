# Odlyzko `b = 4` archimedean certificate

This certificate concerns the two archimedean constants in Odlyzko's
unconditional Table 4 row used by v15. Its Lean implementation is
`TraceEuclidean/V15OdlyzkoExplicitFormulaReduction.lean` and
`TraceEuclidean/V15OdlyzkoNumerical.lean`.

## Convergence and interval decomposition

The sinh integrand has a removable singularity at zero: the numerator
`1 - F_{4}(x)` and denominator `2 sinh(x/2)` both vanish there, and the
derivative of the even kernel at zero is zero. Its tail decays exponentially;
Lean proves integrability on `(0, infinity)`.

For `0 <= x <= 1/100`, the explicit kernel formula and elementary sine and
cosine bounds imply

```text
H(t) >= 1 - pi^2 t^2 / 6,
(1 - F_4(x)) / (2 sinh(x/2)) <= x/2.
```

Thus the integral from zero to `1/100` is at most `1/40000`. Beyond the
support endpoint `x = 8`, Lean proves

```text
(1 - F_4(x)) / (2 sinh(x/2)) <= (1000/999) exp(-x/2),
(1 - F_4(x)) / (2 cosh(x/2)) <= exp(-x/2),
exp(-4) <= 18316/1000000.
```

The respective tail integrals are at most `(2000/999) exp(-4)` and
`2 exp(-4)`.

## Finite-interval checks

The source's elementary `H` formula is represented by a LeanCert expression.
Lean proves that its real evaluation equals the paper's kernel on the
integration intervals. The LeanCert dyadic interval checker then encloses
the finite integrals using outward-rounded arithmetic:

| Integral | Interval | Partition cells | Upper bound |
| --- | ---: | ---: | ---: |
| sinh term | `[1/100, 8]` | 131072 | `95551/100000` |
| cosh term | `[0, 8]` | 65536 | `750041/1000000` |

Both computations use dyadic precision `-100` and Taylor depth `20`.
Combining them with the endpoint estimates gives

```text
I_sinh <= 0.992204,
I_cosh <= 0.786673.
```

LeanCert's certified Euler–Mascheroni bound gives `gamma >= 0.5772151`.
Two additional strict dyadic checks verify

```text
16.593 < 8*pi*exp(0.5772151 - 0.992204),
36.347 < 8*pi*exp(pi/2 + 0.5772151 - 1.778877).
```

These imply the strict source-normalized `A = 36.347` and `B = 16.593`
logarithmic inequalities recorded by `V15OdlyzkoABIntegralCertificate`.

## Trust boundary

The interval calculations and the Euler–Mascheroni bound use LeanCert's
`native_decide`. Their Boolean checks are connected to the integral and
constant theorems by proved soundness theorems, but `native_decide` trusts
Lean's native compiler. The public axiom audit lists five generated
`_native.native_decide.ax_*` dependencies for the final certificate. This is a distinct trust
boundary from a proof reduced only by the Lean kernel. The vendored LeanCert
source and its Apache 2.0 license are in `lean/LeanCert`.

This certificate does not prove the Stark/Weil explicit formula or the
separate low-degree field-discriminant inputs. Analytic continuation,
completed-function growth, and direct zero-sum convergence are now supplied
by separate Lean modules. The remaining items stay explicit external
mathematical inputs to the v15 verification.
