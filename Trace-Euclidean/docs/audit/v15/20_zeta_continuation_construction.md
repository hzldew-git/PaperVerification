# Dedekind zeta continuation constructed in Lean

The formalization now constructs, for every number field `K`, an entire
function agreeing with `(s - 1) * NumberField.dedekindZeta K s` whenever
`1 < Re(s)`. It is the concrete value
`TraceEuclidean.v15ConstructedDedekindZetaRegularization K`, rather than an
assumed instance of the zero-theory structure.

## Source and normalization

The number-field theta, Poisson, cone-integral, and ideal-class modules were
adapted from `mathlib-initiative/sum_product` at commit
`80e4127a67742659d521466204c6d2d7e0ca2b3f`. The source is Apache 2.0;
its license and the local adaptation note are in `lean/THIRD_PARTY_LICENSES`
and `lean/DedekindZeta/README.md`. The upstream abstract Mellin module had
already been vendored as `TraceEuclidean.AnalyticMellinPrinciple`. The local
proof adaptations make the number-field files compile with Lean 4.32.1 and
the repository's pinned mathlib.

The new `DedekindZeta.GlobalContinuation` module sums the Mellin
continuations of the partial zeta integrals over the finite ideal class
group. It proves the exact right-half-plane equality

```text
completedZetaContinuation K s = ZInfty K s * dedekindZeta K s
```

for `1 < Re(s)`. It then removes the possible poles at `0` and `1` by a
polynomial expression. `completedZetaPoleRemoved_analyticOn` proves this
expression entire, and `completedZetaPoleRemoved_eq_zeta` proves that it is
`s * (s - 1) * ZInfty K s * dedekindZeta K s` on the same half-plane.

The new `DedekindZeta.ZetaRegularization` module constructs an **entire**
reciprocal of `s * ZInfty K s`. It cancels the apparent pole at `s = 0` using
the shifted real Gamma relation and one of the field's infinite places.
`dedekindZetaRegularized_analyticOn` and
`dedekindZetaRegularized_eq` prove that the resulting product is entire and
equals `(s - 1) * dedekindZeta K s` for `1 < Re(s)`. The exact definitions and
right-half-plane identities are checked by Lean, including the discriminant
and both real and complex Gamma factors.

`TraceEuclidean.V15DedekindZetaConstructed` instantiates the existing
`V15DedekindZetaRegularization` structure. Its Table 4 endpoint
`v15_odlyzkoTable4_of_constructed_circle_growth` no longer assumes that the
regularization exists. It still states the circle-growth estimate, the
source explicit formula, and the already certified archimedean bounds as
explicit premises.

## Trust and remaining work

The local full Lean build and `MainTheoremAudit` pass. The new construction,
right-half-plane equality, and Table 4 endpoint depend only on `propext`,
`Classical.choice`, and `Quot.sound`. There is no `sorry`, project axiom, or
`native_decide` in these new proofs. The separate numerical certificate's
previously disclosed native compiler dependence is unchanged.

This construction proves entire continuation of the **pole-removed ordinary
zeta**. It does not yet prove the functional equation of the completed
Dedekind zeta. The finite ideal-class sum must still be related under
dual-ideal inversion to its `s ↦ 1-s` transform. A quantitative circle-growth
bound for the constructed entire function is also needed to activate the
existing Jensen zero-count theorem. Finally, the Stark/Weil explicit formula
for the manuscript's test function remains a named source-level premise.
The cited small-degree discriminant results remain separate literature
inputs. The four main manuscript results retain the scoped Grade B and
PROVISIONAL_MATCH assessments.
