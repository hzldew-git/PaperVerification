# Vendored number-field theta and Mellin development

The Lean files in this directory are based on
[`mathlib-initiative/sum_product`](https://github.com/mathlib-initiative/sum_product),
commit `80e4127a67742659d521466204c6d2d7e0ca2b3f`, under Apache 2.0.
See `../THIRD_PARTY_LICENSES/sum_product_APACHE-2.0.txt`.

`PoissonSummation`, `Theta`, `Statements`, `GammaIntegral`,
`ConeRadialReduction`, `ConeMellinBridge`, and `PerClass` are upstream files
with small proof adaptations for Lean 4.32.1 and this repository's existing
copy of `MellinPrinciple` (`TraceEuclidean.AnalyticMellinPrinciple`).
`GlobalContinuation` and `ZetaRegularization` are new modules added for this
verification project. Their public theorems prove an entire continuation of
`(s - 1) * NumberField.dedekindZeta K s` for every number field `K`.

The functional equation, quantitative growth bound, and Stark/Weil explicit
formula require separate proofs.
