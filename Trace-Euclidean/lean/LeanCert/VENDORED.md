# LeanCert modules used by the Odlyzko integral certificates

These 27 Lean modules are copied unchanged from the `v4.32.1` tag of
[LeanCert](https://github.com/alerad/leancert). The complete upstream Apache
2.0 license is in [LICENSE](LICENSE). Only the transitive module imports of
`LeanCert.Validity.IntegrationDyadic`,
`LeanCert.Examples.EulerMascheroniBounds`, and `LeanCert.Validity.Dyadic`
are included. The latter two provide certified bounds for the
Euler–Mascheroni constant and elementary scalar functions.

The original LeanCert release uses Lean 4.32.0. These unchanged source files
are compiled here against the verification project's pinned Lean 4.32.1 and
mathlib `v4.32.1`. Numerical proof certificates using `native_decide` depend
on Lean's native evaluator; `#print axioms` exposes generated
`_native.native_decide.ax_*` dependencies. This trust boundary must be
reported separately from the analytic Odlyzko explicit formula.
