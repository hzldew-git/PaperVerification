# Sources and provenance

The project pins Lean 4.32.1 and mathlib revision
`520045ab14e26149ee970e2e617ca04b09bde5d6` in its Lake files.

The number-field theta, Poisson, and Mellin modules in
`lean/DedekindZeta/` adapt code from
[`mathlib-initiative/sum_product`](https://github.com/mathlib-initiative/sum_product),
commit `80e4127a67742659d521466204c6d2d7e0ca2b3f`, under Apache 2.0.
The digamma-series module also adapts code from
[`anthropics/formal-math`](https://github.com/anthropics/formal-math),
commit `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`, under Apache 2.0.
See the notices and license texts in `lean/THIRD_PARTY_LICENSES/`.

The maximal-order certificate kernel in `lean/IdealArithmetic/` adapts the
necessary modules from
[`alainchmt/CertifyingInvariantsNF`](https://github.com/alainchmt/CertifyingInvariantsNF),
commit `6c035d7123819ad79b3f37dfe27f5cdb2b658dad`, under Apache 2.0.
The interval certificate modules in `lean/LeanCert/` come from
[`alerad/leancert`](https://github.com/alerad/leancert), tag `v4.32.1`, under
Apache 2.0. Their license and detailed scope are included there.

The discriminant-bound development follows A. M. Odlyzko's
[unconditional Table 4](https://www-users.cse.umn.edu/~odlyzko/unpublished/discr.bound.table4)
and [table description](https://www-users.cse.umn.edu/~odlyzko/unpublished/discr.bound.tables.txt).
The finite field data in `inputs/voight/` are attributed to John Voight's
[totally real field enumeration](https://jvoight.github.io/articles/ANTS144-fixed-errata-052714.pdf).
The enumeration completeness and the specialized degree-eleven formula
premises are identified in `TRUST.md`; the numerical optimization is proved
in Lean.

Rational attainment of the covering maximum is the conclusion of
Clark and Jagy, [*Euclidean quadratic forms and ADC forms II: integral
forms*, Proposition 4.1(a)](https://doi.org/10.4064/aa164-3-4).
This geometric existence statement is a literature input; the subsequent
trace-coordinate transfer is proved in Lean.

The extracted numerical inputs in `inputs/verification_inputs.json` are
provided to reproduce the public checks. The manuscript itself, its private
source metadata, and the author's source-to-input comparison are not
distributed here.
