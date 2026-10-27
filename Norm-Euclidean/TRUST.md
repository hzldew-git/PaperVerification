# Trust and validation boundary

## Fixed dependencies

| Component | Revision |
| --- | --- |
| Lean | 4.32.1 |
| mathlib | `520045ab14e26149ee970e2e617ca04b09bde5d6` |
| BongTheory | `a1343b6e471cbf417cab0e09dc5876b74358260a` |
| Vendored class-field source | `01b4bcb786c458c9af029860c9bbdbd67dd7c978`, adapted to the fixed toolchain |

All additional package revisions remain pinned in `lean/lake-manifest.json`.
The adapted class-field sources are compiled as part of this release; an
upstream theorem name is not treated as an external axiom.

## What the checks establish

`tools/verify_public.py` checks source hashes, the local import closure,
unchanged dependency pins, forbidden unfinished proof constructs and public
metadata. Its default run builds the selected root and then elaborates an
explicit `#check` and transitive `#print axioms` probe for every registered
declaration. Missing reports, duplicate reports and any axiom outside
`propext`, `Classical.choice`, and `Quot.sound` cause failure.

The selected endpoints do not use `sorryAx`, custom axioms or a native-code
decision oracle. The source gate also rejects `native_decide` and constructs
that bypass normal kernel checking in the exported proof sources. Finite
numerical experiments are not substituted for general Lean proofs.

An axiom report does not discharge mathematical hypotheses in a theorem type.
The theorem index lists the material scope, and the generated statement types
make the hypotheses inspectable. In particular, no assumed stable class number
one, external strong approximation, or supplied high-rank mass value is added
to the advertised class-number endpoint.

## Reproducibility and fidelity are separate

The source package is intended to rebuild without project-owned precompiled
objects. Fixed upstream dependency caches may be used. GitHub Actions performs
the same build and declaration audit on a fresh checkout, without a cache of
this package's own compiled objects.

Local checked results are recorded separately from hosted CI. The presence of a
workflow file is not evidence that it has run. A repository commit and a
successful run at that exact commit are needed to assert hosted reproduction.

The correspondence status of the selected paper statements is
`PROVISIONAL_MATCH`. No independent author/expert signoff is inferred from
publication authorization. This package makes no paper-wide Grade A/B/C claim.
The private manuscript binding and historical working audit are not public
verification inputs.
