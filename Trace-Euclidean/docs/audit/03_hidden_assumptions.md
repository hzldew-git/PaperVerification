# Hidden-assumption audit

## Number-field lattice semantics

`NumberFieldLattice` explicitly requires a number field, total reality, a
finite-dimensional quadratic form, a full `O_F`-lattice, nondegeneracy,
positive definiteness at every real embedding, and integrality of every
quadratic value. Classic integrality is a separate predicate using mathlib's
associated bilinear form, whose normalization is one half of the polar form.

`NumberFieldLatticeEquiv` records the field isomorphism, additive bijection,
semilinearity, lattice preservation, and quadratic-form compatibility from the
paper. The current global finiteness endpoints do not construct the quotient
by this equivalence; their type `α` is documented as the quotient and remains
part of the semantic confirmation obligation.

## Power means

`pNormEuclidean_imp_traceEuclidean` assumes the pointwise power-mean
inequality as an argument. It does not define finite or infinite power means,
prove the inequality, or formalize the identity `M_1=Tr/d`. The paper's
uniform use of `t=d` across varying fields remains a paper-level argument.

## Scaling and equivalence

`IsometricForms` uses a bare type equivalence and equality of real-valued form
functions. It does not encode modules over rings of integers, integrality,
volume ideals, same-field linearity, or field-varying semilinear equivalence.
The cancellation theorem validates the algebraic factor-two step, but the
complete class-bijection argument still needs those structures.

## Analytic maximum

The Lean Hessian theorem assumes the differentiated critical-point identities,
`z>0`, `gxx<0`, and the negative stationary derivative. It proves the
saddle conclusion from those inputs. The definitions of the gamma-based
function, differentiation, boundary compactification, uniqueness of boundary
critical points, and global boundary comparison are checked by Mathematica or
remain analytic paper arguments.

## Finiteness

The exact `g_s` and `g_n` functions, their fixed-rank degree tails,
fixed-degree rank tails, and uniform high-rank envelopes are now proved in
Lean. Hermite finiteness and bounded ideal-norm finiteness are invoked from
mathlib.

`MainFinitenessFramework` remains a material assumption. Its fields require:

1. identification of the represented objects with equivalence classes of
   positive-definite trace-Euclidean number-field lattices;
2. the manuscript's discriminant and volume-ideal bounds;
3. the classic and factor-two-scaled integral volume ideals;
4. finiteness of each fixed-field, fixed-rank, fixed-volume-ideal fiber, where
   O'Meara 103:4 and Remark 103:5 enter.

No field of the structure is an axiom in Lean: every public theorem is
conditional on an explicit value of the structure. The absence of an
instantiation for the paper's actual objects is nevertheless a stronger
assumption than the paper theorem and blocks an unconditional match.

## Quadratic covering geometry

The original vector algebra remains available, but the principal proof no
longer assumes facet exhaustion. On the full real plane, rounding constructs a
lattice point within the claimed radius for every point, and an explicit
midpoint or vertex gives a lower bound against every integral lattice point.
`SquaredCoveringRadiusSpecOver` expresses the resulting least upper bound by
an upper property and sharpness below it. Independent review must confirm that
this order-theoretic specification is accepted as the paper's squared
covering-radius convention.

## Quadratic classification

`realQuadratic_two_trace_euclidean_iff` constructs the quadratic algebra,
proves the full algebraic-integer coordinate description in both residue
classes, transports the exact trace-square cost, and proves necessity and
sufficiency for `m=2,5,13`. It is not parameterized by a coordinate model or
an assumed radius formula. The remaining item is independent confirmation that
the concrete `QuadraticAlgebra ℚ m 0` presentation and its field-level trace
predicate are the intended paper conventions.

## External sources

All cited number-field, lattice-finiteness, volume, and Voronoi theorems are
treated as `EXTERNAL_INPUT`. Their hypotheses and normalization choices must
be checked independently against the cited editions.
