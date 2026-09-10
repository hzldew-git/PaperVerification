# Hidden-assumption audit

## Number-field lattice semantics

`NumberFieldLattice` explicitly requires a number field, total reality, a
finite-dimensional quadratic form, a full `O_F`-lattice, nondegeneracy,
positive definiteness at every real embedding, and integrality of every
quadratic value. Classic integrality is a separate predicate using mathlib's
associated bilinear form, whose normalization is one half of the polar form.

`GlobalLatticePresentation.EquivalenceData` records the field isomorphism,
additive bijection, semilinearity, lattice preservation, quadratic-form
compatibility, rank, and degree from the paper. `GlobalLatticeClass` is the
actual quotient by this relation. The public global finiteness endpoints
quantify over that quotient rather than over an abstract placeholder type.

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

The former material framework premise has been removed from the endpoint
signatures. The current dependency chain proves:

1. a pseudobasis for every full lattice, including nonfree projective
   `O_F`-modules;
2. the general trace determinant and squared-covolume identities;
3. sharp classic and factor-two integral discriminant lower bounds;
4. the trace-Euclidean covering upper bound;
5. bounded-discriminant field finiteness through mathlib's Hermite theorem;
6. fixed-field, fixed-rank class finiteness by a finite Gram/module reduction
   code whose equality reconstructs the quotient equivalence;
7. the analytic degree, rank, and uniform-envelope tails.

`MainFinitenessFramework` remains an internal generic assembly record, but
`GlobalFiniteness.toMainFinitenessFramework` supplies every field with a
proved theorem. It is absent from the eight public endpoint hypotheses.

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

Mathlib results used for Dedekind projectivity, fractional ideals, Hermite
finiteness, Haar covolume, and standard real/number-field algebra remain part
of the trusted library dependency. The manuscript's cited results are still
source-review obligations unless the theorem correspondence table records an
independent Lean proof or an alternative Lean route.
