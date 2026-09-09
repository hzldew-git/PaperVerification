# Hidden-assumption audit

## Abstract Euclidean predicates

`StrictEuclidean` receives an arbitrary real-valued cost. It does not construct
the trace cost from a totally real field, quadratic form, Minkowski embedding,
or lattice. `SquaredCoveringRadiusSpec` assumes both the upper-bound property
and sharpness of the proposed radius. The Lean radius implications are valid
once that specification is supplied; existence and identification of the
paper's `rho_T(L)` are not formalized.

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

The abstract Lean finiteness lemmas assume convergence to minus infinity,
explicit rectangle bounds, or finite fibers. They do not prove number-field
discriminant finiteness, ideal finiteness, O'Meara's quadratic-space and lattice
class finiteness, or the manuscript's volume and discriminant bounds.

## Voronoi geometry

The Lean two-vector module assumes the coordinate models and, where needed,
`s^2=m` and a nonzero Gram determinant. It proves the algebra after the
relevant facet normals are known. It does not prove that the displayed vectors
form a strict obtuse superbase, that they are precisely the strict Voronoi
vectors, that every listed bisector intersection is a cell vertex, or that the
listed vertices exhaust the Voronoi cell.

## Quadratic classification

The arithmetic module proves candidate elimination from the two radius formulas
and proves the midpoint obstruction for `m=3`. It does not construct
`Q(sqrt m)`, its ring of integers, its Minkowski lattice, or the equivalence
between trace Euclideanity and a strict covering-radius inequality. Sufficiency
for `m=2,5,13` therefore still depends on Proposition 6.1 and Lemma 2.2 at the
paper level.

## External sources

All cited number-field, lattice-finiteness, volume, and Voronoi theorems are
treated as `EXTERNAL_INPUT`. Their hypotheses and normalization choices must
be checked independently against the cited editions.
