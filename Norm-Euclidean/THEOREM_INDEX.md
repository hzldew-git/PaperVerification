# Selected theorem correspondence

The numbering below identifies the reference manuscript statements checked for
this release. Private manuscript identification is retained locally by the
author. The mathematical scope and public declarations are given here so that
the release remains usable without manuscript files.

Status: **PROVISIONAL_MATCH** for the selected correspondences. Statement
extraction and formal-source comparison were performed separately by the same
agent. No independent human fidelity certificate or paper-wide grade is claimed.
Exact elaborated types are generated from `lean/validation/Core.lean`; a passing
build and standard-axiom report alone do not establish source correspondence.
Inherited helper comments may use older result numbering; this index controls
the advertised correspondence for this release.

| Reference result | Public declaration(s), prefixed by `NormEuclidean.` | Scope |
| --- | --- | --- |
| [Theorem 1.2](lean/NormEuclidean/MainClassNumber.lean#L32) | `MainClassNumber.class_number_theorem` | For a positive-rank anisotropic integral norm-Euclidean lattice: maximality, ordinary class number one, stable lattice class number equal to the field class number, and the separate rank branches. |
| [Corollary 1.4](lean/NormEuclidean/StableGenusDecomposition.lean#L82) | `StableGenusDecomposition.genus_eq_union`, `classes_disjoint` | If the field class number is two, the ordinary genus of the standard stabilization is exactly the disjoint union of its class and the class obtained using any nonprincipal ideal hyperbolic plane. Includes rank one. |
| [Theorem 3.1](lean/NormEuclidean/NumberFieldCancellation.lean#L24) | `numberField_hyperbolic_cancellation_from_module` | Isometries of the actual stabilized integral modules descend to an isometry of the original integral modules. The comparison lattice is arbitrary; no freeness assumption is added. |
| [Corollary 3.2](lean/NormEuclidean/IdealHyperbolicCancellation.lean#L104) | `IdealHyperbolic.cancellation_iff_classGroup`, `cancellation_from_module` | An ideal hyperbolic stabilization is isometric to the standard stabilization precisely when the ideal class is trivial and the original lattices are integrally isometric. No genus premise is imposed on the comparison lattice. |
| [Lemma 4.3](lean/NormEuclidean/HilbertBinaryStabilization.lean#L88) | `HilbertBinaryStabilization.hyperbolic_isometry` | An anisotropic binary lattice with discriminant extension equal to the actual ordinary Hilbert class field stabilizes every lattice in its genus. No norm-Euclidean hypothesis is required here. |
| [Lemma 5.1](lean/NormEuclidean/LatticeRank.lean#L59) | `normIdeal_absNorm_lt_of_pos_finrank` | For positive rank, the absolute norm of the actual norm ideal is strictly less than `4^[F:Q]`. |
| [Theorem 1.5(iii)](lean/NormEuclidean/UnaryRankFiniteness.lean#L51) | `UnaryRankFiniteness.exists_finite_models`, `finite_euclideanClasses` | Finitely many actual integral-isometry classes of anisotropic norm-Euclidean rank-one lattices over a fixed number field, including nonfree modules and all signatures. |
| [Lemma 5.4](lean/NormEuclidean/BoundedVolumeFiniteness.lean#L31) | `BoundedVolumeFiniteness.exists_finite_models`, `finite_classes` | Fixed-field, fixed-rank, bounded-volume finiteness for anisotropic integral lattices in varying ambient quadratic spaces. The positive definite case in the paper is included. |

## Definitions and hypotheses that matter

- `Lattice` bundles a finite full integral module. It does not assume an
  integral basis or freeness. Ambient vector-space bases in some interfaces
  are coordinate choices, not integral freeness assumptions.
- `HasNumberFieldApproximation` is the strict absolute field-norm inequality
  for approximation by an element of the entire integral lattice. Anisotropy
  is a separate hypothesis.
- `SameGenus` uses the actual completions at finite and infinite places.
  `OrdinaryGenusMass.classNumber` counts ordinary integral-isometry classes,
  not proper or spinor classes.
- The stable equality in Theorem 1.2 is `h(L perpendicular H)=h(F)`.
  The field class number can be two in the unary and binary branches.
- An ideal hyperbolic plane uses a nonzero fractional ideal; the explicit
  nonzero hypothesis is retained in its Lean interfaces.
- The unary equality criterion is exactly failure of module freeness. The
  binary extension is constructed from the negative determinant of an
  associated Gram matrix inside a separable closure, and compared with the
  actual Hilbert class field.
- The Hilbert class field uses the ordinary class group: it is unramified
  at finite and infinite places. It is not the narrow class field.
- The bounded-volume theorem uses the half-polar volume ideal. Half-polar
  coefficients need not be integral at dyadic places. Its conclusion uses
  actual integral isometry, not an invariant standing in for isometry.
- Rank is ambient field dimension; localization identifies it with the
  integral module rank without assuming freeness.

## Scope excluded from this release

Theorem 1.5(i), full Theorem 1.5(ii), the high-rank parts of Proposition 5.3,
the numerical classification bounds of Theorem 1.7, and the exact unary
field enumeration discussed in Remark 1.6 are not certified by this package.
Some related lemmas occur as dependencies; that does not enlarge the advertised
scope. The old free-scalar unary supplement is not the endpoint used for the
nonfree unary theorem above.

The positive binary bounded-class results in the development need a separate
total-definiteness/sign-pattern assembly before the complete binary statement
is advertised. The high-rank measure comparisons still need independent
standard Tamagawa normalization and numerical covolume evaluation. These
remaining tasks are not assumed as axioms in the selected endpoints.
