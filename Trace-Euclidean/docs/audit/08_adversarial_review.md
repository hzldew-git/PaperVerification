# Adversarial review

## Quantifier and boundary attacks

1. **Could a uniform lattice witness be required accidentally?** No. The
   abstract predicate retains `forall x, exists y`, so the witness may depend
   on the point.
2. **Could a closed covering bound prove strict Euclideanity at equality?** No.
   The Lean bridge requires `rhoSq<t`; in the reverse direction it concludes
   only `rhoSq<=t`.
3. **Could `m=3` slip through the closed bound?** The candidate theorem allows
   `m=3`, and a separate exact half-integer midpoint theorem proves the strict
   obstruction.
4. **Could Corollary 1.6 silently fix `t` while the degree varies?** The Lean
   component proves only the pointwise cost implication. The paper's uniform
   `t=d` reasoning is visible as an unformalized bridge.

## Algebra and calculus attacks

5. **Could an interior critical point be mistaken for a maximum?** The repaired
   argument proves that the stationary derivative is negative and that the
   Hessian determinant is strictly negative under the differentiated critical
   identities. Mathematica independently checks the identities and sign chain.
6. **Could the maximum escape to infinity?** The computational ledger checks
   the two tail limits, the sign at `x=3`, and monotonicity of `x K(x)`.
7. **Could the wrong boundary win?** Certified rational brackets establish the
   strict comparison between the two boundary candidates in Lemma 4.3.
8. **Could the Voronoi norm formula contain a denominator or factor error?**
   Lean solves the bisector system and proves the general norm identity under a
   nonzero determinant; both quadratic specializations are then proved.

## Scope attacks

9. **Does the coordinate algebra prove that these are all Voronoi vertices?**
   No. The strict obtuse-superbase and facet-exhaustion argument remains a
   paper-level geometric step.
10. **Does scaling a form function prove finiteness of lattice classes?** No.
    It validates cancellation of the factor two. Integrality, ideal scaling,
    and class finiteness remain external.
11. **Do finite parameter lemmas prove the global finiteness theorems?** No.
    They assemble finite bounds only after analytic and arithmetic inputs are
    supplied.
12. **Does successful compilation prove the classification theorem?** No. The
    field construction and end-to-end iff statement are absent.

No further mathematical contradiction was found in the v9 statements covered
by the executable checks. The unanswered attacks above are recorded as scope
gaps, not silently treated as proved.
