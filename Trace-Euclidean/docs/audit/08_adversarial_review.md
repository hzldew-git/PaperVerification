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

9. **Does the covering proof depend on an incomplete Voronoi vertex list?**
   No. The new proof works on every point of the real plane by rounding and
   proves sharpness against every integral lattice point. The vertex algebra is
   retained as independent supporting evidence.
10. **Does scaling a form function alone prove finiteness of lattice classes?**
    No. The current proof also constructs the scale-two integral Gram matrix,
    proves its determinant norm factor `2^(nd)`, and builds a finite reduction
    code that reconstructs the full lattice equivalence class.
11. **Do the eight finite-set conclusions prove the paper theorems
    unconditionally?** Yes at the level of formal hypotheses. Their signatures
    quantify over `GlobalLatticeClass` and contain only the paper parameters
    and range assumptions. The generic framework is fully instantiated inside
    the proof.
12. **Could the quadratic endpoint use an assumed coordinate model?** The
    generic bridge can, but the audited theorem
    `realQuadratic_two_trace_euclidean_iff` constructs the field, both
    integer-coordinate equivalences, and trace formula before applying it.
13. **Could the integer-ring description prove only one containment?** No.
    Explicit integrality proves one containment and the trace/norm parity
    argument proves every algebraic integer has the stated coordinates.
14. **Could `m=3` be excluded only by a decimal approximation?** No. Lean
    proves the exact midpoint lower bound at the strict threshold.

15. **Could the pseudobasis argument silently assume the lattice is free?**
    No. `exists_pseudoBasis` is proved for every full lattice over the ring of
    integers, and the determinant proof uses the fractional ideals in that
    pseudobasis. No `Module.Free O_F L` hypothesis occurs in the final formula.
16. **Could equal finite codes forget information needed for isometry?** No.
    The code stores the full field-valued Gram matrix and the
    determinant-normalized coordinate submodule. Equality reconstructs a
    field-linear isometry mapping one lattice onto the other, then descends to
    equality in `GlobalLatticeClass`.

No further mathematical contradiction was found in the v9 statements covered
by the executable checks. The four core result groups are promoted to
`PROVISIONAL_MATCH`; independent author/domain and Lean review remains
required before `VERIFIED_MATCH` or Grade A.
