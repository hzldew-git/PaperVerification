# Main theorem correspondence

| Paper result | Formal result and external boundary | Assessment |
| --- | --- | --- |
| Theorem 1.2 | Strict root-discriminant bound and varying-degree global finiteness in Lean. The latter takes the published unconditional Odlyzko Table 4 bound as an explicit premise. | PROVISIONAL_MATCH |
| Theorem 1.3 | Strict integral root bound, rank at most 34, rank-one integral-to-classic lemma, and varying-degree global finiteness in Lean. Same explicit Table 4 premise. | PROVISIONAL_MATCH |
| Theorem 1.7 | All nonzero fractional ideal presentations: reduced basis, six-row sieve, principality including m=3, six actual isometry classes, constructive converse, valid representatives, and distinctness. | PROVISIONAL_MATCH |
| Corollary 1.9 | Concrete field-square iff m in {2,5,13}; source and strict threshold checked against v15. | PROVISIONAL_MATCH |
| Corollary 1.6 | v15_pnorm_finite_of_odlyzko_table4: every finite p >= 1 and p = infinity; the embedding power mean implies strict trace Euclideanity, then varying-field finiteness follows from the cited Table 4 input. | PROVISIONAL_MATCH; independent semantic sign-off pending. |
| Proposition 6.1 | v15_proposition_six_one_full: actual nonzero fractional ideal, totally positive integral coefficient, reduced Gram basis, determinant, exact radius, and both positive-integer scalar formulas on the full integer ring. NumberFieldLattice.v15AbstractRankOneIdealBridgeAnyField supplies the ideal presentation for arbitrary abstract rank-one spaces over every totally real field. | PROVISIONAL_MATCH; independent semantic sign-off pending. |

VERIFIED_MATCH: 0. The original four main results remain PROVISIONAL_MATCH. Corollary 1.6 and Proposition 6.1 now have complete scoped endpoints but have not received independent semantic sign-off. The author/domain and independent Lean review cards are unsigned. No critical weakening or extra project-specific endpoint premise was found beyond the disclosed cited Odlyzko inequality. The finite numerical table maxima are now standalone Lean theorems; the exact-rational computation identifying the table rows from the analytic H(n,d) inequalities remains a separate public certificate.
