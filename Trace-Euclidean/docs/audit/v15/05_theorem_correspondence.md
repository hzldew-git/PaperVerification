# Main theorem correspondence

| Paper result | Formal result and external boundary | Assessment |
| --- | --- | --- |
| Theorem 1.2 | Strict root-discriminant bound and varying-degree global finiteness in Lean. The latter takes the published unconditional Odlyzko Table 4 bound as an explicit premise. | PROVISIONAL_MATCH |
| Theorem 1.3 | Strict integral root bound, rank at most 34, rank-one integral-to-classic lemma, and varying-degree global finiteness in Lean. Same explicit Table 4 premise. | PROVISIONAL_MATCH |
| Theorem 1.7 | All nonzero fractional ideal presentations: reduced basis, six-row sieve, principality including m=3, six actual isometry classes, constructive converse, valid representatives, and distinctness. | PROVISIONAL_MATCH |
| Corollary 1.9 | Concrete field-square iff m in {2,5,13}; source and strict threshold checked against v15. | PROVISIONAL_MATCH |
| Proposition 6.1, general clause | v15_proposition_six_one_ideal: actual nonzero fractional ideal, totally positive integral coefficient, reduced Gram basis, determinant identity, and exact rational-field covering radius. GlobalLatticePresentation.rankOne_ideal_bridge supplies the canonical abstract presentation. | FORMALIZED_COMPONENT; independent semantic sign-off and one combined scalar-specialization endpoint remain outstanding. |

VERIFIED_MATCH: 0. The author/domain and independent Lean review cards are unsigned. No critical weakening or extra project-specific endpoint premise was found beyond the disclosed cited Odlyzko inequality. The generic Proposition 6.1 formula and canonical rank-one presentation are now exported. Its two scalar specializations and several standalone supporting lemmas have not been assembled into one complete proposition-level endpoint.
