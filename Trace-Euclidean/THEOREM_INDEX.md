# Trace-Euclidean v15 theorem index

Frozen author source SHA-256:
83a236e93648ce0802f8a0d3022de63710d089f3a4f7e61214a4c855459597b5.
The manuscript is not redistributed.

Status vocabulary: PROVISIONAL_MATCH means the reviewed paper claim and Lean
statement appear aligned but independent sign-off is absent. FORMALIZED_COMPONENT
means a specified part is proved. COMPUTATION_VERIFIED means the encoded
calculation was rerun. EXTERNAL_INPUT means a cited result is an explicit premise.

| Paper item | Lean or computational evidence | Status |
| --- | --- | --- |
| Definition 1.1, strict trace Euclideanity | IsTraceEuclidean, V15IdealTraceEuclidean; strict threshold equals field degree | PROVISIONAL_MATCH |
| Theorem 1.2, classic integral finiteness | v15_classic_root_discriminant_lt; v15_classic_finite_of_odlyzko_table4; variable-degree finite assembly | PROVISIONAL_MATCH with Table 4 EXTERNAL_INPUT |
| Theorem 1.3, integral finiteness | v15_integral_root_discriminant_lt; v15_rank_one_classic_input; v15_integral_finite_of_odlyzko_table4_source | PROVISIONAL_MATCH with Table 4 EXTERNAL_INPUT |
| Corollary 1.6, p-norm finiteness | Existing power-mean witness transfer; full varying-degree corollary not exported | FORMALIZED_COMPONENT |
| Theorem 1.7, six rank-one classes | v15_actual_ideal_six_rows, v15_actual_ideal_principal, v15_rank_one_real_quadratic_classification_totally_positive; six representative validity and Euclidean proofs; distinction | PROVISIONAL_MATCH |
| Corollary 1.9, trace Euclidean fields | realQuadratic_two_trace_euclidean_iff and concrete square-form bridge | PROVISIONAL_MATCH |
| Reduced Gram sieve | 22 triples, nine field rows, six surviving rows, all linked to actual ideals | FORMALIZED_COMPONENT |
| Proposition 6.1, general binary radius formula | Rational deep-hole necessity, six constructive upper covers, exact six radius expressions; full generic formula not exported | PARTIAL_FORMALIZATION |
| Section 4 numerical tables | Public Python and Wolfram v15 reruns; source-bound private checks | COMPUTATION_VERIFIED |

The active [v15 audit](docs/audit/v15/05_theorem_correspondence.md) expands the
assumptions and quantifiers. The [Lean axiom report](lean/audit/main_theorem_axioms.txt)
contains the elaborated endpoint signatures and trust dependencies. The
historical v9 index is under docs/v9_release_notes.
