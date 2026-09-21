# Coverage report

| Category | Reviewed | Formal and computational coverage |
| --- | --- | --- |
| Main theorems 1.2, 1.3, 1.7 | 3 of 3 | All have substantial kernel-checked v15 endpoints; global finiteness uses the explicit cited Odlyzko premise. |
| Main field corollary 1.9 | 1 of 1 | Concrete iff endpoint reused and checked against v15. |
| Main-result status | 4 results | 4 PROVISIONAL_MATCH, 0 VERIFIED_MATCH, 0 critical mismatches. |
| Strict root-discriminant and finite grid | Both bounds, rank and degree | Strict Lean bounds; rank at most 34; degree at most 14 from Table 4. |
| Rank-one classification | Six classes | All fractional ideals, principality, six isometries, six valid constructive representatives, and distinctness. |
| Reduced Gram sieve | 22, nine, six rows | Formal integer and field arithmetic connected to an actual ideal basis. |
| General binary radius and scalar formulas | Proposition 6.1 | Generic real/rational reduced-Gram theorem, actual-ideal basis and determinant, both positive-integer scalar formulas, and one combined proposition-level endpoint. |
| Abstract rank-one ideal presentation | Rank-one preamble to Proposition 6.1 | Canonical global model yields a nonzero fractional ideal and totally positive integral coefficient with equivalent strict trace condition at any real threshold, including the field degree. |
| Abstract-space coordinate transport | All totally real number fields | Arbitrary positive-rank finite-dimensional space gives an actual semilinear coordinate isometry to a coded field; the full lattice, form, trace condition, degree, and classic integrality are preserved. Rank one composes to an ideal presentation at every real threshold. |
| p-norm finiteness | Corollary 1.6 | Every finite real p >= 1 and p = infinity; normalized embedding means, pointwise power-mean bound, strict trace implication, and varying-field finite classes from explicit Table 4 input. |
| Analytic Section 4 and supporting lemmas | Selected | Public rational-interval checks resolve every cell of the finite admissibility grid. Lean independently proves the 24/63 row counts, complete rank/degree bound arrays, exact global maxima, degree 7--9 rank-two result, and the conditional overall rank-twelve consequence from those rows. The analytic interval-to-row bridge remains computational rather than a Lean theorem. |
| Public computation | v15 | 1156 Python PASS and 115 Wolfram PASS; no failures. |
| Private source-bound computation | v15 | 1165 Python PASS and 112 Wolfram PASS; no failures. |

The v9 checks remain archived evidence for the prior source version. They are not included in the v15 counts. Coverage percentages for mathematical theorems are omitted because statement scope matters more than declaration count.
