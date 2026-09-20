# Coverage report

| Category | Reviewed | Formal and computational coverage |
| --- | --- | --- |
| Main theorems 1.2, 1.3, 1.7 | 3 of 3 | All have substantial kernel-checked v15 endpoints; global finiteness uses the explicit cited Odlyzko premise. |
| Main field corollary 1.9 | 1 of 1 | Concrete iff endpoint reused and checked against v15. |
| Main-result status | 4 results | 4 PROVISIONAL_MATCH, 0 VERIFIED_MATCH, 0 critical mismatches. |
| Strict root-discriminant and finite grid | Both bounds, rank and degree | Strict Lean bounds; rank at most 34; degree at most 14 from Table 4. |
| Rank-one classification | Six classes | All fractional ideals, principality, six isometries, six valid constructive representatives, and distinctness. |
| Reduced Gram sieve | 22, nine, six rows | Formal integer and field arithmetic connected to an actual ideal basis. |
| General binary radius formula | Proposition 6.1 | Complete generic real/rational reduced-Gram theorem, plus actual-ideal basis, determinant, and exact rational-field radius. The two displayed scalar specializations are not assembled in one new endpoint. |
| Abstract rank-one ideal presentation | Rank-one preamble to Proposition 6.1 | Canonical global model now yields a nonzero fractional ideal and totally positive integral coefficient with equivalent strict trace condition. |
| Analytic Section 4 and supporting lemmas | Selected | Source-bound exact and numerical checks; not every standalone statement is in Lean. |
| Public computation | v15 | 1156 Python PASS and 115 Wolfram PASS; no failures. |
| Private source-bound computation | v15 | 1165 Python PASS and 112 Wolfram PASS; no failures. |

The v9 checks remain archived evidence for the prior source version. They are not included in the v15 counts. Coverage percentages for mathematical theorems are omitted because statement scope matters more than declaration count.
