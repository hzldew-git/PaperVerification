# Definition dictionary

| Manuscript term | Lean expression | Semantic check |
| --- | --- | --- |
| Totally real number field | CodedNumberField and GlobalLatticePresentation.totallyReal | Every global class carries total reality. |
| Positive definite integral lattice | GlobalLatticePresentation | Full module, positive definite form, and value integrality are bundled. |
| Classic integral | GlobalLatticePresentation.IsClassicIntegral | Bilinear scale is integral; independent factor-of-two review remains. |
| Trace Euclidean | IsTraceEuclidean and V15IdealTraceEuclidean | Universal field point, existential lattice approximation, strict threshold equal to field degree. |
| Varying-field isometry class | GlobalLatticeClass | Quotient by field equivalence and semilinear lattice isometry. |
| Rank-one presentation (I, alpha x^2) | FractionalIdeal, alpha, v15ValueFractionalIdeal | Nonzero ideal, total positivity, and alpha I^2 subset O_F are explicit. |
| Two real embeddings positive | V15RealQuadraticTotallyPositive | Coordinates alpha.re plus/minus alpha.im times sqrt(m); proved equivalent to positive rational part and field norm. |
| Six F-isometry classes | V15SixFreeIsometryClass | Actual O_F-module equivalence preserving the form, with the six printed coefficients. |
| Trace Euclidean field | IsFieldTraceEuclidean 2 | Square form on the full integer ring. |
| p-norm Euclidean, p in [1, infinity] | V15PNormExponent and GlobalLatticePresentation.IsV15PNormEuclidean | Finite real exponents at least one and a separate infinity constructor; normalized complex-embedding values are real under total reality. Independent field-model review remains. |
| Ideal trace Euclidean at threshold t | V15IdealTraceEuclideanAt | Arbitrary real threshold; rankOne_ideal_bridge_degree specializes t to the field degree. |

Strict inequality and arbitrary fractional-ideal scope were checked against the printed statements rather than inferred from theorem names.
