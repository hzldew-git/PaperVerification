# Trust and axiom report

The Lean project builds on Lean 4.32.1 with the pinned mathlib revision. All 186 selected v15 endpoint axiom sets contain only propext, Classical.choice, and Quot.sound. Four additional finite-array equality theorems are kernel computations with no axiom dependencies. Source scanning found no sorry, sorryAx, project axiom, native_decide, run_tac, unsafe, extern, or implemented_by in the proof source.

The field-discriminant estimates are EXTERNAL_INPUTS. Degree one is now proved internally from Minkowski's bound. Separate field-level premises record the exact minima in degrees 2--9, the empty degree-ten range at root discriminant at most 14, and the optimized degree-eleven bound 14.083. V15OdlyzkoTable4DescriptionInput records the full unconditional Table 4 row b=4 with A=36.347, B=16.593, the signature exponents, and the nonnegative prime-ideal correction. Lean proves 32/3 <= 10.667, the valid upward-rounding implication, the totally real specialization, field-to-class transport, and that Table 4 is required only from degree 12 for Section 4 and degree 15 for finiteness. The online November 1976 Table 2 has 14.034 at degree 11, so 14.083 is kept as a distinct later optimized source input. None of these cited source theorems is concealed as a project axiom. Lean proves their combination, the exact Gamma normalization and rational enclosure of H(n,d), both complete finite-grid equivalences, and the downstream class-level membership theorems.

The same axiom audit now covers the exact Fourier transform of the
hyperbolic-secant factor, the product-to-convolution bridge, and the theorem
that the complete unconditional `b=4` kernel has a real nonnegative Fourier
transform. It also covers the exponentially tilted factor, positivity in the
open strip, continuity up to both boundary weights, and the source-exact
theorem `Re Phi(s) >= 0` for `0 <= Re(s) <= 1`. For a summable zero family,
Lean proves that its total contribution has nonnegative real part. The
Dedekind-zeta continuation and functional equation, the Stark/Weil explicit
formula and convergence of its paired zero sum, and the certified
archimedean estimates for A and B remain external mathematics. Lean now
proves the test function's differentiability and derivative decay, and
evaluates the exact E = 32/3 archimedean error integral.

The public Python and Wolfram checks trust their kernels and the extracted v15 input file. The private source-bound checks additionally verify the manuscript hash and printed data. Neither computational PASS counts nor Lean compilation certifies paper-to-code semantic fidelity. Only the active v15 computational artifacts are included in the current package.
