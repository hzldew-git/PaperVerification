# Trust and axiom report

The Lean project builds on Lean 4.32.1 with the pinned mathlib revision. The selected v15 endpoint axiom audits include the new fourth-order kernel, uniform-mass, Fourier-decay, and paired-summability theorems. Kernel-checked endpoints use only standard logical axioms (`propext`, `Classical.choice`, and `Quot.sound`) where applicable. Four finite-array equality theorems are kernel computations with no axiom dependencies. The archimedean numerical certificate uses `native_decide` in its interval and scalar checks; its compiler trust is audited separately. No `sorry`, `sorryAx`, or project axiom is used in the delivered proofs.

The field-discriminant estimates are EXTERNAL_INPUTS. Degree one is now proved internally from Minkowski's bound. Separate field-level premises record the exact minima in degrees 2--9, the empty degree-ten range at root discriminant at most 14, and the optimized degree-eleven bound 14.083. V15OdlyzkoTable4DescriptionInput records the full unconditional Table 4 row b=4 with A=36.347, B=16.593, the signature exponents, and the nonnegative prime-ideal correction. Lean proves 32/3 <= 10.667, the valid upward-rounding implication, the totally real specialization, field-to-class transport, and that Table 4 is required only from degree 12 for Section 4 and degree 15 for finiteness. The online November 1976 Table 2 has 14.034 at degree 11, so 14.083 is kept as a distinct later optimized source input. None of these cited source theorems is concealed as a project axiom. Lean proves their combination, the exact Gamma normalization and rational enclosure of H(n,d), both complete finite-grid equivalences, and the downstream class-level membership theorems.

The same axiom audit now covers the exact Fourier transform of the
hyperbolic-secant factor, the product-to-convolution bridge, and the theorem
that the complete unconditional `b=4` kernel has a real nonnegative Fourier
transform. It also covers the exponentially tilted factor, positivity in the
open strip, continuity up to both boundary weights, and the source-exact
theorem `Re Phi(s) >= 0` for `0 <= Re(s) <= 1`. For a summable zero family,
Lean proves that its total contribution has nonnegative real part. The
Dedekind-zeta continuation and functional equation, the Stark/Weil explicit
formula and the count of actual zero occurrences remain external mathematics. Lean now
proves the test function's `C^4` regularity, derivative decay, uniform
fourth-power transform decay, and paired-zero convergence conditional on a
quadratic count for an ordered occurrence enumeration. It also
evaluates the exact E = 32/3 archimedean error integral and both endpoint
transforms `Phi(0) = Phi(1) = 16/3`.
The source-exact equation (2.3) remains a named unproved premise in a
conditional theorem that derives the Table 4 interface. Both archimedean
integrals are proved convergent and the strict `A,B` certificate is supplied
by analytic endpoint bounds, verified dyadic interval enclosures, and a
certified Euler–Mascheroni lower bound. The interval calculations use
`native_decide`, whose generated `_native.native_decide.ax_*` dependencies are a distinct trust
boundary from kernel-only reduction. The remaining explicit-formula input is
not asserted as a project axiom or proved source theorem.

The public Python and Wolfram checks trust their kernels and the extracted v15 input file. The private source-bound checks additionally verify the manuscript hash and printed data. Neither computational PASS counts nor Lean compilation certifies paper-to-code semantic fidelity. Only the active v15 computational artifacts are included in the current package.
