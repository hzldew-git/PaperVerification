# Trust and axiom report

The Lean project builds on Lean 4.32.1 with the pinned mathlib revision. The selected v15 endpoint axiom audits include the new fourth-order kernel, uniform-mass, Fourier-decay, and paired-summability theorems. Kernel-checked endpoints use only standard logical axioms (`propext`, `Classical.choice`, and `Quot.sound`) where applicable. Four finite-array equality theorems are kernel computations with no axiom dependencies. The archimedean numerical certificate uses `native_decide` in its interval and scalar checks; its compiler trust is audited separately. No `sorry`, `sorryAx`, or project axiom is used in the delivered proofs.

The field-discriminant estimates are EXTERNAL_INPUTS. Degree one is now proved internally from Minkowski's bound. Separate field-level premises record the exact minima in degrees 2--9, the empty degree-ten range at root discriminant at most 14, and the optimized degree-eleven bound 14.083. V15OdlyzkoTable4DescriptionInput records the full unconditional Table 4 row b=4 with A=36.347, B=16.593, the signature exponents, and the nonnegative prime-ideal correction. Lean proves 32/3 <= 10.667, the valid upward-rounding implication, the totally real specialization, field-to-class transport, and that Table 4 is required only from degree 12 for Section 4 and degree 15 for finiteness. The online November 1976 Table 2 has 14.034 at degree 11, so 14.083 is kept as a distinct later optimized source input. None of these cited source theorems is concealed as a project axiom. Lean proves their combination, the exact Gamma normalization and rational enclosure of H(n,d), both complete finite-grid equivalences, and the downstream class-level membership theorems.

The `V15DedekindZetaZeros.lean` and `V15DedekindZetaConjugation.lean` modules
add no project axiom. The required entire continuation of `(s-1) ζ_K(s)`
is now constructed by the vendored number-field theta/Mellin development and
`V15DedekindZetaConstructed.lean`. The sharp HSW numerical count remains a
named mathematical hypothesis, but it is no longer needed for convergence of
the Odlyzko zero sum: the completed-function growth and Jensen route supplies
a coarser quadratic count internally.
From mathlib's
class-number-formula residue and analytic identity/isolated-zero theorems,
Lean proves any such continuation is unique and nonzero, its zeros are
discrete, and its multiplicity-aware occurrence set is finite at bounded
height. Real ideal-norm coefficients and continuation uniqueness imply
conjugation symmetry; repeated derivatives show that conjugation preserves
analytic zero order. The induced map is an involution on actual zero
occurrences and preserves every bounded-height set. The constructed instance
proves existence of the continuation. The published sharp count inequality
remains unproved, while `V15MellinGrowth.lean` now proves the coarser count
needed here.

`V15DedekindZetaZeroHeight.lean` adds a finite exhaustion and countability
proof for the actual multiplicity-aware occurrences. It proves a right
interval of locally constant zero counts and, from continuity, extends any
bound established at occurrence-free heights to boundary heights. The
source-normalized HSW transfer still assumes the numerical inequality at
regular heights. The regularization is now constructed. The new endpoint
dependency audit is included in
`lean/audit/main_theorem_axioms.txt`.

The same axiom audit now covers the exact Fourier transform of the
hyperbolic-secant factor, the product-to-convolution bridge, and the theorem
that the complete unconditional `b=4` kernel has a real nonnegative Fourier
transform. It also covers the exponentially tilted factor, positivity in the
open strip, continuity up to both boundary weights, and the source-exact
theorem `Re Phi(s) >= 0` for `0 <= Re(s) <= 1`. For a summable zero family,
Lean proves that its total contribution has nonnegative real part. The
completed Dedekind-zeta functional equation is now a Lean theorem.
`V15MellinGrowth.lean` turns the theta decay estimates into a global quadratic
exponential bound for the entire completed function, supplies the precise
Jensen circles, proves a quadratic count of actual zero occurrences, and
proves absolute convergence of their direct Odlyzko transform. The
Stark/Weil explicit formula remains external mathematics. Lean now
proves the test function's `C^4` regularity, derivative decay, uniform
fourth-power transform decay, and direct zero-occurrence convergence. It also
evaluates the exact E = 32/3 archimedean error integral and both endpoint
transforms `Phi(0) = Phi(1) = 16/3`. The kernel-only
`V15OdlyzkoArchimedeanBridge` proves joint absolute integrability for the
critical transform and both Gauss digamma kernels, the required Fubini
interchanges and real-place rescaling, and the exact number-field identity
whose right side is `log |D_K| - r_1 log A_* - 2 r_2 log B_*`.
The source-exact equation (2.3) remains a named unproved premise in a
conditional theorem that derives the Table 4 interface. Both archimedean
integrals are proved convergent and the strict `A,B` certificate is supplied
by analytic endpoint bounds, verified dyadic interval enclosures, and a
certified Euler–Mascheroni lower bound. The interval calculations use
`native_decide`, whose generated `_native.native_decide.ax_*` dependencies are a distinct trust
boundary from kernel-only reduction. The remaining explicit-formula input is
not asserted as a project axiom or proved source theorem. Its unformalized
content is now localized to the transformed prime-power matching and the
global contour/residue identity; the archimedean specialization is no longer
part of that boundary.

The public Python and Wolfram checks trust their kernels and the extracted v15 input file. The private source-bound checks additionally verify the manuscript hash and printed data. Neither computational PASS counts nor Lean compilation certifies paper-to-code semantic fidelity. Only the active v15 computational artifacts are included in the current package.
