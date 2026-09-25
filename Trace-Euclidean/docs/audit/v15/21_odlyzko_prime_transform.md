# Odlyzko transformed prime-power certificate

This note records the kernel-checked prime side of the explicit-formula
development. The implementation is
`lean/TraceEuclidean/V15OdlyzkoPrimeTransform.lean`.

## Vertical transform

For every fixed real `sigma`, Lean proves a fourth-power bound

~~~text
norm(Phi(sigma + i*t)) <= D / (1 + |t|)^4
~~~

for some nonnegative `D`. Hence `Phi` is integrable on every fixed vertical
line. Fourier inversion for the exponentially tilted source kernel then gives

~~~text
integral_R exp(-i*t*x) * Phi(sigma+i*t) dt
  = 2*pi * exp((sigma-1/2)*x) * F(x).
~~~

The principal declarations are
`v15OdlyzkoPhi_vertical_exists_fourthPowerBound` and
`v15OdlyzkoPhi_vertical_inversion_integral`.

## One Euler term

For a nonzero prime ideal `P` and stored exponent `m`, the Euler term is split
into its fixed amplitude and Fourier phase. Lean then proves

~~~text
integral_R Phi(sigma+i*t) * primePowerLogTerm(P,m,sigma+i*t) dt
  = pi * PrimeTerm(P,m+1).
~~~

This identity is independent of `sigma`; the exponential tilt from the
vertical line cancels exactly against the tilt in Fourier inversion.

## Complete sum and actual zeta

The finite norm balls prove that the type of nonzero prime ideals is
countable. On `sigma > 1`, the exported absolute-summability theorem for the
prime-power logarithmic series supplies a summable family of integral norms.
Lean therefore applies Bochner sum/integral interchange to the complete
double series. Compact support of the source kernel then identifies the result
with the previously proved finite box of norms at most 4095 and exponents at
most eleven:

~~~text
integral_R Phi(sigma+i*t) * sum_(P,m) primePowerLogTerm(P,m,sigma+i*t) dt
  = pi * PrimeCorrection(K).
~~~

Finally, the proved Euler-product logarithmic-derivative identity yields

~~~text
integral_R Phi(sigma+i*t) * (zeta_K'/zeta_K)(sigma+i*t) dt
  = -pi * PrimeCorrection(K).
~~~

The final declarations are
`v15OdlyzkoPhi_mul_primePowerLogTerm_tsum_integral` and
`v15OdlyzkoPhi_mul_logDeriv_dedekindZeta_integral`.

## Trust and remaining boundary

The endpoints use only `propext`, `Classical.choice`, and `Quot.sound`. They do
not use `sorry`, a project axiom, or `native_decide`. The transformed
prime-power matching is therefore closed. The remaining analytic boundary is
the global Stark/Weil contour argument: a weighted logarithmic-derivative
integral for the completed zeta must be identified with the convergent sum of
its zeros, including multiplicity, after the horizontal contour terms are
shown to vanish.
