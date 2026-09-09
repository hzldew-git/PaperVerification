# Paper theorem inventory

The inventory below summarizes the target manuscript without reproducing its
source. Every lattice is assumed positive definite and integral unless the row
states the classic-integral refinement.

| ID | Paper item | Essential hypotheses and quantified conclusion |
|---|---|---|
| P01 | Definition 1.1 | For fixed real `t>0`, trace Euclideanity requires `forall x in V, exists y in L` with strict trace cost below `t`; house Euclideanity uses strict house cost below one. |
| P02 | Theorem 1.2(i) | Fixed `t`, fixed degree `d>=t`, and rank `n=1` or `2`: finitely many classic-integral pairs as the totally real field varies. |
| P03 | Theorem 1.2(ii) | Fixed `t` and fixed rank `n>=3`: finitely many classic-integral pairs while both field and degree may vary, subject to `d>=t`. |
| P04 | Theorem 1.2(iii) | Fixed `t` and fixed degree `d>=t`: finitely many classic-integral pairs of arbitrary rank. |
| P05 | Theorem 1.2(iv) | Fixed `t`: finitely many classic-integral pairs with `n>=3` while field, degree, and rank vary, subject to `d>=t`. |
| P06 | Theorem 1.3(i) | Fixed `t`, fixed degree `d>=t`, and rank `n in {1,2,3,4}`: finitely many integral pairs. |
| P07 | Theorem 1.3(ii) | Fixed `t` and fixed rank `n>=5`: finitely many integral pairs while the totally real field varies. |
| P08 | Theorem 1.3(iii) | Fixed `t` and fixed degree `d>=t`: finitely many integral pairs of arbitrary rank. |
| P09 | Theorem 1.3(iv) | Fixed `t`: finitely many integral pairs with `n>=5` while field, degree, and rank vary. |
| P10 | Definition 1.5 | `p`-norm Euclideanity has quantifier order `forall x, exists y` and the strict inequality `M_p(x,y)<1`. |
| P11 | Corollary 1.6 | For every `p in [1,infinity]`, each assertion of Theorems 1.2 and 1.3 remains valid after replacing trace Euclideanity by `p`-norm Euclideanity; the proof uses `t=d` uniformly. |
| P12 | Definition 1.7 | A totally real field of degree `d` is `t`-trace Euclidean when `0<t<=d` and every field element has an integer translate with strict trace-square cost below `t`. |
| P13 | Theorem 1.8 | For square-free `m>1`, the real quadratic field `Q(sqrt m)` is 2-trace Euclidean exactly for `m in {2,5,13}`. |
| P14 | Lemma 2.1 | The periodic minimum function `Phi_R` is lattice-periodic and continuous, attains its supremum modulo the full lattice, and has the same supremum as the rational-space function. |
| P15 | Lemma 2.2 | `rho_T(L)<=t` is equivalent to the pointwise non-strict approximation condition; moreover `rho_T(L)<t` implies strict trace Euclideanity, which implies `rho_T(L)<=t`. |
| P16 | Lemma 3.1 | The trace Gram determinant is expressed through the field discriminant and the norm of the lattice volume ideal. |
| P17 | Lemma 3.2 | The covolume of the Minkowski lattice is `Delta_F^(n/2) sqrt(N(v(L)))`. |
| P18 | Lemma 3.3 | The lattice covolume is bounded above by the Euclidean ball-volume constant times a power of the trace covering radius. |
| P19 | Lemma 3.4 | Trace Euclideanity yields explicit bounds involving discriminant, volume, scale, norm, and the function `G_t(n,d)`. |
| P20 | Lemma 4.1 | For fixed `y`, `g(x,y)` is strictly concave in `x), with a threshold controlling its unique maximum. |
| P21 | Lemma 4.2 | For fixed `x`, the `y`-behavior of `g` is classified by the sign threshold `2 pi/e` and a unique root `x_0`. |
| P22 | Lemma 4.3 | The global maximum of `g` on `x>=3,y>=1` lies on the `y=1` boundary; the proof excludes interior maxima by a negative Hessian determinant and compares certified boundary values. |
| P23 | Lemma 4.4 | For fixed `y>=1`, `g_s(x,y)` is strictly decreasing for `x>=3`. |
| P24 | Lemma 4.5 | The `y`-derivative of `g_s` transfers from that of `g`. |
| P25 | Lemma 4.6 | The maximum of `g_s` on `x>=3,y>=1` occurs at the rank-three boundary and its stated critical point. |
| P26 | Lemma 4.7 | For fixed `y>=1`, `g_n(x,y)` is strictly decreasing for `x>=5`. |
| P27 | Lemma 4.8 | For fixed `x`, the `y`-behavior of `g_n` is classified by `4 pi/e` and a unique threshold `x_n`. |
| P28 | Lemma 4.9 | The maximum of `g_n` on `x>=5,y>=1` occurs at the rank-five boundary and its stated critical point. |
| P29 | Lemma 5.1 | For fixed rank, degree, discriminant bound, and volume--ideal norm bound, only finitely many equivalence classes of field-lattice pairs occur. |
| P30 | Proposition 6.1 | For square-free `m>1`, the squared covering radius is `(m+1)/2` for `m congruent 2 or 3 mod 4`, and `(m+1)^2/(8m)` for `m congruent 1 mod 4`. |

The field-varying finiteness rows use equivalence of pairs through a field
isomorphism and a compatible semilinear lattice isometry. That equivalence is
part of the paper statement and must not be replaced by same-field linear
isometry in a complete formalization.
