# Trace-Euclidean v15: paper claim inventory

Source: `source/Trace-Euclidean-v15.tex`, SHA-256
`83a236e93648ce0802f8a0d3022de63710d089f3a4f7e61214a4c855459597b5`.
This inventory is extracted from the paper. Formal declarations and their
correspondence are recorded separately.

| Paper anchor | Claim to preserve in formalization |
| --- | --- |
| `defn:trace-Euclidean` | For a positive definite integral lattice over a totally real field of degree `d`, trace Euclideanity means that every vector in the ambient `F`-space has a lattice approximation with `Tr(Q(x-y)) < d`. House Euclideanity has the analogous house threshold `1`. |
| `thm:finiteness-classic` | As the totally real field and positive rank both vary, the classic integral trace Euclidean lattices form finitely many isometry classes, and each satisfies `n Δ_F^(1/d) < 2πe`. |
| `thm:finiteness-integral` | The same global finiteness assertion for integral lattices, with `n Δ_F^(1/d) < 4πe`. |
| `defn:p-norm`, `cor:p-norm` | For every fixed `p ∈ [1,∞]`, the integral `p`-norm Euclidean lattices of arbitrary positive rank and varying totally real field form finitely many isometry classes. |
| `thm:rank-one-classification` | For every square-free `m>1`, every positive definite integral rank-one lattice over `F=ℚ(√m)` is trace Euclidean exactly when it is `F`-isometric to one of the six listed pairs `(m,a)`: `(2,1)`, `(3,2+√3)`, `(5,1)`, `(5,2)`, `(13,1)`, `(21,(5+√21)/2)`. Every such lattice is free; the six classes are distinct. The input includes nonprincipal fractional ideals. |
| `defn:trace-euclidean-field`, `cor:trace-euclidean-quadratic` | A totally real field is trace Euclidean when its integer ring with square form meets the strict trace threshold. For square-free `m>1`, `ℚ(√m)` has this property exactly for `m∈{2,5,13}`. |
| `lem:Phi`, `lem:phi-Euclidean-trace` | The trace inhomogeneous minimum is the squared covering radius, and strict trace Euclideanity is equivalent to the squared radius being strictly below the field degree. The argument uses rational attainment; density alone does not justify the strict inequality. |
| `lem:gram-det`, `lem:covolume-formula`, `lem:covering-volume-inequality`, `lem:discriminant-norm-bound` | The determinant, covolume, covering-volume, and volume-ideal bounds apply to full projective lattices, including nonfree lattices. The ambient real dimension is `nd`. |
| `lem:root-discriminant-bound`, `lem:discriminant-lower-bounds`, `cor:finite-grid` | The Gamma and discriminant estimates yield the strict root-discriminant bounds and a finite candidate grid `1≤n≤34`, `1≤d≤14`. Analytic and tabulated source bounds must be identified explicitly. |
| `lem:bounded-discriminant-volume-finiteness` | Bounded field discriminant, fixed rank and degree, and bounded volume-ideal norm imply finiteness of the relevant lattice isometry classes, allowing the ambient quadratic spaces to vary. |
| `prop:trace-euclidean-quadratic` | The exact binary covering-radius formulas hold for arbitrary rank-one fractional ideal lattices after choosing a reduced integral trace Gram basis. |

The paper's proof of `thm:rank-one-classification` first bounds reduced Gram
triples, obtains 22 triples and 9 field candidates, applies a trace/norm/index
identity to eliminate 3 candidates and prove that each survivor is free, then
constructs 6 representatives with exact radii below `2`. Each step is a
separate formal or computational obligation; the finite enumeration alone does
not prove the classification of all fractional-ideal lattices.
