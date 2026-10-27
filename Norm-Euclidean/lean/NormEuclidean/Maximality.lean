import NormEuclidean.NumberField

/-!
# Direct maximality of norm-Euclidean integral lattices

The argument in the proof of Corollary `cor:rank-degree-bounds` only needs
anisotropy, approximation, and integrality of an overmodule. In particular,
neither freeness nor finite generation of the overmodule is required.
-/

namespace NormEuclidean

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {R : Subring K} (N : IntegralNorm R)

/-- A nonzero integral scalar has absolute norm at least one. -/
theorem IntegralNorm.one_le_of_integral {a : K} (ha : a ∈ R) (ha0 : a ≠ 0) :
    1 ≤ N.norm a := by
  have hpos : 0 < N.measure a := by
    exact_mod_cast (show (0 : ℚ) < N.measure a by
      rw [N.measure_spec a ha]
      exact N.pos a ha0)
  rw [← N.measure_spec a ha]
  exact_mod_cast hpos

/-- Every integral overmodule of an anisotropic norm-Euclidean submodule
is equal to it. This is the direct maximality argument from the manuscript. -/
theorem normEuclidean_eq_integral_overmodule
    (Q : QuadraticForm K V) (L M : Submodule R V)
    (hA : Q.Anisotropic) (hE : IsNormEuclidean N Q L)
    (hLM : L ≤ M) (hM : ∀ x ∈ M, Q x ∈ R) : L = M := by
  apply le_antisymm hLM
  intro x hx
  obtain ⟨u, hu, happ⟩ := hE x
  have hxu : x = u := by
    by_contra hne
    have hQne : Q (x - u) ≠ 0 := fun h => hne (sub_eq_zero.mp (hA _ h))
    have hbound := N.one_le_of_integral (hM _ (M.sub_mem hx (hLM hu))) hQne
    exact (not_lt_of_ge hbound) happ
  simpa [hxu] using hu

variable [NumberField K]

/-- Number-field endpoint: a finite full integral norm-Euclidean lattice
is maximal among all integral submodules of the same quadratic space. -/
theorem numberField_normEuclidean_maximal
    (Q : QuadraticForm K V) (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (M : Submodule (integerSubring K) V) (hLM : L.carrier ≤ M)
    (hM : ∀ x ∈ M, Q x ∈ integerSubring K) : L.carrier = M :=
  normEuclidean_eq_integral_overmodule (numberFieldNorm K) Q L.carrier M hA hE hLM hM

/-- In particular no proper integral superlattice exists. -/
theorem numberField_no_proper_integral_superlattice
    (Q : QuadraticForm K V) (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (M : Lattice (integerSubring K) Q) : ¬ L.carrier < M.carrier := by
  intro h
  exact h.ne (numberField_normEuclidean_maximal Q L hA hE M.carrier h.le M.integral)

end NormEuclidean
