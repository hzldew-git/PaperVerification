import NormEuclidean.ChapterX.VolumeIdeal

/-!
# Finite volume-ideal intervals

This proves the ideal-interval reduction in 103:3 step 1, using the actual
finite-quotient property of the number-field integer ring. It does not
assert class finiteness or bounded represented-value coverage.
-/

noncomputable section

namespace NormEuclidean.IntegralVolume

open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- Between a fixed nonzero fractional ideal and the integer ring there
are only finitely many actual fractional ideals. No class group input is used. -/
theorem finite_integral_ideals_containing (c : FractionalIdeal (integerSubring K)⁰ K)
    (hc : c ≠ 0) :
    {I : FractionalIdeal (integerSubring K)⁰ K | c ≤ I ∧ I ≤ 1}.Finite := by
  letI : Ring.HasFiniteQuotients (integerSubring K) :=
    inferInstanceAs (Ring.HasFiniteQuotients (NumberField.RingOfIntegers K))
  have hcFull : Submodule.span K (c.coeToSubmodule : Set K) = ⊤ :=
    (NumberFieldLatticeModule.fractionalIdeal_isLattice c hc).span_eq_top
  have hfg : ((1 : FractionalIdeal (integerSubring K)⁰ K) :
      Submodule (integerSubring K) K).FG :=
    FractionalIdeal.fg_of_isUnit _ (by simp)
  have hinterval := LatticeInterval.finite_interval_of_full (integerSubring K)
    c.coeToSubmodule ((1 : FractionalIdeal (integerSubring K)⁰ K) :
      Submodule (integerSubring K) K) hcFull hfg
  apply Set.Finite.of_injOn (f := fun I : FractionalIdeal (integerSubring K)⁰ K ↦
    I.coeToSubmodule)
    (t := {M : Submodule (integerSubring K) K | c.coeToSubmodule ≤ M ∧
      M ≤ ((1 : FractionalIdeal (integerSubring K)⁰ K) : Submodule (integerSubring K) K)})
  · intro I hI
    exact hI
  · exact FractionalIdeal.coeToSubmodule_injective.injOn
  · exact hinterval

/-- Integral-scale lattices in the source bounded-volume family have only
finitely many possible actual volumes. This is not lattice-class finiteness. -/
theorem finite_volumeIdeals_of_lower_bound {V : Type*} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (c : FractionalIdeal (integerSubring K)⁰ K) (hc : c ≠ 0) :
    {I : FractionalIdeal (integerSubring K)⁰ K |
      ∃ L : Lattice (integerSubring K) Q, L.scaleIdeal ≤ 1 ∧ c ≤ L.volumeIdeal ∧
        L.volumeIdeal = I}.Finite := by
  apply (finite_integral_ideals_containing c hc).subset
  rintro I ⟨L, hs, hvol, rfl⟩
  exact ⟨hvol, L.volumeIdeal_le_one hs⟩

end NormEuclidean.IntegralVolume
