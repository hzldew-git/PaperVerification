/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import NormEuclidean.Reuse.Bong.Lattice.NumberFieldHasseIsotropyReduction
import NormEuclidean.Reuse.Bong.QuadraticSpace.FieldBinaryIsotropy

/-!
# The Global Square input and rank-two Hasse isotropy

O'Meara 65:15 says that an element of a global field which is a square at
almost all spots is a global square.  Since the infinite spots form a finite
set, its nonzero content is captured by eventual squareness in the cofinite
filter on finite places.  This file keeps that arithmetic theorem as a named
input and proves the complete binary step of O'Meara 66:1 from it.
-/

namespace Bong.HeADCV5.Global

open scoped NumberField TensorProduct

namespace NumberFieldLattice

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- O'Meara 65:15 expressed on the cofinite filter of finite places. -/
def HasCofiniteFinitePlaceGlobalSquare
    (K : Type u) [Field K] [NumberField K] : Prop :=
  ∀ a : K,
    (∀ᶠ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      IsSquare (algebraMap K (p.adicCompletion K) a)) →
    IsSquare a

theorem finiteDiagonal_isIsotropicSpace_iff_diagonalIsotropic
    {F : Type u} [Field F] {n : Nat}
    (a : Fin n → F) (ha : ∀ i, a i ≠ 0) :
    IsIsotropicSpace (Bong.QuadraticSpace.finiteDiagonal a ha) ↔
      DiagonalIsotropic a := by
  simp only [IsIsotropicSpace, DiagonalIsotropic,
    Bong.QuadraticSpace.finiteDiagonal_quadratic_apply]

/-- The binary diagonal case of O'Meara 66:1 follows from the exact
Global Square input. -/
theorem finiteDiagonal_rankTwo_hasse_isotropy_of_globalSquare
    (hSquare : HasCofiniteFinitePlaceGlobalSquare K)
    {n : Nat} (a : Fin n → K) (ha : ∀ i, a i ≠ 0)
    (hRank : n = 2)
    (hFinite : ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      IsIsotropicSpace
        ((Bong.QuadraticSpace.finiteDiagonal a ha).scalarExtension
          (E := p.adicCompletion K))) :
    IsIsotropicSpace (Bong.QuadraticSpace.finiteDiagonal a ha) := by
  subst n
  have hLocalSquare :
      ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        IsSquare (algebraMap K (p.adicCompletion K) (-(a 0 * a 1))) := by
    intro p
    let aE : Fin 2 → p.adicCompletion K :=
      fun i ↦ algebraMap K (p.adicCompletion K) (a i)
    have haE : ∀ i, aE i ≠ 0 := by
      intro i
      exact (map_ne_zero (algebraMap K (p.adicCompletion K))).mpr (ha i)
    have hDiagonalSpace :
        IsIsotropicSpace (Bong.QuadraticSpace.finiteDiagonal aE haE) := by
      exact isIsotropicSpace_map
        (Bong.QuadraticSpace.scalarExtensionFiniteDiagonalIsometry
          (E := p.adicCompletion K) a ha)
        (hFinite p)
    have hDiagonal : DiagonalIsotropic aE :=
      (finiteDiagonal_isIsotropicSpace_iff_diagonalIsotropic aE haE).mp
        hDiagonalSpace
    have hSquareE :=
      (fieldBinary_isotropic_iff_isSquare_neg_product aE haE).mp hDiagonal
    simpa only [aE, map_neg, map_mul] using hSquareE
  have hGlobalSquare : IsSquare (-(a 0 * a 1)) :=
    hSquare (-(a 0 * a 1)) (Filter.Eventually.of_forall hLocalSquare)
  exact (finiteDiagonal_isIsotropicSpace_iff_diagonalIsotropic a ha).mpr
    ((fieldBinary_isotropic_iff_isSquare_neg_product a ha).mpr hGlobalSquare)

/-- The rank-two case of O'Meara 66:1 for an arbitrary regular quadratic
space, with O'Meara 65:15 retained as the sole arithmetic input. -/
theorem rankTwo_hasse_isotropy_of_globalSquare
    (hSquare : HasCofiniteFinitePlaceGlobalSquare K)
    {V : Type u} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (q : Bong.QuadraticSpace K V)
    (hRank : Module.finrank K V = 2)
    (hFinite : ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      IsIsotropicSpace (q.scalarExtension (E := p.adicCompletion K))) :
    IsIsotropicSpace q := by
  let a := q.fieldDiagonalCoefficients
  have ha : ∀ i, a i ≠ 0 := q.fieldDiagonalCoefficients_ne_zero
  have hDiagonalFinite :
      ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        IsIsotropicSpace
          ((Bong.QuadraticSpace.finiteDiagonal a ha).scalarExtension
            (E := p.adicCompletion K)) := by
    intro p
    exact isIsotropicSpace_map
      (q.fieldDiagonalizationIsometry.scalarExtension
        (E := p.adicCompletion K))
      (hFinite p)
  have hDiagonal :=
    finiteDiagonal_rankTwo_hasse_isotropy_of_globalSquare
      hSquare a ha hRank hDiagonalFinite
  exact isIsotropicSpace_map q.fieldDiagonalizationIsometry.symm hDiagonal

end NumberFieldLattice

end Bong.HeADCV5.Global
