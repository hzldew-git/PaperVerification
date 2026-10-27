/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import NormEuclidean.Reuse.Bong.Lattice.NumberFieldQuadraticHasseNorm
import NormEuclidean.Reuse.Bong.QuadraticSpace.FieldQuaternarySquareDeterminant

/-!
# The square-determinant rank-four Hasse isotropy branch

This file proves the square-determinant quaternary branch in O'Meara 66:1.
At every place, O'Meara 42:12 reduces the local quaternary form to its
leading ternary subform. The already isolated quadratic Hasse Norm input then
globalizes that ternary isotropy, and 42:12 lifts it back to rank four.
-/
namespace Bong.HeADCV5.Global

open scoped NumberField TensorProduct

namespace NumberFieldLattice

open Bong.Dyadic

universe u

variable {K : Type u} [Field K] [NumberField K]

private theorem local_prefixDiagonal_of_quaternary_isotropic
    {E : Type u} [Field E] [CharZero E] [Algebra K E]
    (a : Fin 4 → K) (ha : ∀ i, a i ≠ 0)
    (hdet : IsSquare (∏ i, Units.mk0 (a i) (ha i)))
    (hLocal : IsIsotropicSpace
      ((Bong.QuadraticSpace.finiteDiagonal a ha).scalarExtension (E := E))) :
    DiagonalIsotropic (fun i ↦ algebraMap K E
      (Bong.fieldQuaternaryPrefix
        (fun j ↦ Units.mk0 (a j) (ha j)) i : K)) := by
  let aUnits : Fin 4 → Kˣ := fun i ↦ Units.mk0 (a i) (ha i)
  let aE : Fin 4 → E := fun i ↦ algebraMap K E (a i)
  let aEUnits : Fin 4 → Eˣ :=
    fun i ↦ Units.map (algebraMap K E).toMonoidHom (aUnits i)
  have haE : ∀ i, aE i ≠ 0 := by
    intro i
    exact (map_ne_zero (algebraMap K E)).mpr (ha i)
  have hDiagonalSpace :
      IsIsotropicSpace (Bong.QuadraticSpace.finiteDiagonal aE haE) :=
    isIsotropicSpace_map
      (Bong.QuadraticSpace.scalarExtensionFiniteDiagonalIsometry
        (E := E) a ha)
      hLocal
  have hDiagonal : DiagonalIsotropic aE :=
    (finiteDiagonal_isIsotropicSpace_iff_diagonalIsotropic aE haE).mp
      hDiagonalSpace
  have hDiagonalUnits :
      DiagonalIsotropic (fun i ↦ (aEUnits i : E)) := by
    simpa [aE, aEUnits, aUnits] using hDiagonal
  have hdetE : IsSquare (∏ i, aEUnits i) := by
    rcases hdet with ⟨d, hd⟩
    refine ⟨Units.map (algebraMap K E).toMonoidHom d, ?_⟩
    have hmap := congrArg
      (Units.map (algebraMap K E).toMonoidHom) hd
    simpa [aEUnits, aUnits] using hmap
  have hprefix :=
    (Bong.fieldQuaternary_isotropic_iff_prefix_of_square_det
      aEUnits hdetE).mp hDiagonalUnits
  have hcoeff :
      (fun i ↦ (Bong.fieldQuaternaryPrefix aEUnits i : E)) =
        (fun i ↦ algebraMap K E
          (Bong.fieldQuaternaryPrefix aUnits i : K)) := by
    funext i
    fin_cases i <;> simp [aEUnits, aUnits]
  rw [hcoeff] at hprefix
  simpa [aUnits] using hprefix

/-- The square-determinant quaternary branch in the proof of O'Meara 66:1.
It follows from the ternary Hasse step and the field-algebra theorem 42:12. -/
theorem finiteDiagonal_rankFour_squareDet_hasse_isotropy_of_hasseNorm
    (hNorm : HasQuadraticHasseNorm K)
    {n : Nat} (a : Fin n → K) (ha : ∀ i, a i ≠ 0)
    (hRank : n = 4)
    (hdet : IsSquare (∏ i, Units.mk0 (a i) (ha i)))
    (hFinite : ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      IsIsotropicSpace
        ((Bong.QuadraticSpace.finiteDiagonal a ha).scalarExtension
          (E := p.adicCompletion K)))
    (hInfinite : ∀ p : NumberField.InfinitePlace K,
      IsIsotropicSpace
        ((Bong.QuadraticSpace.finiteDiagonal a ha).scalarExtension
          (E := p.Completion))) :
    IsIsotropicSpace (Bong.QuadraticSpace.finiteDiagonal a ha) := by
  subst n
  let aUnits : Fin 4 → Kˣ := fun i ↦ Units.mk0 (a i) (ha i)
  let b : Fin 3 → K := fun i ↦
    (Bong.fieldQuaternaryPrefix aUnits i : K)
  have hb : ∀ i, b i ≠ 0 := by
    intro i
    exact Units.ne_zero (Bong.fieldQuaternaryPrefix aUnits i)
  have hFinitePrefix :
      ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        IsIsotropicSpace
          ((Bong.QuadraticSpace.finiteDiagonal b hb).scalarExtension
            (E := p.adicCompletion K)) := by
    intro p
    let bE : Fin 3 → p.adicCompletion K :=
      fun i ↦ algebraMap K (p.adicCompletion K) (b i)
    have hbE : ∀ i, bE i ≠ 0 := by
      intro i
      exact (map_ne_zero (algebraMap K (p.adicCompletion K))).mpr (hb i)
    have hDiagonal : DiagonalIsotropic bE := by
      simpa [bE, b, aUnits] using
        (local_prefixDiagonal_of_quaternary_isotropic
          a ha hdet (hFinite p))
    have hDiagonalSpace :
        IsIsotropicSpace (Bong.QuadraticSpace.finiteDiagonal bE hbE) :=
      (finiteDiagonal_isIsotropicSpace_iff_diagonalIsotropic bE hbE).mpr
        hDiagonal
    exact isIsotropicSpace_map
      (Bong.QuadraticSpace.scalarExtensionFiniteDiagonalIsometry
        (E := p.adicCompletion K) b hb).symm
      hDiagonalSpace
  have hInfinitePrefix :
      ∀ p : NumberField.InfinitePlace K,
        IsIsotropicSpace
          ((Bong.QuadraticSpace.finiteDiagonal b hb).scalarExtension
            (E := p.Completion)) := by
    intro p
    letI : CharZero p.Completion :=
      Algebra.charZero_of_charZero K p.Completion
    let bE : Fin 3 → p.Completion :=
      fun i ↦ algebraMap K p.Completion (b i)
    have hbE : ∀ i, bE i ≠ 0 := by
      intro i
      exact (map_ne_zero (algebraMap K p.Completion)).mpr (hb i)
    have hDiagonal : DiagonalIsotropic bE := by
      simpa [bE, b, aUnits] using
        (local_prefixDiagonal_of_quaternary_isotropic
          a ha hdet (hInfinite p))
    have hDiagonalSpace :
        IsIsotropicSpace (Bong.QuadraticSpace.finiteDiagonal bE hbE) :=
      (finiteDiagonal_isIsotropicSpace_iff_diagonalIsotropic bE hbE).mpr
        hDiagonal
    exact isIsotropicSpace_map
      (Bong.QuadraticSpace.scalarExtensionFiniteDiagonalIsometry
        (E := p.Completion) b hb).symm
      hDiagonalSpace
  have hPrefixSpace :=
    finiteDiagonal_rankThree_hasse_isotropy_of_hasseNorm
      hNorm b hb rfl hFinitePrefix hInfinitePrefix
  have hPrefix : DiagonalIsotropic b :=
    (finiteDiagonal_isIsotropicSpace_iff_diagonalIsotropic b hb).mp
      hPrefixSpace
  have hPrefixUnits :
      DiagonalIsotropic
        (fun i ↦ (Bong.fieldQuaternaryPrefix aUnits i : K)) := by
    simpa [b] using hPrefix
  have hFullUnits : DiagonalIsotropic (fun i ↦ (aUnits i : K)) :=
    (Bong.fieldQuaternary_isotropic_iff_prefix_of_square_det
      aUnits (by simpa [aUnits] using hdet)).mpr hPrefixUnits
  apply (finiteDiagonal_isIsotropicSpace_iff_diagonalIsotropic a ha).mpr
  simpa [aUnits] using hFullUnits

/-- The square-determinant rank-four case of O'Meara 66:1 for an arbitrary
regular quadratic space. -/
theorem rankFour_squareDet_hasse_isotropy_of_hasseNorm
    (hNorm : HasQuadraticHasseNorm K)
    {V : Type u} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (q : Bong.QuadraticSpace K V)
    (hRank : Module.finrank K V = 4)
    (hdet : IsSquare
      (∏ i, Bong.QuadraticSpace.fieldDiagonalUnits q i))
    (hFinite : ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      IsIsotropicSpace (q.scalarExtension (E := p.adicCompletion K)))
    (hInfinite : ∀ p : NumberField.InfinitePlace K,
      IsIsotropicSpace (q.scalarExtension (E := p.Completion))) :
    IsIsotropicSpace q := by
  let a := q.fieldDiagonalCoefficients
  have ha : ∀ i, a i ≠ 0 := q.fieldDiagonalCoefficients_ne_zero
  have hdetA : IsSquare (∏ i, Units.mk0 (a i) (ha i)) := by
    simpa [a, ha, Bong.QuadraticSpace.fieldDiagonalUnits] using hdet
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
  have hDiagonalInfinite :
      ∀ p : NumberField.InfinitePlace K,
        IsIsotropicSpace
          ((Bong.QuadraticSpace.finiteDiagonal a ha).scalarExtension
            (E := p.Completion)) := by
    intro p
    exact isIsotropicSpace_map
      (q.fieldDiagonalizationIsometry.scalarExtension (E := p.Completion))
      (hInfinite p)
  have hDiagonal :=
    finiteDiagonal_rankFour_squareDet_hasse_isotropy_of_hasseNorm
      hNorm a ha hRank hdetA hDiagonalFinite hDiagonalInfinite
  exact isIsotropicSpace_map q.fieldDiagonalizationIsometry.symm hDiagonal

end NumberFieldLattice

end Bong.HeADCV5.Global
