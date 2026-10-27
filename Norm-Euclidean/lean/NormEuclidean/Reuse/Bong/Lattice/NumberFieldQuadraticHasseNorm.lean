/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import NormEuclidean.Reuse.Bong.Lattice.NumberFieldGlobalSquare
import NormEuclidean.Reuse.Bong.QuadraticSpace.FieldTernaryHasseNorm

/-!
# The quadratic Hasse Norm input and rank-three Hasse isotropy

O'Meara 65:23 is the Hasse Norm Theorem for a quadratic extension.  This
file records its exact all-place consequence as an ordinary proposition and
proves the complete ternary step of O'Meara 66:1 from that input.
-/

open scoped Bong.HeADCV5.Global

namespace Bong.HeADCV5.Global

open scoped NumberField TensorProduct

namespace NumberFieldLattice

open Bong.Dyadic

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- O'Meara 65:23 for the quadratic extension determined by a nonsquare
parameter, expressed through its norm equation at every finite and infinite
place. -/
def HasQuadraticHasseNorm
    (K : Type u) [Field K] [NumberField K] : Prop :=
  ∀ (theta alpha : Kˣ),
    ¬ IsSquare theta →
    (∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      IsQuadraticNorm (p.adicCompletion K)
        (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta)
        (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom alpha)) →
    (∀ p : NumberField.InfinitePlace K,
      IsQuadraticNorm p.Completion
        (Units.map (algebraMap K p.Completion).toMonoidHom theta)
        (Units.map (algebraMap K p.Completion).toMonoidHom alpha)) →
    IsQuadraticNorm K theta alpha

omit [NumberField K] in
private theorem mapped_fieldTernaryNormTheta
    {E : Type u} [Field E] [Algebra K E]
    (a : Fin 3 → Kˣ) :
    fieldTernaryNormTheta
        (fun i ↦ Units.map (algebraMap K E).toMonoidHom (a i)) =
      Units.map (algebraMap K E).toMonoidHom
        (fieldTernaryNormTheta a) := by
  apply Units.ext
  simp [fieldTernaryNormTheta]

omit [NumberField K] in
private theorem mapped_fieldTernaryNormAlpha
    {E : Type u} [Field E] [Algebra K E]
    (a : Fin 3 → Kˣ) :
    fieldTernaryNormAlpha
        (fun i ↦ Units.map (algebraMap K E).toMonoidHom (a i)) =
      Units.map (algebraMap K E).toMonoidHom
        (fieldTernaryNormAlpha a) := by
  apply Units.ext
  simp [fieldTernaryNormAlpha]

private theorem local_norm_of_finiteDiagonal_isotropic
    {E : Type u} [Field E] [CharZero E] [Algebra K E]
    (a : Fin 3 → K) (ha : ∀ i, a i ≠ 0)
    (hLocal : IsIsotropicSpace
      ((Bong.QuadraticSpace.finiteDiagonal a ha).scalarExtension (E := E))) :
    IsQuadraticNorm E
      (Units.map (algebraMap K E).toMonoidHom
        (fieldTernaryNormTheta (fun i ↦ Units.mk0 (a i) (ha i))))
      (Units.map (algebraMap K E).toMonoidHom
        (fieldTernaryNormAlpha (fun i ↦ Units.mk0 (a i) (ha i)))) := by
  let aE : Fin 3 → E := fun i ↦ algebraMap K E (a i)
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
  let aUnits : Fin 3 → Kˣ := fun i ↦ Units.mk0 (a i) (ha i)
  let aEUnits : Fin 3 → Eˣ :=
    fun i ↦ Units.map (algebraMap K E).toMonoidHom (aUnits i)
  have hDiagonalUnits : DiagonalIsotropic (fun i ↦ (aEUnits i : E)) := by
    simpa [aE, aEUnits, aUnits] using hDiagonal
  have hNorm :=
    (fieldTernary_isotropic_iff_isQuadraticNorm aEUnits).mp
      hDiagonalUnits
  rw [mapped_fieldTernaryNormTheta aUnits,
    mapped_fieldTernaryNormAlpha aUnits] at hNorm
  exact hNorm

/-- The ternary diagonal case of O'Meara 66:1 follows from the quadratic
Hasse Norm Theorem. -/
theorem finiteDiagonal_rankThree_hasse_isotropy_of_hasseNorm
    (hNorm : HasQuadraticHasseNorm K)
    {n : Nat} (a : Fin n → K) (ha : ∀ i, a i ≠ 0)
    (hRank : n = 3)
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
  let aUnits : Fin 3 → Kˣ := fun i ↦ Units.mk0 (a i) (ha i)
  by_cases htheta : IsSquare (fieldTernaryNormTheta aUnits)
  · have hGlobalNorm : IsQuadraticNorm K
        (fieldTernaryNormTheta aUnits)
        (fieldTernaryNormAlpha aUnits) :=
      isQuadraticNorm_of_isSquare_left K htheta
    apply (finiteDiagonal_isIsotropicSpace_iff_diagonalIsotropic a ha).mpr
    have hDiagonalUnits :
        DiagonalIsotropic (fun i ↦ (aUnits i : K)) :=
      (fieldTernary_isotropic_iff_isQuadraticNorm aUnits).mpr hGlobalNorm
    simpa [aUnits] using hDiagonalUnits
  · have hFiniteNorm :
        ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          IsQuadraticNorm (p.adicCompletion K)
            (Units.map
              (algebraMap K (p.adicCompletion K)).toMonoidHom
              (fieldTernaryNormTheta aUnits))
            (Units.map
              (algebraMap K (p.adicCompletion K)).toMonoidHom
              (fieldTernaryNormAlpha aUnits)) := by
      intro p
      exact local_norm_of_finiteDiagonal_isotropic a ha (hFinite p)
    have hInfiniteNorm :
        ∀ p : NumberField.InfinitePlace K,
          IsQuadraticNorm p.Completion
            (Units.map (algebraMap K p.Completion).toMonoidHom
              (fieldTernaryNormTheta aUnits))
            (Units.map (algebraMap K p.Completion).toMonoidHom
              (fieldTernaryNormAlpha aUnits)) := by
      intro p
      letI : CharZero p.Completion :=
        Algebra.charZero_of_charZero K p.Completion
      exact local_norm_of_finiteDiagonal_isotropic a ha (hInfinite p)
    have hGlobalNorm := hNorm
      (fieldTernaryNormTheta aUnits)
      (fieldTernaryNormAlpha aUnits)
      htheta hFiniteNorm hInfiniteNorm
    apply (finiteDiagonal_isIsotropicSpace_iff_diagonalIsotropic a ha).mpr
    have hDiagonalUnits :
        DiagonalIsotropic (fun i ↦ (aUnits i : K)) :=
      (fieldTernary_isotropic_iff_isQuadraticNorm aUnits).mpr hGlobalNorm
    simpa [aUnits] using hDiagonalUnits

/-- The rank-three case of O'Meara 66:1 for an arbitrary regular quadratic
space, with O'Meara 65:23 retained as the sole arithmetic input. -/
theorem rankThree_hasse_isotropy_of_hasseNorm
    (hNorm : HasQuadraticHasseNorm K)
    {V : Type u} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (q : Bong.QuadraticSpace K V)
    (hRank : Module.finrank K V = 3)
    (hFinite : ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      IsIsotropicSpace (q.scalarExtension (E := p.adicCompletion K)))
    (hInfinite : ∀ p : NumberField.InfinitePlace K,
      IsIsotropicSpace (q.scalarExtension (E := p.Completion))) :
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
    finiteDiagonal_rankThree_hasse_isotropy_of_hasseNorm
      hNorm a ha hRank hDiagonalFinite hDiagonalInfinite
  exact isIsotropicSpace_map q.fieldDiagonalizationIsometry.symm hDiagonal

end NumberFieldLattice

end Bong.HeADCV5.Global
