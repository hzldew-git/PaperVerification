/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import NormEuclidean.Reuse.Bong.Lattice.NumberFieldPlaceExtension
import NormEuclidean.Reuse.Bong.Lattice.NumberFieldQuaternarySquareDeterminant
import NormEuclidean.Reuse.Bong.QuadraticSpace.FieldQuaternaryDiscriminantDescent

/-!
# The arbitrary-discriminant rank-four Hasse step

This file completes step 4 in O'Meara 66:1. The square-discriminant branch
uses 42:12. In the nonsquare branch, the form is extended to its
discriminant quadratic field, local isotropy is transported to every place
of that field, and the square-discriminant branch is applied there. O'Meara
58:7 then descends isotropy to the original field.
-/

namespace Bong.HeADCV5.Global.NumberFieldLattice

open scoped NumberField TensorProduct
open Bong
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum

universe u

/-- The quadratic Hasse Norm theorem, uniformly for every number field in
the working universe. -/
def HasUniversalQuadraticHasseNorm : Prop :=
  ∀ (E : Type u) [Field E] [NumberField E],
    HasQuadraticHasseNorm E

theorem isSquare_unit_iff_isSquare_coe
    {F : Type u} [Field F] (a : Fˣ) :
    IsSquare a ↔ IsSquare (a : F) := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨(b : F), ?_⟩
    exact congrArg Units.val hb
  · rintro ⟨x, hx⟩
    have hxne : x ≠ 0 := by
      intro hx0
      subst x
      simp only [zero_mul] at hx
      exact Units.ne_zero a hx
    refine ⟨Units.mk0 x hxne, ?_⟩
    apply Units.ext
    exact hx

/-- The product of the four mapped coefficients is a square in the
discriminant quadratic field. -/
theorem discriminantExtension_mappedProduct_isSquare
    {F : Type u} [Field F] (a : Fin 4 → Fˣ)
    (hnotSquare : ¬ IsSquare
      (fieldQuaternaryDiscriminantUnit a : F)) :
    letI : Field (QuadraticAlgebra F
      (fieldQuaternaryDiscriminantUnit a : F) 0) :=
      fieldQuaternaryDiscriminantExtensionField a hnotSquare
    IsSquare (∏ i, Units.map
      (algebraMap F (QuadraticAlgebra F
        (fieldQuaternaryDiscriminantUnit a : F) 0)).toMonoidHom
      (a i)) := by
  let E := QuadraticAlgebra F
    (fieldQuaternaryDiscriminantUnit a : F) 0
  letI : Field E :=
    fieldQuaternaryDiscriminantExtensionField a hnotSquare
  let s : E := fieldQuaternaryDiscriminantSqrt a
  have hs : s ≠ 0 := by
    intro hs0
    have hsq := fieldQuaternaryDiscriminantSqrt_sq a
    rw [show fieldQuaternaryDiscriminantSqrt a = 0 from hs0,
      zero_pow (by decide : (2 : Nat) ≠ 0)] at hsq
    have hCne : (QuadraticAlgebra.C
        (fieldQuaternaryDiscriminantUnit a : F) : E) ≠ 0 := by
      intro h
      exact Units.ne_zero (fieldQuaternaryDiscriminantUnit a) (by
        simpa using congrArg QuadraticAlgebra.re h)
    exact hCne hsq.symm
  refine ⟨Units.mk0 s hs, ?_⟩
  apply Units.ext
  change (∏ i, algebraMap F E (a i : F)) = s * s
  rw [← pow_two, show s ^ 2 = QuadraticAlgebra.C
      (fieldQuaternaryDiscriminantUnit a : F) from
    fieldQuaternaryDiscriminantSqrt_sq a]
  calc
    (∏ i, algebraMap F E (a i : F)) =
        algebraMap F E (∏ i, (a i : F)) := by
      rw [map_prod]
    _ = algebraMap F E
        (fieldQuaternaryDiscriminantUnit a : F) := by
      simp [fieldQuaternaryDiscriminantUnit]
    _ = QuadraticAlgebra.C
        (fieldQuaternaryDiscriminantUnit a : F) := rfl

/-- The nonsquare-discriminant rank-four Hasse step in diagonal
coordinates. -/
theorem finiteDiagonal_rankFour_hasse_isotropy_of_discriminantExtension
    {K : Type u} [Field K] [NumberField K]
    (hNorm : HasUniversalQuadraticHasseNorm.{u})
    (a : Fin 4 → Kˣ)
    (hnotSquare : ¬ IsSquare
      (fieldQuaternaryDiscriminantUnit a : K))
    (hFinite : ∀ p : HeightOneSpectrum (𝓞 K),
      IsIsotropicSpace
        ((QuadraticSpace.finiteDiagonal
          (fun i ↦ (a i : K))
          (fun i ↦ Units.ne_zero (a i))).scalarExtension
            (E := p.adicCompletion K)))
    (hInfinite : ∀ p : NumberField.InfinitePlace K,
      IsIsotropicSpace
        ((QuadraticSpace.finiteDiagonal
          (fun i ↦ (a i : K))
          (fun i ↦ Units.ne_zero (a i))).scalarExtension
            (E := p.Completion))) :
    DiagonalIsotropic (fun i ↦ (a i : K)) := by
  let coeffK : Fin 4 → K := fun i ↦ (a i : K)
  have hcoeffK : ∀ i, coeffK i ≠ 0 :=
    fun i ↦ Units.ne_zero (a i)
  let qK := QuadraticSpace.finiteDiagonal coeffK hcoeffK
  let E := QuadraticAlgebra K
    (fieldQuaternaryDiscriminantUnit a : K) 0
  letI : Field E :=
    fieldQuaternaryDiscriminantExtensionField a hnotSquare
  letI : NumberField E := NumberField.of_module_finite K E
  let coeffE : Fin 4 → E :=
    fun i ↦ algebraMap K E (a i : K)
  have hcoeffE : ∀ i, coeffE i ≠ 0 := by
    intro i
    exact (map_ne_zero (algebraMap K E)).mpr
      (Units.ne_zero (a i))
  have hdetE : IsSquare
      (∏ i, Units.mk0 (coeffE i) (hcoeffE i)) := by
    have hunit (i : Fin 4) :
        Units.mk0 (coeffE i) (hcoeffE i) =
          Units.map (algebraMap K E).toMonoidHom (a i) := by
      apply Units.ext
      rfl
    simpa only [hunit] using
      (discriminantExtension_mappedProduct_isSquare a hnotSquare)
  let qE := QuadraticSpace.finiteDiagonal coeffE hcoeffE
  let baseChangeIsometry : QuadraticSpace.Isometry
      (qK.scalarExtension (E := E)) qE :=
    QuadraticSpace.scalarExtensionFiniteDiagonalIsometry
      (E := E) coeffK hcoeffK
  have hFiniteE : ∀ w : HeightOneSpectrum (𝓞 E),
      IsIsotropicSpace
        (qE.scalarExtension (E := w.adicCompletion E)) := by
    intro w
    let v : HeightOneSpectrum (𝓞 K) := w.under (𝓞 K)
    have hBase : IsIsotropicSpace
        (qK.scalarExtension (E := v.adicCompletion K)) := by
      simpa [qK, coeffK, hcoeffK, v] using hFinite v
    have hDirect : IsIsotropicSpace
        (qK.scalarExtension (E := w.adicCompletion E)) :=
      Bong.numberField_finitePlace_isotropic_of_under qK w hBase
    have hIterated : IsIsotropicSpace
        ((qK.scalarExtension (E := E)).scalarExtension
          (E := w.adicCompletion E)) :=
      isIsotropicSpace_map
        (qK.scalarExtensionTowerIsometry
          (E := E) (L := w.adicCompletion E)).symm hDirect
    exact isIsotropicSpace_map
      (baseChangeIsometry.scalarExtension
        (E := w.adicCompletion E)) hIterated
  have hInfiniteE : ∀ w : NumberField.InfinitePlace E,
      IsIsotropicSpace
        (qE.scalarExtension (E := w.Completion)) := by
    intro w
    let v : NumberField.InfinitePlace K :=
      w.comap (algebraMap K E)
    have hBase : IsIsotropicSpace
        (qK.scalarExtension (E := v.Completion)) := by
      simpa [qK, coeffK, hcoeffK, v] using hInfinite v
    have hDirect : IsIsotropicSpace
        (qK.scalarExtension (E := w.Completion)) :=
      Bong.numberField_infinitePlace_isotropic_of_comap qK w hBase
    have hIterated : IsIsotropicSpace
        ((qK.scalarExtension (E := E)).scalarExtension
          (E := w.Completion)) :=
      isIsotropicSpace_map
        (qK.scalarExtensionTowerIsometry
          (E := E) (L := w.Completion)).symm hDirect
    exact isIsotropicSpace_map
      (baseChangeIsometry.scalarExtension
        (E := w.Completion)) hIterated
  have hIsoE : IsIsotropicSpace qE :=
    finiteDiagonal_rankFour_squareDet_hasse_isotropy_of_hasseNorm
      (hNorm E) coeffE hcoeffE rfl hdetE hFiniteE hInfiniteE
  have hDiagonalE : DiagonalIsotropic coeffE :=
    (finiteDiagonal_isIsotropicSpace_iff_diagonalIsotropic
      coeffE hcoeffE).mp hIsoE
  have hExtension :
      FieldQuaternaryDiscriminantExtensionIsotropic a hnotSquare := by
    change DiagonalIsotropic
      (fun i ↦ QuadraticAlgebra.C (a i : K))
    simpa [coeffE, E, QuadraticAlgebra.C_eq_algebraMap] using hDiagonalE
  simpa [coeffK] using
    (fieldQuaternary_isotropic_of_discriminantExtension
      a hnotSquare hExtension)

/-- Diagonal coefficients of a rank-four quadratic space, reindexed by
`Fin 4`. -/
noncomputable def fieldQuaternarySpaceCoefficients
    {F V : Type u} [Field F] [CharZero F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (q : QuadraticSpace F V)
    (hRank : Module.finrank F V = 4) : Fin 4 → Fˣ :=
  fun i ↦ q.fieldDiagonalUnits ((finCongr hRank).symm i)

abbrev FieldQuaternarySpaceDiscriminantExtension
    {F V : Type u} [Field F] [CharZero F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (q : QuadraticSpace F V)
    (hRank : Module.finrank F V = 4) :=
  QuadraticAlgebra F
    (fieldQuaternaryDiscriminantUnit
      (fieldQuaternarySpaceCoefficients q hRank) : F) 0

noncomputable def FieldQuaternarySpaceDiscriminantExtensionIsotropic
    {F V : Type u} [Field F] [CharZero F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (q : QuadraticSpace F V)
    (hRank : Module.finrank F V = 4)
    (hnotSquare : ¬ IsSquare
      (fieldQuaternaryDiscriminantUnit
        (fieldQuaternarySpaceCoefficients q hRank) : F)) : Prop := by
  letI : Field (FieldQuaternarySpaceDiscriminantExtension q hRank) :=
    fieldQuaternaryDiscriminantExtensionField
      (fieldQuaternarySpaceCoefficients q hRank) hnotSquare
  exact IsIsotropicSpace
    (q.scalarExtension
      (E := FieldQuaternarySpaceDiscriminantExtension q hRank))

private noncomputable def fieldQuaternarySpaceDiagonalIsometry
    {F V : Type u} [Field F] [CharZero F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (q : QuadraticSpace F V)
    (hRank : Module.finrank F V = 4) :
    QuadraticSpace.Isometry q
      (QuadraticSpace.finiteDiagonal
        (fun i : Fin 4 ↦
          (fieldQuaternarySpaceCoefficients q hRank i : F))
        (fun i ↦ Units.ne_zero
          (fieldQuaternarySpaceCoefficients q hRank i))) := by
  let e : Fin 4 ≃ Fin (Module.finrank F V) :=
    (finCongr hRank).symm
  exact q.fieldDiagonalizationIsometry.trans
    (QuadraticSpace.finiteDiagonalReindexIsometry
      q.fieldDiagonalCoefficients
      q.fieldDiagonalCoefficients_ne_zero e)

/-- Arbitrary-space form of the reverse implication in O'Meara 58:7. -/
theorem fieldQuaternarySpace_isotropic_of_discriminantExtension
    {F V : Type u} [Field F] [CharZero F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (q : QuadraticSpace F V)
    (hRank : Module.finrank F V = 4)
    (hnotSquare : ¬ IsSquare
      (fieldQuaternaryDiscriminantUnit
        (fieldQuaternarySpaceCoefficients q hRank) : F))
    (hiso : FieldQuaternarySpaceDiscriminantExtensionIsotropic
      q hRank hnotSquare) :
    IsIsotropicSpace q := by
  let aUnits := fieldQuaternarySpaceCoefficients q hRank
  let a : Fin 4 → F := fun i ↦ (aUnits i : F)
  have ha : ∀ i, a i ≠ 0 := fun i ↦ Units.ne_zero (aUnits i)
  let E := FieldQuaternarySpaceDiscriminantExtension q hRank
  letI : Field E :=
    fieldQuaternaryDiscriminantExtensionField aUnits hnotSquare
  change IsIsotropicSpace (q.scalarExtension (E := E)) at hiso
  have hdiagExt : IsIsotropicSpace
      ((QuadraticSpace.finiteDiagonal a ha).scalarExtension (E := E)) :=
    isIsotropicSpace_map
      ((fieldQuaternarySpaceDiagonalIsometry q hRank).scalarExtension
        (E := E)) hiso
  have hdiagMapped : IsIsotropicSpace
      (QuadraticSpace.finiteDiagonal
        (fun i ↦ algebraMap F E (a i))
        (fun i ↦ (map_ne_zero (algebraMap F E)).mpr (ha i))) :=
    isIsotropicSpace_map
      (QuadraticSpace.scalarExtensionFiniteDiagonalIsometry
        (E := E) a ha) hdiagExt
  have hDiagonalE : DiagonalIsotropic
      (fun i ↦ algebraMap F E (a i)) :=
    (finiteDiagonal_isIsotropicSpace_iff_diagonalIsotropic
      _ _).mp hdiagMapped
  have hExtension :
      FieldQuaternaryDiscriminantExtensionIsotropic aUnits hnotSquare := by
    change DiagonalIsotropic
      (fun i ↦ QuadraticAlgebra.C (aUnits i : F))
    simpa [E, a, aUnits, QuadraticAlgebra.C_eq_algebraMap] using hDiagonalE
  have hDiagonalF : DiagonalIsotropic a := by
    simpa [a, aUnits] using
      (fieldQuaternary_isotropic_of_discriminantExtension
        aUnits hnotSquare hExtension)
  have hdiagBase : IsIsotropicSpace
      (QuadraticSpace.finiteDiagonal a ha) :=
    (finiteDiagonal_isIsotropicSpace_iff_diagonalIsotropic a ha).mpr
      hDiagonalF
  exact isIsotropicSpace_map
    (fieldQuaternarySpaceDiagonalIsometry q hRank).symm hdiagBase

/-- Arbitrary-space form of the forward implication in O'Meara 58:7. -/
theorem fieldQuaternarySpace_discriminantExtension_isotropic_of_isotropic
    {F V : Type u} [Field F] [CharZero F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (q : QuadraticSpace F V)
    (hRank : Module.finrank F V = 4)
    (hnotSquare : ¬ IsSquare
      (fieldQuaternaryDiscriminantUnit
        (fieldQuaternarySpaceCoefficients q hRank) : F))
    (hiso : IsIsotropicSpace q) :
    FieldQuaternarySpaceDiscriminantExtensionIsotropic
      q hRank hnotSquare := by
  let aUnits := fieldQuaternarySpaceCoefficients q hRank
  let a : Fin 4 → F := fun i ↦ (aUnits i : F)
  have ha : ∀ i, a i ≠ 0 := fun i ↦ Units.ne_zero (aUnits i)
  let E := FieldQuaternarySpaceDiscriminantExtension q hRank
  letI : Field E :=
    fieldQuaternaryDiscriminantExtensionField aUnits hnotSquare
  have hdiagBase : IsIsotropicSpace
      (QuadraticSpace.finiteDiagonal a ha) :=
    isIsotropicSpace_map
      (fieldQuaternarySpaceDiagonalIsometry q hRank) hiso
  have hDiagonalF : DiagonalIsotropic a :=
    (finiteDiagonal_isIsotropicSpace_iff_diagonalIsotropic a ha).mp
      hdiagBase
  have hExtension :
      FieldQuaternaryDiscriminantExtensionIsotropic aUnits hnotSquare :=
    fieldQuaternary_discriminantExtension_isotropic_of_isotropic
      aUnits hnotSquare (by simpa [a, aUnits] using hDiagonalF)
  have hDiagonalE : DiagonalIsotropic
      (fun i ↦ algebraMap F E (a i)) := by
    change DiagonalIsotropic
      (fun i ↦ QuadraticAlgebra.C (aUnits i : F)) at hExtension
    simpa [E, a, aUnits, QuadraticAlgebra.C_eq_algebraMap] using hExtension
  have hdiagMapped : IsIsotropicSpace
      (QuadraticSpace.finiteDiagonal
        (fun i ↦ algebraMap F E (a i))
        (fun i ↦ (map_ne_zero (algebraMap F E)).mpr (ha i))) :=
    (finiteDiagonal_isIsotropicSpace_iff_diagonalIsotropic _ _).mpr
      hDiagonalE
  have hdiagExt : IsIsotropicSpace
      ((QuadraticSpace.finiteDiagonal a ha).scalarExtension (E := E)) :=
    isIsotropicSpace_map
      (QuadraticSpace.scalarExtensionFiniteDiagonalIsometry
        (E := E) a ha).symm hdiagMapped
  have hqExt : IsIsotropicSpace (q.scalarExtension (E := E)) :=
    isIsotropicSpace_map
      ((fieldQuaternarySpaceDiagonalIsometry q hRank).scalarExtension
        (E := E)).symm hdiagExt
  change IsIsotropicSpace (q.scalarExtension (E := E))
  exact hqExt

/-- O'Meara 58:7 for an arbitrary regular rank-four quadratic space with
nonsquare discriminant. -/
theorem fieldQuaternarySpace_discriminantExtension_isotropic_iff
    {F V : Type u} [Field F] [CharZero F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (q : QuadraticSpace F V)
    (hRank : Module.finrank F V = 4)
    (hnotSquare : ¬ IsSquare
      (fieldQuaternaryDiscriminantUnit
        (fieldQuaternarySpaceCoefficients q hRank) : F)) :
    FieldQuaternarySpaceDiscriminantExtensionIsotropic
        q hRank hnotSquare ↔
      IsIsotropicSpace q :=
  ⟨fieldQuaternarySpace_isotropic_of_discriminantExtension
      q hRank hnotSquare,
    fieldQuaternarySpace_discriminantExtension_isotropic_of_isotropic
      q hRank hnotSquare⟩

/-- The complete rank-four step in O'Meara 66:1, conditional only on the
quadratic Hasse Norm theorem for number fields. -/
theorem rankFour_hasse_isotropy_of_universal_hasseNorm
    {K V : Type u} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hNorm : HasUniversalQuadraticHasseNorm.{u})
    (q : QuadraticSpace K V)
    (hRank : Module.finrank K V = 4)
    (hFinite : ∀ p : HeightOneSpectrum (𝓞 K),
      IsIsotropicSpace
        (q.scalarExtension (E := p.adicCompletion K)))
    (hInfinite : ∀ p : NumberField.InfinitePlace K,
      IsIsotropicSpace
        (q.scalarExtension (E := p.Completion))) :
    IsIsotropicSpace q := by
  by_cases hdet : IsSquare
      (∏ i, QuadraticSpace.fieldDiagonalUnits q i)
  · exact rankFour_squareDet_hasse_isotropy_of_hasseNorm
      (hNorm K) q hRank hdet hFinite hInfinite
  · let a := fieldQuaternarySpaceCoefficients q hRank
    have hprod : fieldQuaternaryDiscriminantUnit a =
        ∏ i, QuadraticSpace.fieldDiagonalUnits q i := by
      change (∏ i : Fin 4,
        QuadraticSpace.fieldDiagonalUnits q
          ((finCongr hRank).symm i)) = _
      exact Equiv.prod_comp (finCongr hRank).symm
        (QuadraticSpace.fieldDiagonalUnits q)
    have hnotSquare : ¬ IsSquare
        (fieldQuaternaryDiscriminantUnit a : K) := by
      rw [hprod]
      intro hsquare
      apply hdet
      exact (isSquare_unit_iff_isSquare_coe _).mpr hsquare
    let diagonalIsometry :=
      fieldQuaternarySpaceDiagonalIsometry q hRank
    have hFiniteDiagonal : ∀ p : HeightOneSpectrum (𝓞 K),
        IsIsotropicSpace
          ((QuadraticSpace.finiteDiagonal
            (fun i ↦ (a i : K))
            (fun i ↦ Units.ne_zero (a i))).scalarExtension
              (E := p.adicCompletion K)) := by
      intro p
      exact isIsotropicSpace_map
        (diagonalIsometry.scalarExtension
          (E := p.adicCompletion K)) (hFinite p)
    have hInfiniteDiagonal : ∀ p : NumberField.InfinitePlace K,
        IsIsotropicSpace
          ((QuadraticSpace.finiteDiagonal
            (fun i ↦ (a i : K))
            (fun i ↦ Units.ne_zero (a i))).scalarExtension
              (E := p.Completion)) := by
      intro p
      exact isIsotropicSpace_map
        (diagonalIsometry.scalarExtension
          (E := p.Completion)) (hInfinite p)
    have hDiagonal :=
      finiteDiagonal_rankFour_hasse_isotropy_of_discriminantExtension
        hNorm a hnotSquare hFiniteDiagonal hInfiniteDiagonal
    have hDiagonalSpace : IsIsotropicSpace
        (QuadraticSpace.finiteDiagonal
          (fun i ↦ (a i : K))
          (fun i ↦ Units.ne_zero (a i))) :=
      (finiteDiagonal_isIsotropicSpace_iff_diagonalIsotropic
        (fun i ↦ (a i : K))
        (fun i ↦ Units.ne_zero (a i))).mpr hDiagonal
    exact isIsotropicSpace_map
      diagonalIsometry.symm hDiagonalSpace

end Bong.HeADCV5.Global.NumberFieldLattice
