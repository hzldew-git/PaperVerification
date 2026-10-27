/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances

/-!
# The embeddings between actual completions above a place

Adapted from the completed place maps in HeADC's NumberFieldPlaceExtension.
Only the field embeddings and scalar towers are reused; no global isotropy
or norm-index proposition is imported.
-/

namespace NormEuclidean.ExtensionPlaces

open scoped NumberField NumberField.LiesOver TensorProduct
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

universe u uA uB uK uL

variable {A : Type uA} {B : Type uB} {K : Type uK} {L : Type uL}
variable [CommRing A] [IsDedekindDomain A]
  [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.IsTorsionFree A B]
variable [Field K] [Field L] [Algebra K L]
variable [Algebra A K] [IsFractionRing A K]
  [Algebra A L] [IsScalarTower A K L]
variable [Algebra B L] [IsFractionRing B L]
  [IsScalarTower A B L]

/-- The homomorphism between finite-place completions induced by a place
`w` above `v`. -/
noncomputable def finitePlaceCompletionMap
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver v.asIdeal] :
    v.adicCompletion K →+* w.adicCompletion L :=
  (adicCompletion.equiv L w).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation K))
        (WithVal (w.valuation L)))
      (uniformContinuous_algebraMap_liesOver K L v w).continuous).comp
      (adicCompletion.equiv K v).toRingHom)

@[simp]
theorem finitePlaceCompletionMap_coe
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver v.asIdeal] (x : K) :
    finitePlaceCompletionMap (K := K) (L := L) v w
        (x : v.adicCompletion K) =
      (algebraMap K L x : w.adicCompletion L) := by
  apply adicCompletion.ext L w
  change UniformSpace.Completion.map
      (algebraMap (WithVal (v.valuation K))
        (WithVal (w.valuation L)))
      (↑(WithVal.toVal (v.valuation K) x)) =
    ↑(WithVal.toVal (w.valuation L) (algebraMap K L x))
  rw [UniformSpace.Completion.map_coe
    (uniformContinuous_algebraMap_liesOver K L v w)]
  congr 1

noncomputable scoped instance finitePlaceCompletionAlgebra
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver v.asIdeal] :
    Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  (finitePlaceCompletionMap (K := K) (L := L) v w).toAlgebra

@[simp]
theorem finitePlaceCompletion_algebraMap_apply
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver v.asIdeal] (x : v.adicCompletion K) :
    algebraMap (v.adicCompletion K) (w.adicCompletion L) x =
      finitePlaceCompletionMap (K := K) (L := L) v w x :=
  rfl

scoped instance finitePlaceCompletion_isScalarTower
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver v.asIdeal] :
    IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [finitePlaceCompletion_algebraMap_apply]
    change (algebraMap K L x : w.adicCompletion L) =
      finitePlaceCompletionMap (K := K) (L := L) v w
        (x : v.adicCompletion K)
    exact (finitePlaceCompletionMap_coe v w x).symm

/-- The canonical algebra structures make the completion at an infinite
place of `E` a scalar tower over every subfield `K`. -/
scoped instance numberField_infinitePlaceCompletion_isScalarTower
    {K E : Type u} [Field K] [Field E] [Algebra K E]
    (w : NumberField.InfinitePlace E) :
    IsScalarTower K E w.Completion :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    apply NumberField.InfinitePlace.Completion.ext
    rw [NumberField.InfinitePlace.Completion.algebraMap_toCompletion,
      NumberField.InfinitePlace.Completion.algebraMap_toCompletion]
    exact congrArg
      (UniformSpace.Completion.coeRingHom (α := WithAbs w.1))
      (IsScalarTower.algebraMap_apply K E (WithAbs w.1) x)

end NormEuclidean.ExtensionPlaces
