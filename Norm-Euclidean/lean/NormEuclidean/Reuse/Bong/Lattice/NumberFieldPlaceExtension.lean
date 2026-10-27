/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import NormEuclidean.Reuse.Bong.Lattice.NumberFieldHasseIsotropyReduction
import NormEuclidean.Reuse.Bong.QuadraticSpace.ScalarExtensionTower
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Extension of finite and infinite places of number fields

For a finite extension `L / K`, this file constructs the map from the
completion of `K` at a finite place `v` to the completion of `L` at a place
`w` above `v`. It then proves the finite and infinite place transport of
isotropy needed in the rank-four Hasse argument.
-/

namespace Bong

open scoped NumberField NumberField.LiesOver TensorProduct
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum

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

noncomputable instance finitePlaceCompletionAlgebra
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

instance finitePlaceCompletion_isScalarTower
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver v.asIdeal] :
    IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [finitePlaceCompletion_algebraMap_apply]
    change (algebraMap K L x : w.adicCompletion L) =
      finitePlaceCompletionMap (K := K) (L := L) v w
        (x : v.adicCompletion K)
    exact (finitePlaceCompletionMap_coe v w x).symm

/-- Isotropy remains isotropy after scalar extension. -/
theorem isIsotropicSpace_scalarExtension
    {F E V : Type u} [Field F] [Field E] [Algebra F E]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (q : QuadraticSpace F V)
    (h : HeADCV5.Global.NumberFieldLattice.IsIsotropicSpace q) :
    HeADCV5.Global.NumberFieldLattice.IsIsotropicSpace
      (q.scalarExtension (E := E)) := by
  rcases h with ⟨x, hx, hqx⟩
  refine ⟨1 ⊗ₜ[F] x, ?_, ?_⟩
  · intro hzero
    apply hx
    exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff F V x).mp hzero
  · simp [hqx]

/-- If a scalar extension is isotropic, then every further scalar extension
through a field tower is isotropic. -/
theorem isIsotropicSpace_scalarExtension_tower
    {F E L V : Type u} [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra E L] [Algebra F L]
    [IsScalarTower F E L]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (q : QuadraticSpace F V)
    (h : HeADCV5.Global.NumberFieldLattice.IsIsotropicSpace
      (q.scalarExtension (E := E))) :
    HeADCV5.Global.NumberFieldLattice.IsIsotropicSpace
      (q.scalarExtension (E := L)) :=
  HeADCV5.Global.NumberFieldLattice.isIsotropicSpace_map
    (q.scalarExtensionTowerIsometry (E := E) (L := L))
    (isIsotropicSpace_scalarExtension
      (q.scalarExtension (E := E)) h)

/-- The canonical algebra structures make the completion at an infinite
place of `E` a scalar tower over every subfield `K`. -/
instance numberField_infinitePlaceCompletion_isScalarTower
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

/-- Isotropy at the contracted finite place of `K` transports to isotropy
at the chosen finite place of `E`. -/
theorem numberField_finitePlace_isotropic_of_under
    {K E V : Type u} [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra K E]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (q : QuadraticSpace K V)
    (w : HeightOneSpectrum (𝓞 E))
    (h : HeADCV5.Global.NumberFieldLattice.IsIsotropicSpace
      (q.scalarExtension
        (E := (w.under (𝓞 K)).adicCompletion K))) :
    HeADCV5.Global.NumberFieldLattice.IsIsotropicSpace
      (q.scalarExtension (E := w.adicCompletion E)) := by
  let v : HeightOneSpectrum (𝓞 K) := w.under (𝓞 K)
  haveI : w.asIdeal.LiesOver v.asIdeal := by
    change w.asIdeal.LiesOver (w.asIdeal.under (𝓞 K))
    infer_instance
  exact isIsotropicSpace_scalarExtension_tower
    (E := v.adicCompletion K) (L := w.adicCompletion E)
    q (by simpa [v] using h)

/-- Isotropy at the restriction of an infinite place of `E` transports to
isotropy at that place of `E`. -/
theorem numberField_infinitePlace_isotropic_of_comap
    {K E V : Type u} [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra K E]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (q : QuadraticSpace K V)
    (w : NumberField.InfinitePlace E)
    (h : HeADCV5.Global.NumberFieldLattice.IsIsotropicSpace
      (q.scalarExtension
        (E := (w.comap (algebraMap K E)).Completion))) :
    HeADCV5.Global.NumberFieldLattice.IsIsotropicSpace
      (q.scalarExtension (E := w.Completion)) := by
  let v : NumberField.InfinitePlace K :=
    w.comap (algebraMap K E)
  haveI : w.1.LiesOver v.1 := by
    constructor
    rfl
  exact isIsotropicSpace_scalarExtension_tower
    (E := v.Completion) (L := w.Completion)
    q (by simpa [v] using h)

end Bong
