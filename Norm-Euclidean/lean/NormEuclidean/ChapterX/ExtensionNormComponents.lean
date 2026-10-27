/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import NormEuclidean.ChapterX.ExtensionPlaces
import NormEuclidean.ChapterX.IdeleComponents
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Field norm components at the places above a base place

Adapted from HeADC's NumberFieldExtensionIdeleNormComponents. The maps use
all actual extension places and determinant field norms. Restricted-product
assembly is proved separately, using preservation of local units.
-/

namespace NormEuclidean.ExtensionIdeleNorm

open scoped NumberField
open scoped NumberField.LiesOver TensorProduct
open scoped NormEuclidean.ExtensionPlaces
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum

universe u
variable {K E : Type u} [Field K] [NumberField K]
  [Field E] [NumberField E] [Algebra K E]

/-- Finite places of `E` lying over a fixed finite place of `K`. -/
abbrev FinitePlacesAbove (p : HeightOneSpectrum (𝓞 K)) :=
  {w : HeightOneSpectrum (𝓞 E) // w.under (𝓞 K) = p}

/-- The fiber of finite places is the usual finite set of prime ideals
lying over the base prime. -/
noncomputable def finitePlacesAboveEquivPrimesOver
    (p : HeightOneSpectrum (𝓞 K)) :
    FinitePlacesAbove (E := E) p ≃ p.asIdeal.primesOver (𝓞 E) where
  toFun w := by
    refine ⟨w.1.asIdeal, ⟨w.1.isPrime, ?_⟩⟩
    exact ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩
  invFun Q := by
    let w : HeightOneSpectrum (𝓞 E) :=
      ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot Q.2⟩
    refine ⟨w, ?_⟩
    apply HeightOneSpectrum.ext_iff.mpr
    exact Q.2.2.over.symm
  left_inv := by
    intro w
    apply Subtype.ext
    apply HeightOneSpectrum.ext_iff.mpr
    rfl
  right_inv := by
    intro Q
    apply Subtype.ext
    rfl

noncomputable instance (p : HeightOneSpectrum (𝓞 K)) :
    Fintype (FinitePlacesAbove (E := E) p) :=
  Fintype.ofEquiv (p.asIdeal.primesOver (𝓞 E))
    (finitePlacesAboveEquivPrimesOver (E := E) p).symm

omit [NumberField E] in
/-- Every base finite place has at least one extension place. -/
theorem finitePlacesAbove_nonempty (p : HeightOneSpectrum (𝓞 K)) :
    Nonempty (FinitePlacesAbove (E := E) p) := by
  obtain ⟨Q, hmax, hover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := 𝓞 E) p.asIdeal
  exact ⟨(finitePlacesAboveEquivPrimesOver (E := E) p).symm
    ⟨Q, hmax.isPrime, hover⟩⟩

/-- Map from a base finite completion into a completion above it. -/
noncomputable def finitePlaceAboveCompletionMap
    (p : HeightOneSpectrum (𝓞 K))
    (w : FinitePlacesAbove (E := E) p) :
    p.adicCompletion K →+* w.1.adicCompletion E := by
  letI : w.1.asIdeal.LiesOver p.asIdeal :=
    ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩
  exact NormEuclidean.ExtensionPlaces.finitePlaceCompletionMap (K := K) (L := E) p w.1

/-- The finite-completion map agrees with the original field embedding. -/
theorem finitePlaceAboveCompletionMap_global
    (p : HeightOneSpectrum (𝓞 K))
    (w : FinitePlacesAbove (E := E) p) (x : K) :
    finitePlaceAboveCompletionMap p w (x : p.adicCompletion K) =
      (algebraMap K E x : w.1.adicCompletion E) := by
  letI : w.1.asIdeal.LiesOver p.asIdeal :=
    ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩
  exact NormEuclidean.ExtensionPlaces.finitePlaceCompletionMap_coe p w.1 x

/-- The map between actual finite completions is continuous. -/
theorem finitePlaceAboveCompletionMap_continuous
    (p : HeightOneSpectrum (𝓞 K))
    (w : FinitePlacesAbove (E := E) p) :
    Continuous (finitePlaceAboveCompletionMap p w) := by
  letI : w.1.asIdeal.LiesOver p.asIdeal :=
    ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩
  change Continuous
    ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv E w.1).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (p.valuation K))
        (WithVal (w.1.valuation E)))
      (IsDedekindDomain.HeightOneSpectrum.uniformContinuous_algebraMap_liesOver
        K E p w.1).continuous).comp
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K p).toRingHom))
  exact (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion E w.1).comp
    (UniformSpace.Completion.continuous_map.comp
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_toCompletion K p))

/-- The actual finite completed-field extension as an algebra. -/
@[reducible] noncomputable def finitePlaceAboveAlgebra
    (p : HeightOneSpectrum (𝓞 K))
    (w : FinitePlacesAbove (E := E) p) :
    Algebra (p.adicCompletion K) (w.1.adicCompletion E) :=
  (finitePlaceAboveCompletionMap p w).toAlgebra

/-- Actual finite completed extensions are finite-dimensional.  The
continuity and scalar-tower instances below are the hypotheses of
mathlib's finite-dimensionality theorem for number-field completions. -/
theorem finitePlaceAbove_moduleFinite
    (p : HeightOneSpectrum (𝓞 K))
    (w : FinitePlacesAbove (E := E) p) :
    letI : Algebra (p.adicCompletion K) (w.1.adicCompletion E) :=
      finitePlaceAboveAlgebra p w
    Module.Finite (p.adicCompletion K) (w.1.adicCompletion E) := by
  letI : w.1.asIdeal.LiesOver p.asIdeal :=
    ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩
  letI : Algebra (p.adicCompletion K) (w.1.adicCompletion E) :=
    finitePlaceAboveAlgebra p w
  letI : ContinuousSMul (p.adicCompletion K) (w.1.adicCompletion E) :=
    ⟨((finitePlaceAboveCompletionMap_continuous p w).comp continuous_fst).mul
      continuous_snd⟩
  haveI : IsScalarTower K (p.adicCompletion K) (w.1.adicCompletion E) :=
    NormEuclidean.ExtensionPlaces.finitePlaceCompletion_isScalarTower p w.1
  infer_instance

/-- The field norm on units of one finite completion. -/
noncomputable def finitePlaceAboveNormUnits
    (p : HeightOneSpectrum (𝓞 K))
    (w : FinitePlacesAbove (E := E) p) :
    (w.1.adicCompletion E)ˣ →* (p.adicCompletion K)ˣ := by
  letI : w.1.asIdeal.LiesOver p.asIdeal :=
    ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩
  letI : Algebra (p.adicCompletion K) (w.1.adicCompletion E) :=
    finitePlaceAboveAlgebra p w
  letI : Module.Finite (p.adicCompletion K) (w.1.adicCompletion E) :=
    finitePlaceAbove_moduleFinite p w
  exact Units.map (Algebra.norm (p.adicCompletion K))

/-- The finite-place norm has its expected value on an element of the
base completed field.  In particular, this identifies the norm above
with the determinant norm of an actual finite-dimensional extension. -/
theorem finitePlaceAbove_norm_algebraMap
    (p : HeightOneSpectrum (𝓞 K))
    (w : FinitePlacesAbove (E := E) p) (a : p.adicCompletion K) :
    letI : Algebra (p.adicCompletion K) (w.1.adicCompletion E) :=
      finitePlaceAboveAlgebra p w
    Algebra.norm (p.adicCompletion K) (finitePlaceAboveCompletionMap p w a) =
      a ^ Module.finrank (p.adicCompletion K) (w.1.adicCompletion E) := by
  letI : Algebra (p.adicCompletion K) (w.1.adicCompletion E) :=
    finitePlaceAboveAlgebra p w
  letI : Module.Finite (p.adicCompletion K) (w.1.adicCompletion E) :=
    finitePlaceAbove_moduleFinite p w
  exact Algebra.norm_algebraMap a

/-- Product of local norms over every extension place above one finite place. -/
noncomputable def finitePlaceFiberNormUnits
    (p : HeightOneSpectrum (𝓞 K)) :
    ((w : FinitePlacesAbove (E := E) p) →
      (w.1.adicCompletion E)ˣ) →* (p.adicCompletion K)ˣ where
  toFun z := ∏ w, finitePlaceAboveNormUnits p w (z w)
  map_one' := by simp
  map_mul' := by
    intro x y
    simp [map_mul, Finset.prod_mul_distrib]

/-- The finite component of the norm of an actual extension idèle. -/
noncomputable def finitePlaceExtensionIdeleNormComponent
    (p : HeightOneSpectrum (𝓞 K)) :
    NumberFieldIdele E →* (p.adicCompletion K)ˣ where
  toFun j := ∏ w : FinitePlacesAbove (E := E) p,
    finitePlaceAboveNormUnits p w (ideleFiniteComponent w.1 j)
  map_one' := by simp
  map_mul' := by
    intro j k
    simp [map_mul, Finset.prod_mul_distrib]

/-- The idèle's finite norm component is exactly the norm of the
fiber of its local components. -/
theorem finitePlaceExtensionIdeleNormComponent_eq_fiber
    (p : HeightOneSpectrum (𝓞 K)) (j : NumberFieldIdele E) :
    finitePlaceExtensionIdeleNormComponent p j =
      finitePlaceFiberNormUnits p (fun w ↦ ideleFiniteComponent w.1 j) :=
  rfl

/-- Infinite places of `E` restricting to a given infinite place of `K`. -/
abbrev InfinitePlacesAbove (v : NumberField.InfinitePlace K) :=
  {w : NumberField.InfinitePlace E // w.comap (algebraMap K E) = v}

noncomputable instance (v : NumberField.InfinitePlace K) :
    Fintype (InfinitePlacesAbove (E := E) v) := Fintype.ofFinite _

/-- Map from a base infinite completion into a completion above it. -/
@[reducible] noncomputable def infinitePlaceAboveCompletionMap
    (v : NumberField.InfinitePlace K)
    (w : InfinitePlacesAbove (E := E) v) :
    v.Completion →+* w.1.Completion := by
  letI : w.1.1.LiesOver v.1 := by
    constructor
    exact congrArg Subtype.val w.2
  exact NumberField.LiesOver.completionMap

/-- Each infinite completed-field extension has finite dimension. -/
theorem infinitePlaceAbove_moduleFinite
    (v : NumberField.InfinitePlace K)
    (w : InfinitePlacesAbove (E := E) v) :
    letI : Algebra v.Completion w.1.Completion :=
      (infinitePlaceAboveCompletionMap v w).toAlgebra
    Module.Finite v.Completion w.1.Completion := by
  letI : w.1.1.LiesOver v.1 := by
    constructor
    exact congrArg Subtype.val w.2
  letI : NontriviallyNormedField v.Completion :=
    infiniteCompletionNontriviallyNormedField v
  letI : Algebra v.Completion w.1.Completion :=
    (infinitePlaceAboveCompletionMap v w).toAlgebra
  let Φ : v.Completion ⊗[K] E →ₗ[v.Completion] w.1.Completion :=
    Algebra.TensorProduct.lift (Algebra.algHom v.Completion v.Completion w.1.Completion)
      (Algebra.algHom K E w.1.Completion) (fun _ _ ↦ mul_comm ..) |>.toLinearMap
  have h_dense : DenseRange Φ := by
    apply (NumberField.InfinitePlace.Completion.denseRange_coe (v := w.1)).mono
    rintro _ ⟨e, rfl⟩
    refine ⟨1 ⊗ₜ (WithAbs.equiv w.1.1 e), ?_⟩
    simp [Φ, Algebra.algHom]
  exact Module.Finite.of_surjective Φ (by
    rw [← Set.range_eq_univ]
    have hclosed : IsClosed (Set.range Φ) := by
      change IsClosed (Φ.range : Set w.1.Completion)
      exact Φ.range.closed_of_finiteDimensional
    exact hclosed.closure_eq.symm.trans h_dense.closure_range)

omit [NumberField K] [NumberField E] in
/-- The infinite-completion map agrees with the original field embedding. -/
theorem infinitePlaceAboveCompletionMap_global
    (v : NumberField.InfinitePlace K)
    (w : InfinitePlacesAbove (E := E) v) (x : K) :
    infinitePlaceAboveCompletionMap v w (x : v.Completion) =
      (algebraMap K E x : w.1.Completion) := by
  letI : w.1.1.LiesOver v.1 := by
    constructor
    exact congrArg Subtype.val w.2
  letI : Algebra v.Completion w.1.Completion :=
    (infinitePlaceAboveCompletionMap v w).toAlgebra
  change algebraMap v.Completion w.1.Completion (algebraMap K v.Completion x) =
    algebraMap E w.1.Completion (algebraMap K E x)
  rw [← IsScalarTower.algebraMap_apply K v.Completion w.1.Completion x,
    ← IsScalarTower.algebraMap_apply K E w.1.Completion x]

/-- The field norm on units of one infinite completion. -/
noncomputable def infinitePlaceAboveNormUnits
    (v : NumberField.InfinitePlace K)
    (w : InfinitePlacesAbove (E := E) v) :
    (w.1.Completion)ˣ →* (v.Completion)ˣ := by
  letI : Algebra v.Completion w.1.Completion :=
    (infinitePlaceAboveCompletionMap v w).toAlgebra
  letI : Module.Finite v.Completion w.1.Completion :=
    infinitePlaceAbove_moduleFinite v w
  exact Units.map (Algebra.norm v.Completion)

/-- Product of local norms over every extension place above one infinite place. -/
noncomputable def infinitePlaceFiberNormUnits
    (v : NumberField.InfinitePlace K) :
    ((w : InfinitePlacesAbove (E := E) v) →
      (w.1.Completion)ˣ) →* (v.Completion)ˣ where
  toFun z := ∏ w, infinitePlaceAboveNormUnits v w (z w)
  map_one' := by simp
  map_mul' := by
    intro x y
    simp [map_mul, Finset.prod_mul_distrib]

/-- The infinite component of the norm of an actual extension idèle. -/
noncomputable def infinitePlaceExtensionIdeleNormComponent
    (v : NumberField.InfinitePlace K) :
    NumberFieldIdele E →* (v.Completion)ˣ where
  toFun j := ∏ w : InfinitePlacesAbove (E := E) v,
    infinitePlaceAboveNormUnits v w (ideleInfiniteComponent w.1 j)
  map_one' := by simp
  map_mul' := by
    intro j k
    simp [map_mul, Finset.prod_mul_distrib]

omit [NumberField K] in
/-- The idèle's infinite norm component is the norm of the fiber of
its local components. -/
theorem infinitePlaceExtensionIdeleNormComponent_eq_fiber
    (v : NumberField.InfinitePlace K) (j : NumberFieldIdele E) :
    infinitePlaceExtensionIdeleNormComponent v j =
      infinitePlaceFiberNormUnits v (fun w ↦ ideleInfiniteComponent w.1 j) :=
  rfl

/-- All finite and infinite extension-idèle norm components, before
the restricted-product condition is established. -/
noncomputable def extensionIdeleNormComponentFamily :
    NumberFieldIdele E →*
      (((p : HeightOneSpectrum (𝓞 K)) → (p.adicCompletion K)ˣ) ×
        ((v : NumberField.InfinitePlace K) → (v.Completion)ˣ)) where
  toFun j := (fun p ↦ finitePlaceExtensionIdeleNormComponent p j,
    fun v ↦ infinitePlaceExtensionIdeleNormComponent v j)
  map_one' := by
    ext p <;> simp
  map_mul' := by
    intro j k
    ext p <;> simp [map_mul]

omit [NumberField K] in
/-- Outside a finite set of base primes, all extension-idèle components
over each prime are valuation units. -/
theorem extensionIdele_eventually_all_finitePlacesAbove_units
    (j : NumberFieldIdele E) :
    ∀ᶠ p : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ∀ w : FinitePlacesAbove (E := E) p,
        Valued.v ((ideleFiniteComponent w.1 j : (w.1.adicCompletion E)ˣ) :
          w.1.adicCompletion E) = 1 := by
  classical
  let bad : Set (HeightOneSpectrum (𝓞 E)) :=
    {w | Valued.v ((ideleFiniteComponent w j : (w.adicCompletion E)ˣ) :
      w.adicCompletion E) ≠ 1}
  have hbad : bad.Finite := by
    simpa [bad] using
      (Filter.eventually_cofinite.mp (ideleFiniteComponent_eventually_valuation_one j))
  have hImage : ((fun w : HeightOneSpectrum (𝓞 E) ↦ w.under (𝓞 K)) '' bad).Finite :=
    hbad.image _
  have hAvoid : ∀ᶠ p : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      p ∉ (fun w : HeightOneSpectrum (𝓞 E) ↦ w.under (𝓞 K)) '' bad := by
    apply Filter.eventually_cofinite.mpr
    have hset : {p : HeightOneSpectrum (𝓞 K) |
        ¬p ∉ (fun w : HeightOneSpectrum (𝓞 E) ↦ w.under (𝓞 K)) '' bad} =
        (fun w : HeightOneSpectrum (𝓞 E) ↦ w.under (𝓞 K)) '' bad := by
      ext p
      simp only [Set.mem_setOf_eq, not_not]
    simpa only [hset] using hImage
  filter_upwards [hAvoid] with p hp w
  by_contra hw
  exact hp ⟨w.1, hw, w.2⟩

end NormEuclidean.ExtensionIdeleNorm
