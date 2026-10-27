import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.RingTheory.Localization.BaseChange
import NormEuclidean.CompletedIntegralLattice
import NormEuclidean.LocalizationLatticeRecovery

/-!
# Faithfully flat descent from actual finite completions

The local ring `R_p` is identified with the valuation subring of the fraction
field, and its canonical map to the actual completed valuation ring is proved
faithfully flat. An injective tensor map compares integral scalar extension
with the project's ambient space `K_p ⊗[K] V`. Consequently equality of the
completed carriers determines equality of the localizations, then equality of
the global submodules at all finite places over a non-field Dedekind subring.

This proves the lattice-recovery step used at the end of O'Meara 104:5. It
requires neither a basis for the lattice nor an inverse of two in an integral
ring. It does not assume or prove strong approximation.
-/

noncomputable section

open IsDedekindDomain
open scoped TensorProduct nonZeroDivisors

namespace NormEuclidean.CompletionDescent

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

instance adicCompletion_hasExtension (v : HeightOneSpectrum R) :
    (v.valuation K).HasExtension
      (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))) where
  val_isEquiv_comap := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    change v.valuation K x ≤ 1 ↔
      Valued.v (algebraMap K (v.adicCompletion K) x) ≤ 1
    change v.valuation K x ≤ 1 ↔ Valued.v (x : v.adicCompletion K) ≤ 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

instance valuationSubringAlgebra (v : HeightOneSpectrum R) :
    Algebra R (v.valuation K).valuationSubring :=
  ((algebraMap R K).codRestrict _ (fun r ↦ v.valuation_le_one r)).toAlgebra

instance valuationSubringTower (v : HeightOneSpectrum R) :
    IsScalarTower R (v.valuation K).valuationSubring K :=
  IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

instance valuationSubringLocalization (v : HeightOneSpectrum R) :
    IsLocalization v.asIdeal.primeCompl (v.valuation K).valuationSubring where
  map_units s := by
    apply (Valuation.valuationSubring.integers (v.valuation K)).isUnit_of_one
    · apply IsUnit.mk0
      intro hs
      have hs0 : s.1 = 0 := (IsFractionRing.to_map_eq_zero_iff).mp hs
      exact s.2 (hs0 ▸ v.asIdeal.zero_mem)
    · change v.valuation K (algebraMap R K s.1) = 1
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact (v.intValuation_eq_one_iff_mem_primeCompl s.1).2 s.2
  surj x := by
    obtain ⟨r, s, h⟩ := v.exists_primeCompl_mul_eq_of_integer x.1 x.2
    exact ⟨⟨r, s⟩, Subtype.ext h⟩
  exists_of_eq h := by
    have heq : algebraMap R K _ = algebraMap R K _ := congrArg Subtype.val h
    exact ⟨1, by simpa using (IsFractionRing.injective R K heq)⟩

/-- The abstract local ring is the actual valuation subring of the fraction field. -/
def localizationEquivValuationSubring (v : HeightOneSpectrum R) :
    Localization.AtPrime v.asIdeal ≃ₐ[R] (v.valuation K).valuationSubring :=
  IsLocalization.algEquiv v.asIdeal.primeCompl _ _

/-- Restrict the field-completion embedding to its valuation integers. -/
def valuationToCompletionIntegers (v : HeightOneSpectrum R) :
    (v.valuation K).valuationSubring →+* v.adicCompletionIntegers K :=
  ((algebraMap K (v.adicCompletion K)).comp
    (v.valuation K).valuationSubring.toSubring.subtype).codRestrict _ (fun x ↦ by
    change Valued.v (algebraMap K (v.adicCompletion K) x.1) ≤ 1
    change Valued.v (x.1 : v.adicCompletion K) ≤ 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact x.2)

instance valuationAlgebraCompletionIntegers (v : HeightOneSpectrum R) :
    Algebra (v.valuation K).valuationSubring (v.adicCompletionIntegers K) :=
  (valuationToCompletionIntegers v).toAlgebra

instance valuationCompletionTower (v : HeightOneSpectrum R) :
    IsScalarTower (v.valuation K).valuationSubring
      (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

instance valuationCompletionFaithful (v : HeightOneSpectrum R) :
    FaithfulSMul (v.valuation K).valuationSubring (v.adicCompletionIntegers K) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y h
  apply Subtype.ext
  exact (algebraMap K (v.adicCompletion K)).injective (congrArg Subtype.val h)

instance valuationCompletionTorsionFree (v : HeightOneSpectrum R) :
    Module.IsTorsionFree (v.valuation K).valuationSubring
      (v.adicCompletionIntegers K) := .of_smul_eq_zero <| by simp

instance valuationCompletionIsLocalHom (v : HeightOneSpectrum R) :
    IsLocalHom (valuationToCompletionIntegers (K := K) v) where
  map_nonunit x hx := by
    have hval := (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mp hx
    change Valued.v (x.1 : v.adicCompletion K) = 1 at hval
    have hxval : v.valuation K x.1 = 1 :=
      (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) x.1).symm.trans hval
    apply (Valuation.valuationSubring.integers (v.valuation K)).isUnit_of_one
    · apply IsUnit.mk0
      intro hzero
      change x.1 = 0 at hzero
      have hbad : (0 : WithZero (Multiplicative ℤ)) = 1 := by
        simpa only [hzero, map_zero] using hxval
      exact zero_ne_one hbad
    · exact hxval

instance valuationCompletionFlat (v : HeightOneSpectrum R) :
    Module.Flat (v.valuation K).valuationSubring (v.adicCompletionIntegers K) := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
    ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

/-- Completing the valuation integers is faithfully flat: the map is local,
and the target is torsion-free over the valuation ring. -/
instance valuationCompletionFaithfullyFlat (v : HeightOneSpectrum R) :
    Module.FaithfullyFlat (v.valuation K).valuationSubring
      (v.adicCompletionIntegers K) := by
  haveI : IsLocalHom (algebraMap (v.valuation K).valuationSubring
      (v.adicCompletionIntegers K)) := valuationCompletionIsLocalHom v
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- The canonical map from the abstract localization to the actual completion integers. -/
def localizationToCompletionIntegers (v : HeightOneSpectrum R) :
    Localization.AtPrime v.asIdeal →+* v.adicCompletionIntegers K :=
  (valuationToCompletionIntegers v).comp (localizationEquivValuationSubring v).toRingHom

/-- This canonical map extends the global integral embedding. -/
@[simp] theorem localizationToCompletionIntegers_comp (v : HeightOneSpectrum R) :
    (localizationToCompletionIntegers v).comp
        (algebraMap R (Localization.AtPrime v.asIdeal)) =
      algebraMap R (v.adicCompletionIntegers K) := by
  apply RingHom.ext
  intro r
  change valuationToCompletionIntegers v
    (localizationEquivValuationSubring v (algebraMap R (Localization.AtPrime v.asIdeal) r)) = _
  rw [AlgEquiv.commutes]
  rfl

instance localizationAlgebraCompletionIntegers (v : HeightOneSpectrum R) :
    Algebra (Localization.AtPrime v.asIdeal) (v.adicCompletionIntegers K) :=
  (localizationToCompletionIntegers v).toAlgebra

instance localizationCompletionIsLocalHom (v : HeightOneSpectrum R) :
    IsLocalHom (algebraMap (Localization.AtPrime v.asIdeal)
      (v.adicCompletionIntegers K)) := by
  haveI : IsLocalHom (localizationEquivValuationSubring (K := K) v).toRingHom :=
    isLocalHom_toRingHom (localizationEquivValuationSubring (K := K) v)
  exact RingHom.isLocalHom_comp _ _

instance localizationCompletionFaithful (v : HeightOneSpectrum R) :
    FaithfulSMul (Localization.AtPrime v.asIdeal) (v.adicCompletionIntegers K) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  exact (FaithfulSMul.algebraMap_injective (v.valuation K).valuationSubring
    (v.adicCompletionIntegers K)).comp (localizationEquivValuationSubring v).injective

instance localizationCompletionTorsionFree (v : HeightOneSpectrum R) :
    Module.IsTorsionFree (Localization.AtPrime v.asIdeal)
      (v.adicCompletionIntegers K) := .of_smul_eq_zero <| by simp

/-- The actual completed integer ring is faithfully flat over the abstract local ring. -/
instance localizationCompletionFaithfullyFlat (v : HeightOneSpectrum R) :
    Module.FaithfullyFlat (Localization.AtPrime v.asIdeal)
      (v.adicCompletionIntegers K) := by
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

instance valuationGlobalCompletionTower (v : HeightOneSpectrum R) :
    IsScalarTower R (v.valuation K).valuationSubring (v.adicCompletionIntegers K) :=
  IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

section Tensor

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- Compare integral scalar extension with the actual field-completed ambient space. -/
def integralTensorToCompletedSpace (v : HeightOneSpectrum R) :
    v.adicCompletionIntegers K ⊗[(v.valuation K).valuationSubring] V →ₗ[v.adicCompletionIntegers K]
      v.adicCompletion K ⊗[K] V := by
  let S := (v.valuation K).valuationSubring
  let O := v.adicCompletionIntegers K
  let F := v.adicCompletion K
  letI : TensorProduct.CompatibleSMul S K F V :=
    IsLocalization.tensorProduct_compatibleSMul S⁰ K F V
  exact (TensorProduct.equivOfCompatibleSMul S K O F V).symm.toLinearMap ∘ₗ
    TensorProduct.AlgebraTensorModule.rTensor S V (Algebra.linearMap O F)

/-- This comparison is injective because the original vector space is flat
over its valuation subring and the completed integer ring embeds in its field. -/
theorem integralTensorToCompletedSpace_injective (v : HeightOneSpectrum R) :
    Function.Injective (integralTensorToCompletedSpace (K := K) (V := V) v) := by
  let S := (v.valuation K).valuationSubring
  let O := v.adicCompletionIntegers K
  let F := v.adicCompletion K
  haveI : Module.IsTorsionFree S V := .of_smul_eq_zero <| by
    intro a x hx
    change (a : K) • x = 0 at hx
    rcases smul_eq_zero.mp hx with ha | hx
    · exact Or.inl (Subtype.ext ha)
    · exact Or.inr hx
  haveI : Module.Flat S V := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
      ← Submodule.isTorsionFree_iff_torsion_eq_bot]
    infer_instance
  dsimp only [integralTensorToCompletedSpace, LinearMap.coe_comp, LinearEquiv.coe_coe]
  apply Function.Injective.comp (LinearEquiv.injective _)
  exact Module.Flat.rTensor_preserves_injective_linearMap
    ((Algebra.linearMap O F).restrictScalars S)
    (FaithfulSMul.algebraMap_injective O F)

@[simp] theorem integralTensorToCompletedSpace_tmul
    (v : HeightOneSpectrum R) (a : v.adicCompletionIntegers K) (x : V) :
    integralTensorToCompletedSpace v (a ⊗ₜ[(v.valuation K).valuationSubring] x) =
      (a : v.adicCompletion K) ⊗ₜ[K] x := rfl

end Tensor

section Carriers

open NormEuclidean.CompletedIntegralLattice

variable {V : Type*} [AddCommGroup V] [Module K V]
variable (A : Subring K) [IsDedekindDomain A] [IsFractionRing A K]

/-- Integral base change of the localized span gives exactly the project's completed carrier. -/
theorem map_baseChange_span_eq_carrier (v : HeightOneSpectrum A) (L : Submodule A V) :
    ((Submodule.span (v.valuation K).valuationSubring (L : Set V)).baseChange
      (v.adicCompletionIntegers K)).map (integralTensorToCompletedSpace v) = carrier A v L := by
  rw [Submodule.baseChange_span, Submodule.map_span]
  simp only [Set.image_image]
  rfl

/-- Faithfully flat descent recovers the two valuation-ring spans from completed equality. -/
theorem valuation_span_eq_of_completed_carrier_eq
    (v : HeightOneSpectrum A) {L M : Submodule A V}
    (h : carrier A v L = carrier A v M) :
    Submodule.span (v.valuation K).valuationSubring (L : Set V) =
      Submodule.span (v.valuation K).valuationSubring (M : Set V) := by
  apply Submodule.baseChange_injective (A := v.adicCompletionIntegers K)
  apply Submodule.map_injective_of_injective (integralTensorToCompletedSpace_injective v)
  simpa only [map_baseChange_span_eq_carrier] using h

instance valuationSpaceTower (v : HeightOneSpectrum A) :
    IsScalarTower A (v.valuation K).valuationSubring V where
  smul_assoc a b x := by
    change ((a : K) * (b : K)) • x = (a : K) • (b : K) • x
    exact mul_smul _ _ _

instance valuationSpaceLocalized (v : HeightOneSpectrum A) :
    IsLocalizedModule v.asIdeal.primeCompl (LinearMap.id : V →ₗ[A] V) :=
  isLocalizedModule_id v.asIdeal.primeCompl V (v.valuation K).valuationSubring

/-- Equality at the actual completion recovers equality of the localizations in the global space. -/
theorem localized_eq_of_completed_carrier_eq
    (v : HeightOneSpectrum A) {L M : Submodule A V}
    (h : carrier A v L = carrier A v M) :
    L.localized' (v.valuation K).valuationSubring v.asIdeal.primeCompl LinearMap.id =
      M.localized' (v.valuation K).valuationSubring v.asIdeal.primeCompl LinearMap.id := by
  simpa only [Submodule.localized'_eq_span, LinearMap.id_coe, Set.image_id]
    using valuation_span_eq_of_completed_carrier_eq A v h

/-- Every maximal ideal of a non-field Dedekind domain is a finite place. -/
abbrev maximalPlace (hA : ¬ IsField A) (P : Ideal A) [hP : P.IsMaximal] :
    HeightOneSpectrum A :=
  ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP hA⟩

/-- The actual completed carriers at all finite places determine the global
submodule. No finite-generation, fullness, or quadratic-integrality input is needed. -/
theorem submodule_eq_of_completed_carriers_eq (hA : ¬ IsField A)
    {L M : Submodule A V}
    (h : ∀ v : HeightOneSpectrum A, carrier A v L = carrier A v M) : L = M := by
  exact @Submodule.eq_of_localization_maximal A V _ _ _
    (fun P _ ↦ ((maximalPlace A hA P).valuation K).valuationSubring) _ _
    (fun P _ ↦ valuationSubringLocalization (maximalPlace A hA P))
    (fun _ _ ↦ V) _ _ _ _
    (fun _ _ ↦ (LinearMap.id : V →ₗ[A] V))
    (fun P _ ↦ valuationSpaceLocalized A (V := V) (maximalPlace A hA P)) L M
    (fun P _ ↦ localized_eq_of_completed_carrier_eq A (maximalPlace A hA P) (h _))

end Carriers

end NormEuclidean.CompletionDescent
