/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import NormEuclidean.ChapterX.LocalNormUnits
import NormEuclidean.ChapterX.ExtensionNormComponents

/-!
# The unconditional norm on actual extension idèles

The local unit theorem is proved at every finite place by compactness and
continuity of the determinant norm. The finite products over places above a
base place therefore belong to the restricted product, with no good-place
or local-integrality input. Assembly follows the construction in HeADC's
NumberFieldExtensionIdeleNormAssembly, discharging its arithmetic premise.

Compatibility with the global norm on principal idèles and the quadratic
norm-index formula are separate obligations, not conclusions of assembly.
-/

noncomputable section

namespace NormEuclidean.ExtensionIdeleNorm

open scoped NumberField WithZero
open IsDedekindDomain

universe u
variable {K E : Type u} [Field K] [NumberField K]
  [Field E] [NumberField E] [Algebra K E]

/-- A local field norm preserves valuation units at every finite place above a base place. -/
theorem finitePlaceAboveNormUnits_valuation_one
    (p : HeightOneSpectrum (𝓞 K)) (w : FinitePlacesAbove (E := E) p)
    (z : (w.1.adicCompletion E)ˣ) (hz : Valued.v (z : w.1.adicCompletion E) = 1) :
    Valued.v ((finitePlaceAboveNormUnits p w z : (p.adicCompletion K)ˣ) :
      p.adicCompletion K) = 1 := by
  letI : NontriviallyNormedField (p.adicCompletion K) :=
    Valued.toNontriviallyNormedField (p.adicCompletion K) ℤᵐ⁰
  letI : Algebra (p.adicCompletion K) (w.1.adicCompletion E) := finitePlaceAboveAlgebra p w
  letI : ContinuousSMul (p.adicCompletion K) (w.1.adicCompletion E) :=
    ⟨((finitePlaceAboveCompletionMap_continuous p w).comp continuous_fst).mul
      continuous_snd⟩
  letI : Module.Finite (p.adicCompletion K) (w.1.adicCompletion E) :=
    finitePlaceAbove_moduleFinite p w
  let S : Subring (w.1.adicCompletion E) := (w.1.adicCompletionIntegers E).toSubring
  letI : CompactSpace S := CompletionHensel.compact_completed_integers w.1
  have hzS : (z : w.1.adicCompletion E) ∈ S := hz.le
  have hziS : ((z⁻¹ : (w.1.adicCompletion E)ˣ) : w.1.adicCompletion E) ∈ S := by
    change Valued.v (((z⁻¹ : (w.1.adicCompletion E)ˣ) : w.1.adicCompletion E)) ≤ 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, hz, inv_one]
  have hn := LocalNormUnits.norm_eq_one_of_unit_in_compact_subring
    (Algebra.norm (p.adicCompletion K)) LocalNormUnits.continuous_algebra_norm S z hzS hziS
  change Valued.v (Algebra.norm (p.adicCompletion K) (z : w.1.adicCompletion E)) = 1
  apply le_antisymm
  · exact Valued.toNormedField.norm_le_one_iff.mp hn.le
  · exact Valued.toNormedField.one_le_norm_iff.mp hn.ge

/-- The finite products of local norms are units at almost every base finite place. -/
theorem extensionIdeleNormComponent_eventually_unit (j : NumberFieldIdele E) :
    ∀ᶠ p : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      Valued.v ((finitePlaceExtensionIdeleNormComponent p j :
        (p.adicCompletion K)ˣ) : p.adicCompletion K) = 1 := by
  classical
  filter_upwards [extensionIdele_eventually_all_finitePlacesAbove_units (K := K) j]
    with p hs
  change Valued.v ((∏ w : FinitePlacesAbove (E := E) p,
    finitePlaceAboveNormUnits p w (ideleFiniteComponent w.1 j) :
      (p.adicCompletion K)ˣ) : p.adicCompletion K) = 1
  rw [Units.coe_prod, map_prod]
  apply Finset.prod_eq_one
  intro w _
  exact finitePlaceAboveNormUnits_valuation_one p w (ideleFiniteComponent w.1 j) (hs w)

/-- The actual restricted product of the finite norm components. -/
def extensionFiniteAdeleNormUnits :
    NumberFieldIdele E →* (FiniteAdeleRing (𝓞 K) K)ˣ where
  toFun j := RestrictedProduct.mkUnit
    (fun p ↦ finitePlaceExtensionIdeleNormComponent p j) (by
      filter_upwards [extensionIdeleNormComponent_eventually_unit (K := K) j] with p hp
      exact (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one).mpr hp)
  map_one' := by
    apply Units.ext
    apply RestrictedProduct.ext
    intro p
    change ((finitePlaceExtensionIdeleNormComponent p (1 : NumberFieldIdele E) :
      (p.adicCompletion K)ˣ) : p.adicCompletion K) = 1
    simp
  map_mul' j k := by
    apply Units.ext
    apply RestrictedProduct.ext
    intro p
    change ((finitePlaceExtensionIdeleNormComponent p (j * k) :
      (p.adicCompletion K)ˣ) : p.adicCompletion K) =
        (finitePlaceExtensionIdeleNormComponent p j : p.adicCompletion K) *
        (finitePlaceExtensionIdeleNormComponent p k : p.adicCompletion K)
    simp

/-- The infinite norm components assembled into the infinite adèle unit group. -/
def extensionInfiniteAdeleNormUnits :
    NumberFieldIdele E →* (NumberField.InfiniteAdeleRing K)ˣ where
  toFun j := MulEquiv.piUnits.symm (fun v ↦ infinitePlaceExtensionIdeleNormComponent v j)
  map_one' := by
    apply MulEquiv.piUnits.injective
    funext v
    change infinitePlaceExtensionIdeleNormComponent v (1 : NumberFieldIdele E) = 1
    simp
  map_mul' j k := by
    apply MulEquiv.piUnits.injective
    funext v
    change infinitePlaceExtensionIdeleNormComponent v (j * k) =
      infinitePlaceExtensionIdeleNormComponent v j *
        infinitePlaceExtensionIdeleNormComponent v k
    simp [map_mul]

/-- The norm on full extension idèles, with no additional arithmetic hypothesis. -/
def extensionIdeleNorm : NumberFieldIdele E →* NumberFieldIdele K :=
  MulEquiv.prodUnits.symm.toMonoidHom.comp
    (extensionInfiniteAdeleNormUnits.prod extensionFiniteAdeleNormUnits)

/-- The assembled idèle norm has the stated actual finite components. -/
theorem ideleFiniteComponent_extensionIdeleNorm
    (p : HeightOneSpectrum (𝓞 K)) (j : NumberFieldIdele E) :
    ideleFiniteComponent p (extensionIdeleNorm (K := K) j) =
      finitePlaceExtensionIdeleNormComponent p j := rfl

/-- The assembled idèle norm has the stated actual infinite components. -/
theorem ideleInfiniteComponent_extensionIdeleNorm
    (v : NumberField.InfinitePlace K) (j : NumberFieldIdele E) :
    ideleInfiniteComponent v (extensionIdeleNorm (K := K) j) =
      infinitePlaceExtensionIdeleNormComponent v j := rfl

end NormEuclidean.ExtensionIdeleNorm
