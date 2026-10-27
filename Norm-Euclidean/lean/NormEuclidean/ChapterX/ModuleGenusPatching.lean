import NormEuclidean.ChapterX.GenusPatching

/-!
# Genus patching for finite full modules without norm integrality

O'Meara's lattice convention permits fractional quadratic values. This
module proves the local-image patching construction for finite full modules,
without bundling a norm-integral lattice or assuming an integral quadratic value.
-/

noncomputable section

namespace NormEuclidean.ModuleGenusPatching

open ProperSpinor CompletedIntegralLattice IsDedekindDomain OrthogonalTopology
open OrthogonalWeakApproximationAt Filter Topology
open scoped NormEuclidean.OrthogonalTopology

section Transport

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (R : Subring K) (Q : QuadraticForm K V)

/-- Transport an arbitrary module through an actual ambient orthogonal map. -/
def transportModule (g : ambientGroup Q) (L : Submodule R V) : Submodule R V :=
  L.map (g.1.toLinearMap.restrictScalars R)

theorem mem_transportModule (g : ambientGroup Q) (L : Submodule R V) (x : V) :
    g.1 x ∈ transportModule R Q g L ↔ x ∈ L := by
  constructor
  · rintro ⟨y, hy, heq⟩
    have hxy : y = x := g.1.injective heq
    exact hxy ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem transportModule_full (g : ambientGroup Q) (L : Submodule R V)
    (hL : Submodule.span K (L : Set V) = ⊤) :
    Submodule.span K (transportModule R Q g L : Set V) = ⊤ := by
  rw [transportModule, Submodule.map_coe]
  change Submodule.span K (g.1.toLinearMap '' (L : Set V)) = ⊤
  rw [Submodule.span_image, hL, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr g.1.surjective

/-- Finite generation and fullness give finite dimension without any
quadratic integrality hypothesis. -/
theorem finiteDimensional_of_fg_full (L : Submodule R V) (hLfg : L.FG)
    (hL : Submodule.span K (L : Set V) = ⊤) : FiniteDimensional K V := by
  obtain ⟨s, hs⟩ := hLfg
  have hspan : Submodule.span K (s : Set V) = ⊤ := by
    rw [← Submodule.span_span_of_tower R, hs]
    exact hL
  exact Module.finite_def.mpr (show (⊤ : Submodule K V).FG from ⟨s, hspan⟩)

end Transport

section NumberField

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (Q : QuadraticForm K V)

/-- Realize one local image by a global transport of an arbitrary finite
full module. Norm integrality is not a premise. -/
theorem exists_global_transport_module_local_image (hQ : Q.polarBilin.Nondegenerate)
    (hpos : 0 < Module.finrank K V) (L : Submodule (integerSubring K) V) (hLfg : L.FG)
    (hL : Submodule.span K (L : Set V) = ⊤) (v : HeightOneSpectrum (integerSubring K))
    (a : ambientGroup (form (integerSubring K) v Q)) :
    ∃ g : ambientGroup Q, ∀ x,
      a.1 x ∈ carrier (integerSubring K) v (transportModule (integerSubring K) Q g L) ↔
        x ∈ carrier (integerSubring K) v L := by
  let U := {b : ambientGroup (form (integerSubring K) v Q) |
    a⁻¹ * b ∈ integralStabilizer (form (integerSubring K) v Q)
      (carrier (integerSubring K) v L)}
  have hcaropen := isOpen_of_full (LocalRing (integerSubring K) v)
    (isOpen_localRing (integerSubring K) v) (carrier (integerSubring K) v L)
    (carrier_full (integerSubring K) v L hL)
  have hopen : IsOpen U :=
    (isOpen_integralStabilizer _ _ (carrier_fg (integerSubring K) v L hLfg) hcaropen).preimage
      (continuous_const.mul continuous_id)
  have hU : U ∈ 𝓝 a := hopen.mem_nhds (by simp [U])
  obtain ⟨g, hg⟩ := exists_global_orthogonal_weak_at Q hQ hpos v a U hU
  refine ⟨g, ?_⟩
  intro x
  let b := localizeAmbient Q g v
  let y := b.1.symm (a.1 x)
  have ht := equiv_carrier (integerSubring K) v L
    (transportModule (integerSubring K) Q g L) g.1
    (mem_transportModule (integerSubring K) Q g L) y
  change b.1 y ∈ _ ↔ y ∈ _ at ht
  have ht' : a.1 x ∈ carrier (integerSubring K) v (transportModule (integerSubring K) Q g L) ↔
      y ∈ carrier (integerSubring K) v L := by
    simpa only [y, LinearEquiv.apply_symm_apply] using ht
  have hs := hg y
  have hxy : (a⁻¹ * b).1 y = x := by
    simp only [y, Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply,
      LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  change (a⁻¹ * b).1 y ∈ _ ↔ y ∈ _ at hs
  rw [hxy] at hs
  exact ht'.trans hs.symm

/-- Patch arbitrary finite full modules to exact local orthogonal images.
Finite local genus comparison is proved, even for fractional quadratic values. -/
theorem exists_module_of_local_images (hQ : Q.polarBilin.Nondegenerate)
    (hpos : 0 < Module.finrank K V) (L : Submodule (integerSubring K) V) (hLfg : L.FG)
    (hL : Submodule.span K (L : Set V) = ⊤)
    (T : Finset (HeightOneSpectrum (integerSubring K)))
    (a : (v : HeightOneSpectrum (integerSubring K)) →
      ambientGroup (form (integerSubring K) v Q)) :
    ∃ M : Submodule (integerSubring K) V, M.FG ∧ Submodule.span K (M : Set V) = ⊤ ∧
      FiniteLocallyIsometric (integerSubring K) Q Q L M ∧
      (∀ v ∈ T, ∀ x, (a v).1 x ∈ carrier (integerSubring K) v M ↔
        x ∈ carrier (integerSubring K) v L) ∧
      ∀ v ∉ T, carrier (integerSubring K) v M = carrier (integerSubring K) v L := by
  choose g hg using fun v ↦ exists_global_transport_module_local_image Q hQ hpos L hLfg hL v (a v)
  let N := fun v ↦ transportModule (integerSubring K) Q (g v) L
  obtain ⟨M, hMfg, hM, hin, hout⟩ := LocalLatticePatching.exists_patched_module (integerSubring K)
    L hLfg hL T N (fun v _ ↦ hLfg.map _) (fun v _ ↦ transportModule_full _ Q (g v) L hL)
  have hmap : ∀ v ∈ T, ∀ x, (a v).1 x ∈ carrier (integerSubring K) v M ↔
      x ∈ carrier (integerSubring K) v L := by
    intro v hv x
    rw [hin v hv]
    exact hg v x
  refine ⟨M, hMfg, hM, ?_, hmap, hout⟩
  intro v
  by_cases hv : v ∈ T
  · exact ⟨{ toLinearEquiv := (a v).1
             q_eq := (a v).2
             mem_iff := hmap v hv }⟩
  · exact ⟨{ toLinearEquiv := LinearEquiv.refl _ _
             q_eq := fun _ ↦ rfl
             mem_iff := fun x ↦ by simp only [LinearEquiv.refl_apply, hout v hv] }⟩

/-- Local inclusions into the chosen images recover global containment.
The base module and the contained module need not have integral quadratic values. -/
theorem exists_module_containing (hQ : Q.polarBilin.Nondegenerate)
    (hpos : 0 < Module.finrank K V) (L : Submodule (integerSubring K) V) (hLfg : L.FG)
    (hL : Submodule.span K (L : Set V) = ⊤) (A : Submodule (integerSubring K) V)
    (T : Finset (HeightOneSpectrum (integerSubring K)))
    (a : (v : HeightOneSpectrum (integerSubring K)) →
      ambientGroup (form (integerSubring K) v Q))
    (hin : ∀ v ∈ T, ∀ x ∈ carrier (integerSubring K) v A,
      (a v).1.symm x ∈ carrier (integerSubring K) v L)
    (hout : ∀ v ∉ T, carrier (integerSubring K) v A ≤ carrier (integerSubring K) v L) :
    ∃ M : Submodule (integerSubring K) V, M.FG ∧ Submodule.span K (M : Set V) = ⊤ ∧
      FiniteLocallyIsometric (integerSubring K) Q Q L M ∧ A ≤ M := by
  obtain ⟨M, hMfg, hM, hgen, hmap, houtside⟩ :=
    exists_module_of_local_images Q hQ hpos L hLfg hL T a
  refine ⟨M, hMfg, hM, hgen, ?_⟩
  intro x hx
  apply FixedValueVectors.mem_of_all_completed (integerSubring K)
    (NumberField.RingOfIntegers.not_isField K) M
  intro v
  by_cases hv : v ∈ T
  · have hp := (hmap v hv ((a v).1.symm (inclusion (integerSubring K) v x))).mpr
      (hin v hv _ (inclusion_mem (integerSubring K) v A hx))
    simpa only [LinearEquiv.apply_symm_apply] using hp
  · rw [houtside v hv]
    exact hout v hv (inclusion_mem (integerSubring K) v A hx)

end NumberField

end NormEuclidean.ModuleGenusPatching
