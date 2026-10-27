import NormEuclidean.ChapterX.SmallCompletedModules
import NormEuclidean.ChapterX.ComplementIntersection
import NormEuclidean.ChapterX.RegularSublatticePatching

/-!
# The constructed small complementary module in O'Meara 104:3, step 3

The module on the subspace is the literal intersection with the original
raw finite full module. A supported scalar shrinks its completed carriers
at the targets and is a unit at all other finite primes. The image in the
original completed ambient space satisfies the prescribed zero neighborhoods.
-/

noncomputable section

namespace NormEuclidean.SmallComplement

open IsDedekindDomain CompletedIntegralLattice ComplementIntersection Filter Topology
open scoped NormEuclidean.OrthogonalTopology

variable {K V : Type*} [Field K] [NumberField K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A finite full complementary module is constructed from the actual
intersection. Its whole completed image is small, it lies in the original
module, and its completed carrier agrees with the intersection off the targets. -/
theorem exists_small_on_subspace (L : Submodule (integerSubring K) V) (hLfg : L.FG)
    (hL : Submodule.span K (L : Set V) = ⊤) (U : Submodule K V)
    (T : Finset (HeightOneSpectrum (integerSubring K)))
    (Y : (v : T) → Set (Space (V := V) (integerSubring K) v.1))
    (hY : ∀ v, Y v ∈ 𝓝 0) :
    ∃ M : Submodule (integerSubring K) U, M.FG ∧ Submodule.span K (M : Set U) = ⊤ ∧
      (∀ x ∈ M, (x : V) ∈ L) ∧
      (∀ v : T, ∀ z ∈ carrier (integerSubring K) v.1 M,
        U.subtype.baseChange (LocalField (integerSubring K) v.1) z ∈ Y v) ∧
      ∀ v : HeightOneSpectrum (integerSubring K), v ∉ T →
        carrier (integerSubring K) v M =
          carrier (integerSubring K) v (onSubspace (integerSubring K) L U) := by
  let f (v : T) := U.subtype.baseChange (LocalField (integerSubring K) v.1)
  have hpre (v : T) : f v ⁻¹' Y v ∈ 𝓝 (0 : Space (V := U) (integerSubring K) v.1) := by
    have hf : Continuous (f v) := IsModuleTopology.continuous_of_linearMap (f v)
    apply hf.continuousAt.preimage_mem_nhds
    simpa only [map_zero] using hY v
  obtain ⟨M, hMfg, hM, hMN, hMY, hout⟩ := SmallCompletedModules.exists_small_module
    (onSubspace (integerSubring K) L U) (onSubspace_fg (integerSubring K) L hLfg U)
    (onSubspace_full (integerSubring K) L hL U) T (fun v ↦ f v ⁻¹' Y v) hpre
  exact ⟨M, hMfg, hM, fun x hx ↦ onSubspace_le (integerSubring K) L U x (hMN hx),
    fun v _ hz ↦ hMY v hz, hout⟩

end NormEuclidean.SmallComplement
