import NormEuclidean.ChapterX.CompletedSubspaceIntersection
import NormEuclidean.ChapterX.SmallComplement

/-!
# Small complementary modules with the literal local intersection

The completed intersection identity removes the comparison premise in the
patching step of 104:3. Off the target set the constructed module is exactly
the preimage of the original local lattice under the completed inclusion.
-/

noncomputable section

namespace NormEuclidean.CompletedSmallComplement

open IsDedekindDomain CompletedIntegralLattice Filter Topology
open scoped NormEuclidean.OrthogonalTopology

variable {K V : Type*} [Field K] [NumberField K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The entire complementary module is small at the targets and equals
the actual local intersection at every other finite place. -/
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
          (carrier (integerSubring K) v L).comap
            ((U.subtype.baseChange (LocalField (integerSubring K) v)).restrictScalars
              (LocalRing (integerSubring K) v)) := by
  obtain ⟨M, hfg, hfull, hML, hMY, hout⟩ :=
    SmallComplement.exists_small_on_subspace L hLfg hL U T Y hY
  refine ⟨M, hfg, hfull, hML, hMY, fun v hv ↦ ?_⟩
  rw [hout v hv, CompletedSubspaceIntersection.carrier_onSubspace]

end NormEuclidean.CompletedSmallComplement
