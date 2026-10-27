import NormEuclidean.AmbientVolumeInduction
import NormEuclidean.FixedSpaceVolumeRepresentatives
import NormEuclidean.FixedFieldClassSet

/-!
# Actual finite fixed-rank lattice models from finite volume ideals

Finite ambient forms and the fixed-space class theorem are assembled using
actual quadratic isometries that preserve the entire lattice carrier.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.FixedRankVolumeFiniteness

open Module FixedFieldRankFiniteness FixedSpaceVolumeRepresentatives
open scoped NumberField Classical nonZeroDivisors

universe v
variable {K : Type*} [Field K] [NumberField K]

/-- Actual finite representatives, uniformly over all ambient fixed-rank spaces.
There is no freeness, positivity, Euclidean or class-number hypothesis. -/
theorem exists_finite_models (n : ℕ) (S : Set (FractionalIdeal (integerSubring K)⁰ K))
    (hS : S.Finite) :
    ∃ A : Set (Model K n), A.Finite ∧
      (∀ M ∈ A, M.1.Anisotropic ∧ M.2.volumeIdeal ∈ S) ∧
      ∀ (V : Type v) [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)
        (L : Lattice (integerSubring K) Q), Q.Anisotropic → finrank K V = n →
        L.volumeIdeal ∈ S →
        ∃ M ∈ A, Nonempty (LatticeIsometry Q M.1 L.carrier M.2.carrier) := by
  obtain ⟨F, hF, hforms⟩ := AmbientVolumeInduction.exists_finite_forms n S hS
  let F' : Set (QuadraticForm K (Fin n → K)) := {P ∈ F | P.Anisotropic}
  have hF' : F'.Finite := hF.subset fun _ h ↦ h.1
  letI : Finite F' := hF'
  choose A hA hvol hcover using fun P : F' ↦
    exists_finite_representatives P.1 P.2.2 S hS
  let T : Set (Model K n) := ⋃ P : F', Sigma.mk P.1 '' A P
  have hT : T.Finite := Set.finite_iUnion fun P ↦ (hA P).image _
  refine ⟨T, hT, ?_, ?_⟩
  · intro M hM
    obtain ⟨P, N, hN, rfl⟩ := Set.mem_iUnion.mp hM
    exact ⟨P.2.2, hvol P N hN⟩
  · intro V _ _ Q L hAQ hr hLS
    obtain ⟨b, hb⟩ := hforms V Q L hAQ hr hLS
    let P := Q.basisRepr b
    let e := Q.isometryEquivBasisRepr b
    have hAP : P.Anisotropic := by
      intro x hx
      have hy : Q (e.symm x) = 0 := (e.symm.map_app x).trans hx
      have hz := congrArg e (hAQ _ hy)
      simpa using hz
    let p : F' := ⟨P, hb, hAP⟩
    let M := IntegralFrameIntervals.map L e
    have hM : M.volumeIdeal ∈ S := by rw [map_volume L e]; exact hLS
    obtain ⟨N, hN, ⟨i⟩⟩ := hcover p M hM
    refine ⟨⟨P, N⟩, Set.mem_iUnion_of_mem p ⟨N, hN, rfl⟩, ?_⟩
    exact ⟨(IntegralFrameIntervals.mapIsometry L e).compose i⟩

/-- Equality in the existing class quotient is genuine integral isometry.
The finite representatives therefore give a finite set of actual classes. -/
theorem finite_classes (n : ℕ) (S : Set (FractionalIdeal (integerSubring K)⁰ K))
    (hS : S.Finite) :
    {c : FixedFieldClassSet.ClassSet K n | ∃ M : Model K n,
      M.1.Anisotropic ∧ M.2.volumeIdeal ∈ S ∧ FixedFieldClassSet.classOf K M = c}.Finite := by
  obtain ⟨A, hA, _, hcover⟩ := exists_finite_models n S hS
  apply (hA.image (FixedFieldClassSet.classOf K)).subset
  rintro c ⟨M, hMA, hMV, rfl⟩
  obtain ⟨N, hN, hi⟩ := hcover (Fin n → K) M.1 M.2 hMA (by simp) hMV
  exact ⟨N, hN, ((FixedFieldClassSet.classOf_eq_iff K M N).mpr hi).symm⟩

end NormEuclidean.FixedRankVolumeFiniteness
