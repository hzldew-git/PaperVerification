import NormEuclidean.NormalizedSmallFrames
import NormEuclidean.PositivePairingBounds

/-!
# Finitely many possible polar matrices of norm-Euclidean lattice frames

For a fixed totally real field and rank, the original Euclidean hypotheses
and nonnegative real values give a finite set of actual polar matrices
covering full field bases inside every lattice. The lattice is not assumed
free. This result controls ambient forms; integral overmodules require the
separate finite-interval argument.
-/

noncomputable section

namespace NormEuclidean.FinitePolarFrames

open Module PositivePairingBounds

variable {K : Type*} [Field K] [NumberField K]

omit [Field K] [NumberField K] in
/-- Matrices whose every entry is in a fixed finite set form a finite set. -/
theorem finite_matrices (n : ℕ) (Ψ : Set K) (hΨ : Ψ.Finite) :
    {M : Matrix (Fin n) (Fin n) K | ∀ i j, M i j ∈ Ψ}.Finite := by
  classical
  letI : Finite Ψ := hΨ
  let f : (Fin n → Fin n → Ψ) → Matrix (Fin n) (Fin n) K := fun A i j ↦ (A i j : K)
  have heq : {M : Matrix (Fin n) (Fin n) K | ∀ i j, M i j ∈ Ψ} = Set.range f := by
    ext M
    constructor
    · intro h
      exact ⟨fun i j ↦ ⟨M i j, h i j⟩, rfl⟩
    · rintro ⟨A, rfl⟩
      exact fun i j ↦ (A i j).property
  rw [heq]
  exact Set.finite_range f

/-- A finite list of actual polar matrices covers all Euclidean lattices of the given rank.
The frame is contained in the original module and no classification table is assumed. -/
theorem exists_finite_matrices [NumberField.IsTotallyReal K] (n : ℕ) :
    ∃ S : Set (Matrix (Fin n) (Fin n) K), S.Finite ∧
      ∀ (V : Type*) [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)
        (L : Lattice (integerSubring K) Q), Q.Anisotropic →
        HasNumberFieldApproximation Q L.carrier → TotallyNonnegative Q →
        Module.finrank K V = n →
          ∃ b : Basis (Fin n) K V, (∀ i, b i ∈ L.carrier) ∧
            (fun i j ↦ Q.polarBilin (b i) (b j)) ∈ S := by
  obtain ⟨Φ, hΦ, _, hframe⟩ := NormalizedSmallFrames.exists_uniform_values K
  obtain ⟨Ψ, hΨ, hpolar⟩ := exists_finite_polar_values Φ hΦ
  refine ⟨{M | ∀ i j, M i j ∈ Ψ}, finite_matrices n Ψ hΨ, ?_⟩
  intro V _ _ Q L hA hE hpos hdim
  obtain ⟨b, hb⟩ := hframe V Q L hA hE
  let b' := b.reindex (finCongr hdim)
  have hb' (i : Fin n) : b' i ∈ L.carrier ∧ Q (b' i) ∈ Φ := by
    simpa only [b', Basis.reindex_apply] using hb ((finCongr hdim).symm i)
  refine ⟨b', fun i ↦ (hb' i).1, ?_⟩
  exact fun i j ↦ hpolar V Q L hA hpos _ (hb' i).1 _ (hb' j).1 (hb' i).2 (hb' j).2

end NormEuclidean.FinitePolarFrames
