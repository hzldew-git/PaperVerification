import NormEuclidean.FinitePolarFrames
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# Finite coordinate forms over a fixed totally real field and rank

The actual polar matrix determines a quadratic form in characteristic zero.
Finite polar frames therefore give finitely many coordinate forms, with
actual field bases contained in the original integral modules.
-/

noncomputable section

namespace NormEuclidean.CoordinateFormFiniteness

open Module PositivePairingBounds

variable {K : Type*} [Field K] [NumberField K]

/-- The actual polar matrix on the coordinate vector space. -/
def polarMatrix (n : ℕ) (Q : QuadraticForm K (Fin n → K)) : Matrix (Fin n) (Fin n) K :=
  LinearMap.toMatrix₂' K Q.polarBilin

/-- In characteristic zero the polar matrix determines the entire quadratic form. -/
theorem polarMatrix_injective (n : ℕ) : Function.Injective (polarMatrix (K := K) n) := by
  intro Q P h
  apply QuadraticMap.polarBilin_injective (isUnit_iff_ne_zero.mpr (by norm_num : (2 : K) ≠ 0))
  exact (LinearMap.toMatrix₂' K).injective h

omit [NumberField K] in
/-- The coordinate polar matrix is the literal matrix of pairings of the frame vectors. -/
theorem polarMatrix_basisRepr {V : Type*} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) {n : ℕ} (b : Basis (Fin n) K V) :
    polarMatrix n (Q.basisRepr b) = fun i j ↦ Q.polarBilin (b i) (b j) := by
  have he (i : Fin n) : b.equivFun.symm (Pi.single i 1) = b i := by
    rw [Basis.equivFun_symm_apply]
    simp [Pi.single_apply]
  ext i j
  change (Q.basisRepr b).polarBilin (Pi.single i 1) (Pi.single j 1) = _
  rw [QuadraticMap.basisRepr, QuadraticMap.polarBilin_comp]
  change Q.polarBilin (b.equivFun.symm (Pi.single i 1))
    (b.equivFun.symm (Pi.single j 1)) = _
  rw [he, he]

/-- All the relevant quadratic spaces have representatives among a finite set of coordinate forms.
The rank and field are fixed; the original lattice need not be free. -/
theorem exists_finite_forms [NumberField.IsTotallyReal K] (n : ℕ) :
    ∃ F : Set (QuadraticForm K (Fin n → K)), F.Finite ∧
      ∀ (V : Type*) [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)
        (L : Lattice (integerSubring K) Q), Q.Anisotropic →
        HasNumberFieldApproximation Q L.carrier → TotallyNonnegative Q →
        Module.finrank K V = n →
          ∃ b : Basis (Fin n) K V, (∀ i, b i ∈ L.carrier) ∧ Q.basisRepr b ∈ F := by
  obtain ⟨S, hS, hcover⟩ := FinitePolarFrames.exists_finite_matrices (K := K) n
  refine ⟨polarMatrix n ⁻¹' S,
    Set.Finite.preimage (polarMatrix_injective n).injOn hS, ?_⟩
  intro V _ _ Q L hA hE hpos hdim
  obtain ⟨b, hb, hM⟩ := hcover V Q L hA hE hpos hdim
  refine ⟨b, hb, ?_⟩
  change polarMatrix n (Q.basisRepr b) ∈ S
  rw [polarMatrix_basisRepr]
  exact hM

end NormEuclidean.CoordinateFormFiniteness
