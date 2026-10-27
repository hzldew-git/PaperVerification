import NormEuclidean.PositivePairingBounds
import NormEuclidean.IntegralDiagonalFrame
import NormEuclidean.QuadraticBaseChangeNondegenerate

/-!
# Finite fixed-value vector sets in positive integral lattices

Bounded conjugates of integral polar pairings give finitely many possible
pairing coordinates. Nondegeneracy makes those coordinates injective.
The integral module is not assumed free, principal, maximal or Euclidean.
-/

noncomputable section

namespace NormEuclidean.PositiveLatticeVectors

open Module PositivePairingBounds

variable {K V : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
  [Invertible (2 : K)] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

/-- All vectors of a specified value in a positive integral lattice form an actual finite set. -/
theorem finite_value_fiber (L : Lattice (integerSubring K) Q)
    (hpos : TotallyPositive Q) (a : K) :
    {x : V | x ∈ L.carrier ∧ Q x = a}.Finite := by
  classical
  let F := L.integralDiagonalFrame
  let Φ : Set K := insert a (Set.range fun i ↦ Q (F.basis i))
  have hΦ : Φ.Finite := (Set.finite_range _).insert a
  obtain ⟨Ψ, hΨ, hpair⟩ := exists_finite_polar_values Φ hΦ
  let T : Set V := {x | x ∈ L.carrier ∧ Q x = a}
  let f : T → (Fin (finrank K V) → Ψ) := fun x i ↦
    ⟨Q.polarBilin (F.basis i) x, hpair V Q L hpos.anisotropic hpos.nonnegative
      (F.basis i) (F.basis_mem i) x x.property.1
      (Set.mem_insert_of_mem _ (Set.mem_range_self i))
      (x.property.2 ▸ Set.mem_insert _ _)⟩
  have hB := quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hpos.anisotropic
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply hB.2
    have heq : Q.polarBilin.flip ((x : V) - y) = 0 := F.basis.ext (fun i ↦ by
      have hi := congrArg (fun v ↦ ((v i : Ψ) : K)) h
      change Q.polarBilin (F.basis i) x = Q.polarBilin (F.basis i) y at hi
      change Q.polarBilin (F.basis i) ((x : V) - y) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr hi)
    intro z
    exact congrArg (fun l : V →ₗ[K] K ↦ l z) heq
  letI : Finite Ψ := hΨ
  letI : Finite T := Finite.of_injective f hf
  exact Set.toFinite T

end NormEuclidean.PositiveLatticeVectors
