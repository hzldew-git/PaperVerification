import NormEuclidean.PositiveLatticeVectors
import NormEuclidean.ProperSpinor

/-!
# Actual finite orthogonal automorphism groups of positive integral lattices

The group is the full integral stabilizer, including determinant minus one.
Its action on an ambient field frame is faithful and each image lies in an
actual finite fixed-value fiber. No Euclidean or freeness assumption is used.
-/

noncomputable section

namespace NormEuclidean.PositiveLatticeAutomorphisms

open Module PositivePairingBounds ProperSpinor

variable {K V : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
  [Invertible (2 : K)] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

/-- The ordinary orthogonal automorphism group is finite for every positive integral lattice. -/
theorem finite_group (L : Lattice (integerSubring K) Q) (hpos : TotallyPositive Q) :
    Finite (integralStabilizer Q L.carrier) := by
  classical
  let F := L.integralDiagonalFrame
  let T (i : Fin (finrank K V)) := {x : V // x ∈ L.carrier ∧ Q x = Q (F.basis i)}
  have hT (i) : Finite (T i) :=
    (PositiveLatticeVectors.finite_value_fiber L hpos (Q (F.basis i))).to_subtype
  letI : ∀ i, Finite (T i) := hT
  let f : integralStabilizer Q L.carrier → ∀ i, T i := fun g i ↦
    ⟨g.1.1 (F.basis i), (g.2 _).mpr (F.basis_mem i), g.1.2 _⟩
  apply Finite.of_injective f
  intro g h heq
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply F.basis.ext
  intro i
  exact congrArg (fun v ↦ ((v i : T i) : V)) heq

/-- The scalar minus identity is an actual ordinary integral isometry. -/
def negIdentity (L : Lattice (integerSubring K) Q) : integralStabilizer Q L.carrier :=
  ⟨⟨LinearEquiv.neg K, fun x ↦ Q.map_neg x⟩, fun x ↦ L.carrier.neg_mem_iff⟩

/-- In positive rank the two signs are distinct, including at dyadic places. -/
theorem negIdentity_ne_one [Nontrivial V] (L : Lattice (integerSubring K) Q) :
    negIdentity L ≠ 1 := by
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have heq := congrArg (fun g : integralStabilizer Q L.carrier ↦ g.1.1 x) h
  change -x = x at heq
  have hz : (2 : K) • x = 0 := by
    rw [two_smul]
    exact (congrArg (fun y : V ↦ x + y) heq).symm.trans (add_neg_cancel x)
  exact hx ((smul_eq_zero.mp hz).resolve_left (by norm_num))

/-- Every positive-rank positive lattice has at least two ordinary orthogonal automorphisms. -/
theorem two_le_card [Nontrivial V] (L : Lattice (integerSubring K) Q)
    (hpos : TotallyPositive Q) : 2 ≤ Nat.card (integralStabilizer Q L.carrier) := by
  letI := finite_group L hpos
  letI : Nontrivial (integralStabilizer Q L.carrier) :=
    ⟨⟨negIdentity L, 1, negIdentity_ne_one L⟩⟩
  exact Finite.one_lt_card

end NormEuclidean.PositiveLatticeAutomorphisms
