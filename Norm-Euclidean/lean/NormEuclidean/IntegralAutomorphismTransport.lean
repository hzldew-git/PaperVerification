import NormEuclidean.ChapterX.OrthogonalTransport

/-!
# Integral orthogonal automorphism groups under lattice isometry

Conjugation by the actual ambient isometry carries the entire integral
stabilizer onto the other. Its cardinal, and hence its inverse-cardinal
weight, is independent of the representative of an integral isometry class.
-/

noncomputable section

namespace NormEuclidean.IntegralAutomorphismTransport

open ProperSpinor OrthogonalTransport

variable {K V W : Type*} [Field K] [CharZero K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {Q : QuadraticForm K V} {P : QuadraticForm K W} {R : Subring K}
  {L : Submodule R V} {M : Submodule R W}

/-- Integral conjugation is a homomorphism of actual full orthogonal stabilizers. -/
def map (e : LatticeIsometry Q P L M) : integralStabilizer Q L →* integralStabilizer P M where
  toFun g := ⟨ambientMap Q P e.toLinearEquiv e.q_eq g.1, by
    intro x
    change e.toLinearEquiv (g.1.1 (e.toLinearEquiv.symm x)) ∈ M ↔ x ∈ M
    rw [e.mem_iff, g.2]
    simpa using (e.mem_iff (e.toLinearEquiv.symm x)).symm⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' g h := by apply Subtype.ext; exact map_mul _ _ _

/-- An integral quadratic isometry induces an actual multiplicative group equivalence. -/
def equiv (e : LatticeIsometry Q P L M) : integralStabilizer Q L ≃* integralStabilizer P M where
  toFun := map e
  invFun := map e.inverse
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change e.toLinearEquiv.symm
      (e.toLinearEquiv (g.1.1 (e.toLinearEquiv.symm (e.toLinearEquiv x)))) = g.1.1 x
    simp
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change e.toLinearEquiv
      (e.toLinearEquiv.symm (g.1.1 (e.toLinearEquiv (e.toLinearEquiv.symm x)))) = g.1.1 x
    simp
  map_mul' := (map e).map_mul

/-- The ordinary automorphism-group cardinal is independent of integral-isometry presentation. -/
theorem card_eq (e : LatticeIsometry Q P L M) :
    Nat.card (integralStabilizer Q L) = Nat.card (integralStabilizer P M) :=
  Nat.card_congr (equiv e).toEquiv

end NormEuclidean.IntegralAutomorphismTransport
