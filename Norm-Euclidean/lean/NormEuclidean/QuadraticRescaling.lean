import NormEuclidean.Cancellation
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# Common rescaling of integral quadratic lattices

This file isolates the elementary step needed when an argument first replaces a
quadratic form by a common nonzero scalar multiple and later returns to the
original form.  The carrier submodules are unchanged.  Thus the result proves
that an integral isometry between `a • Q` and `a • Q'` is exactly an integral
isometry between `Q` and `Q'` when `a ≠ 0`.

In particular, over a field of characteristic zero, an isometry after doubling
the two quadratic forms descends to an isometry before doubling.
-/

namespace NormEuclidean

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable {R : Subring K} {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
variable {L : Submodule R V} {L' : Submodule R W}

namespace QuadraticIsometry

/-- An ambient quadratic isometry remains an isometry after common scalar
rescaling. -/
def rescale (a : K) (e : Q.IsometryEquiv Q') :
    (a • Q).IsometryEquiv (a • Q') where
  toLinearEquiv := e.toLinearEquiv
  map_app' v := by
    change a * Q' (e v) = a * Q v
    rw [e.map_app]

/-- Cancel a common nonzero scalar from an ambient quadratic isometry. -/
def of_rescale (a : K) (ha : a ≠ 0)
    (e : (a • Q).IsometryEquiv (a • Q')) : Q.IsometryEquiv Q' where
  toLinearEquiv := e.toLinearEquiv
  map_app' v := by
    apply mul_left_cancel₀ ha
    change a * Q' (e v) = a * Q v
    exact e.map_app v

/-- Equivalence of quadratic spaces is invariant under common nonzero
rescaling. -/
theorem equivalent_rescale_iff (a : K) (ha : a ≠ 0) :
    (a • Q).Equivalent (a • Q') ↔ Q.Equivalent Q' :=
  ⟨fun ⟨e⟩ => ⟨of_rescale a ha e⟩, fun ⟨e⟩ => ⟨rescale a e⟩⟩

end QuadraticIsometry

namespace Lattice

/-- Keep the carrier of an integral lattice and multiply its quadratic form by
an integral scalar. -/
def rescale (a : R) (M : Lattice R Q) : Lattice R ((a : K) • Q) where
  carrier := M.carrier
  finite := M.finite
  full := M.full
  integral v hv := by
    change (a : K) * Q v ∈ R
    exact R.mul_mem a.property (M.integral v hv)

@[simp] theorem rescale_carrier (a : R) (M : Lattice R Q) :
    (M.rescale a).carrier = M.carrier := rfl

end Lattice

namespace LatticeIsometry

/-- A lattice isometry remains an isometry after multiplying both quadratic
forms by the same scalar. -/
def rescale (a : K) (φ : LatticeIsometry Q Q' L L') :
    LatticeIsometry (a • Q) (a • Q') L L' where
  toLinearEquiv := φ.toLinearEquiv
  q_eq v := by
    simp only [QuadraticMap.smul_apply, smul_eq_mul]
    rw [φ.q_eq]
  mem_iff := φ.mem_iff

/-- Cancel a common nonzero scalar from an isometry of integral quadratic
lattices.  The same linear equivalence and the same carrier equivalence are
used; only equality of quadratic values requires cancellation. -/
def of_rescale (a : K) (ha : a ≠ 0)
    (φ : LatticeIsometry (a • Q) (a • Q') L L') :
    LatticeIsometry Q Q' L L' where
  toLinearEquiv := φ.toLinearEquiv
  q_eq v := by
    apply mul_left_cancel₀ ha
    simpa only [QuadraticMap.smul_apply, smul_eq_mul] using φ.q_eq v
  mem_iff := φ.mem_iff

/-- Existence of an integral lattice isometry is invariant under common
rescaling by a nonzero field element. -/
theorem rescale_nonempty_iff (a : K) (ha : a ≠ 0) :
    Nonempty (LatticeIsometry (a • Q) (a • Q') L L') ↔
      Nonempty (LatticeIsometry Q Q' L L') := by
  constructor
  · rintro ⟨φ⟩
    exact ⟨of_rescale a ha φ⟩
  · rintro ⟨φ⟩
    exact ⟨rescale a φ⟩

/-- The common doubling used for `L^(2)` does not change the integral
isometry relation in characteristic zero. -/
theorem two_rescale_nonempty_iff [CharZero K] :
    Nonempty (LatticeIsometry ((2 : K) • Q) ((2 : K) • Q') L L') ↔
      Nonempty (LatticeIsometry Q Q' L L') :=
  rescale_nonempty_iff 2 (by norm_num)

end LatticeIsometry

end NormEuclidean
