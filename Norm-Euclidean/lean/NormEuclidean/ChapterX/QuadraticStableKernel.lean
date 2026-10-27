import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# A conjugation-stable quadratic kernel is zero

In characteristic zero, the traces of `z` and `omega*z` recover its two
coordinates. Thus an algebra homomorphism with nontrivial target is
injective when its kernel is stable under conjugation and theta is nonzero.
This also applies when the quadratic algebra splits.
-/

noncomputable section

namespace NormEuclidean.QuadraticStableKernel

open scoped QuadraticAlgebra

variable {F A : Type*} [Field F] [CharZero F] [CommRing A] [Nontrivial A] [Algebra F A]

/-- Quadratic conjugation as a genuine algebra automorphism over the base field. -/
def conjugation (theta : F) : QuadraticAlgebra F theta 0 ≃ₐ[F] QuadraticAlgebra F theta 0 where
  toFun := star
  invFun := star
  left_inv := star_star
  right_inv := star_star
  map_add' := star_add
  map_mul' x y := by rw [star_mul, mul_comm]
  commutes' x := by ext <;> simp

/-- The trace of a quadratic element is twice its real coordinate. -/
theorem add_conjugate (theta : F) (z : QuadraticAlgebra F theta 0) :
    z + star z = algebraMap F (QuadraticAlgebra F theta 0) (2 * z.re) := by
  ext <;> simp <;> ring

/-- A conjugation-stable kernel cannot discard a split factor. -/
theorem injective_of_stable (theta : F) (htheta : theta ≠ 0)
    (f : QuadraticAlgebra F theta 0 →ₐ[F] A)
    (hstable : ∀ z, f z = 0 → f (star z) = 0) : Function.Injective f := by
  have hreal (z : QuadraticAlgebra F theta 0) (hz : f z = 0) : z.re = 0 := by
    have h : algebraMap F A (2 * z.re) = 0 := by
      rw [← f.commutes, ← add_conjugate, map_add, hz, hstable z hz, add_zero]
    have hzero : 2 * z.re = 0 :=
      (algebraMap F A).injective (h.trans (map_zero _).symm)
    exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)
  intro x y hxy
  have hz : f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hr := hreal (x - y) hz
  have hi := hreal (ω * (x - y)) (by rw [map_mul, hz, mul_zero])
  have hi0 : theta * (x - y).im = 0 := by simpa using hi
  have hi' := (mul_eq_zero.mp hi0).resolve_left htheta
  apply sub_eq_zero.mp
  exact QuadraticAlgebra.ext hr hi'

end NormEuclidean.QuadraticStableKernel
