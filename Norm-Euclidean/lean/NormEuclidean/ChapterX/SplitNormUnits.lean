import NormEuclidean.ChapterX.QuadraticExtensionNorm
import Mathlib.Algebra.Ring.Pi

/-!
# Split quadratic norm preimages

The standard split norm preimage has image either one or the target under
every homomorphism to a field. This gives simultaneous unit preimages in
all split factors without asserting that every preimage is a unit there.
-/

noncomputable section

namespace NormEuclidean.SplitNormUnits

open QuadraticExtensionNorm
open scoped QuadraticAlgebra

/-- A product of nontrivial rings can be a domain only when its index type
has at most one element. -/
theorem subsingleton_of_pi_domain {ι : Type*} (A : ι → Type*)
    [∀ i, Ring (A i)] [∀ i, Nontrivial (A i)] [IsDomain ((i : ι) → A i)] :
    Subsingleton ι := by
  classical
  constructor
  intro i j
  by_contra hij
  let x : (k : ι) → A k := Pi.single i 1
  let y : (k : ι) → A k := Pi.single j 1
  have hx : x ≠ 0 := by
    intro h
    have := congrFun h i
    simp [x] at this
  have hy : y ≠ 0 := by
    intro h
    have := congrFun h j
    simp [y] at this
  have hxy : x * y = 0 := by
    funext k
    by_cases hk : k = i
    · subst k
      simp [x, y, hij]
    · simp [x, hk]
  exact (mul_eq_zero.mp hxy).elim hx hy

/-- A split quadratic norm has a preimage whose every field image is
either one or the embedded target. This is stronger than norm surjectivity. -/
theorem exists_split_preimage {F : Type*} [Field F] [CharZero F]
    (theta a : Fˣ) (htheta : IsSquare theta) :
    ∃ z : (QuadraticAlgebra F (theta : F) 0)ˣ,
      Algebra.norm F (z : QuadraticAlgebra F (theta : F) 0) = (a : F) ∧
      ∀ (A : Type*) [Field A] [Algebra F A]
        (f : QuadraticAlgebra F (theta : F) 0 →ₐ[F] A),
        f (z : QuadraticAlgebra F (theta : F) 0) = 1 ∨
          f (z : QuadraticAlgebra F (theta : F) 0) = algebraMap F A (a : F) := by
  obtain ⟨r, hr⟩ := htheta
  have htheta : (theta : F) = (r : F) ^ 2 := by
    rw [hr]
    simp [pow_two]
  let z : QuadraticAlgebra F (theta : F) 0 :=
    ⟨((a : F) + 1) / 2, ((a : F) - 1) / (2 * (r : F))⟩
  have hn : Algebra.norm F z = (a : F) := by
    rw [algebra_norm_eq_quadraticAlgebra_norm]
    dsimp [z]
    simp only [QuadraticAlgebra.norm_def]
    rw [htheta]
    field_simp [Units.ne_zero r]
    ring
  have hp : (z - 1) * (z - algebraMap F _ (a : F)) = 0 := by
    ext <;> simp [z, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, htheta] <;>
      field_simp [Units.ne_zero r] <;> ring
  have hu : IsUnit z := by
    apply QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr
    rw [← algebra_norm_eq_quadraticAlgebra_norm theta z, hn]
    exact a.isUnit
  refine ⟨hu.unit, by simpa only [hu.unit_spec] using hn, ?_⟩
  intro A _ _ f
  have h := congrArg f hp
  rw [map_mul, map_sub, map_sub, map_one, map_zero, f.commutes] at h
  simpa only [hu.unit_spec, sub_eq_zero] using mul_eq_zero.mp h

end NormEuclidean.SplitNormUnits
