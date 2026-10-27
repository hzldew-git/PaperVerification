import NormEuclidean.Cancellation
import Mathlib.LinearAlgebra.Reflection

/-!
# Integral reflections in vectors of unit quadratic value

These are actual ambient quadratic isometries preserving an integral submodule.
No inverse of two in the integral ring is required. This is a supporting local
construction for the spinor-norm calculation, not a definition or computation
of spinor norms and not a genus uniqueness theorem.
-/
namespace NormEuclidean.IntegralReflection
open QuadraticMap
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

/-- Reflection in an anisotropic vector, with the unhalved polar convention. -/
noncomputable def linearEquiv (v : V) (hv : Q v ≠ 0) : V ≃ₗ[K] V :=
  Module.reflection (x := v) (f := (Q v)⁻¹ • Q.polarBilin v) (by
    simp only [LinearMap.smul_apply, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar_self, smul_eq_mul]
    rw [show (2 : ℕ) • Q v = 2 * Q v by simp [two_smul, two_mul]]
    field_simp)

@[simp] theorem linearEquiv_apply (v : V) (hv : Q v ≠ 0) (x : V) :
    linearEquiv Q v hv x = x - ((Q v)⁻¹ * polar Q v x) • v := rfl

@[simp] theorem linearEquiv_self (v : V) (hv : Q v ≠ 0) :
    linearEquiv Q v hv v = -v := Module.reflection_apply_self _

/-- Every vector polar-orthogonal to the reflecting vector is fixed. -/
theorem linearEquiv_eq_self (v : V) (hv : Q v ≠ 0) (x : V)
    (hx : polar Q v x = 0) : linearEquiv Q v hv x = x := by
  simp [hx]

theorem involutive (v : V) (hv : Q v ≠ 0) :
    Function.Involutive (linearEquiv Q v hv) := Module.involutive_reflection _

theorem q_eq (v : V) (hv : Q v ≠ 0) (x : V) :
    Q (linearEquiv Q v hv x) = Q x := by
  rw [linearEquiv_apply, sub_eq_add_neg, ← neg_smul,
    QuadraticMap.map_add (Q : V → K), Q.map_smul, Q.polar_smul_right, polar_comm Q x v]
  simp only [smul_eq_mul]
  field_simp
  ring

/-- Unit quadratic value makes the ambient reflection integral, including
at residue characteristic two. -/
theorem mem (R : Subring K) (L : Submodule R V)
    (hQ : ∀ x ∈ L, Q x ∈ R) (v : V) (hvL : v ∈ L)
    (hv : Q v ≠ 0) (hinv : (Q v)⁻¹ ∈ R) {x : V} (hx : x ∈ L) :
    linearEquiv Q v hv x ∈ L := by
  rw [linearEquiv_apply]
  apply L.sub_mem hx
  have hp : polar Q v x ∈ R :=
    R.sub_mem (R.sub_mem (hQ _ (L.add_mem hvL hx)) (hQ _ hvL)) (hQ _ hx)
  exact L.smul_mem (⟨(Q v)⁻¹ * polar Q v x, R.mul_mem hinv hp⟩ : R) hvL

/-- The actual integral ambient isometry, with both directions of preservation. -/
noncomputable def isometry (R : Subring K) (L : Submodule R V)
    (hQ : ∀ x ∈ L, Q x ∈ R) (v : V) (hvL : v ∈ L)
    (hv : Q v ≠ 0) (hinv : (Q v)⁻¹ ∈ R) : LatticeIsometry Q Q L L where
  toLinearEquiv := linearEquiv Q v hv
  q_eq := q_eq Q v hv
  mem_iff := fun x => ⟨fun hx => by
    have h := mem Q R L hQ v hvL hv hinv hx
    simpa only [involutive Q v hv x] using h,
    mem Q R L hQ v hvL hv hinv⟩

end NormEuclidean.IntegralReflection
