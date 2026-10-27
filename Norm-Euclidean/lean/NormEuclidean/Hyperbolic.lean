import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Explicit hyperbolic transformations

The polar form used here is `Q(x+y)-Q(x)-Q(y)`, hence is `2 B(x,y)`
in the manuscript's convention. This lets the integral formulas work
without asserting that the bilinear form itself is integral.
-/

namespace NormEuclidean

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

abbrev Hyperbolic (K V : Type*) := V × K × K

namespace Hyperbolic

variable (Q : QuadraticForm K V)

def q (z : Hyperbolic K V) : K := Q z.1 + z.2.1 * z.2.2

def e : Hyperbolic K V := (0, 1, 0)
def f : Hyperbolic K V := (0, 0, 1)

def transvection (u : V) (z : Hyperbolic K V) : Hyperbolic K V :=
  (z.1 - z.2.1 • u, z.2.1, z.2.2 + polar Q z.1 u - z.2.1 * Q u)

def swap (z : Hyperbolic K V) : Hyperbolic K V := (z.1, z.2.2, z.2.1)

omit [Field K] [AddCommGroup V] [Module K V] in
@[simp] theorem swap_swap (z : Hyperbolic K V) : swap (swap z) = z := rfl

@[simp] theorem q_swap (z : Hyperbolic K V) : q Q (swap z) = q Q z := by
  simp [q, swap, mul_comm]

@[simp] theorem transvection_zero (z : Hyperbolic K V) :
    transvection Q 0 z = z := by
  simp [transvection, Q.map_zero, Q.polar_zero_right]

theorem q_sub_smul (v u : V) (a : K) :
    Q (v - a • u) = Q v - a * polar Q v u + a * a * Q u := by
  rw [sub_eq_add_neg, QuadraticMap.map_add (Q : V → K) v (-(a • u))]
  simp only [Q.map_neg, Q.map_smul, smul_eq_mul, Q.polar_neg_right,
    Q.polar_smul_right]
  ring

@[simp] theorem q_transvection (u : V) (z : Hyperbolic K V) :
    q Q (transvection Q u z) = q Q z := by
  simp only [q, transvection, q_sub_smul]
  ring

theorem transvection_transvection (u w : V) (z : Hyperbolic K V) :
    transvection Q u (transvection Q w z) = transvection Q (u + w) z := by
  apply Prod.ext
  · simp only [transvection, smul_add]
    abel
  · apply Prod.ext
    · rfl
    · simp only [transvection, Q.polar_sub_left, Q.polar_smul_left,
        Q.polar_add_right, QuadraticMap.map_add (Q : V → K) u w, smul_eq_mul]
      rw [polar_comm (Q : V → K) w u]
      ring

@[simp] theorem transvection_neg_left (u : V) (z : Hyperbolic K V) :
    transvection Q (-u) (transvection Q u z) = z := by
  rw [transvection_transvection]
  simp

@[simp] theorem transvection_neg_right (u : V) (z : Hyperbolic K V) :
    transvection Q u (transvection Q (-u) z) = z := by
  rw [transvection_transvection]
  simp

/-- The map `Tᵤ` in Lemma 2.3, as an ambient linear equivalence. -/
def transvectionEquiv (u : V) : Hyperbolic K V ≃ₗ[K] Hyperbolic K V where
  toFun := transvection Q u
  invFun := transvection Q (-u)
  left_inv := transvection_neg_left Q u
  right_inv := transvection_neg_right Q u
  map_add' := by
    intro x y
    apply Prod.ext
    · change (x.1 + y.1) - (x.2.1 + y.2.1) • u = _
      simp only [add_smul, transvection, Prod.fst_add]
      abel
    · apply Prod.ext
      · rfl
      · change x.2.2 + y.2.2 + polar Q (x.1 + y.1) u -
          (x.2.1 + y.2.1) * Q u = _
        simp only [Q.polar_add_left, transvection, Prod.snd_add]
        ring
  map_smul' := by
    intro a x
    apply Prod.ext
    · simp [transvection, smul_sub, mul_smul]
    · apply Prod.ext
      · rfl
      · change a * x.2.2 + polar Q (a • x.1) u - (a * x.2.1) * Q u =
          a * (x.2.2 + polar Q x.1 u - x.2.1 * Q u)
        rw [Q.polar_smul_left]
        simp only [smul_eq_mul]
        ring

/-- The hyperbolic swap `S`. -/
def swapEquiv : Hyperbolic K V ≃ₗ[K] Hyperbolic K V where
  toFun := swap
  invFun := swap
  left_inv := swap_swap
  right_inv := swap_swap
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp] theorem conjugate_fixes_e (u : V) :
    swap (transvection Q u (swap (e : Hyperbolic K V))) = e := by
  simp [swap, transvection, e, Q.polar_zero_left]

@[simp] theorem conjugate_normalizes_partner (u : V) :
    swap (transvection Q u (swap (u, -Q u, 1))) = (f : Hyperbolic K V) := by
  simp only [swap, transvection, one_smul, sub_self, Q.polar_self, f]
  congr 2
  ring

/-- The crucial exact identity preceding the norm comparison in Lemma 2.4. -/
theorem descent_identity (z : Hyperbolic K V) (u : V)
    (hiso : q Q z = 0) (ha : z.2.1 ≠ 0) :
    (transvection Q u z).2.2 = -z.2.1 * Q (z.2.1⁻¹ • z.1 - u) := by
  have hv : z.1 - z.2.1 • u = z.2.1 • (z.2.1⁻¹ • z.1 - u) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ ha, one_smul]
  have ht : q Q (transvection Q u z) = 0 := (q_transvection Q u z).trans hiso
  change Q (z.1 - z.2.1 • u) + z.2.1 * (transvection Q u z).2.2 = 0 at ht
  rw [hv, Q.map_smul, smul_eq_mul] at ht
  have hh : z.2.1 * ((transvection Q u z).2.2 +
      z.2.1 * Q (z.2.1⁻¹ • z.1 - u)) = 0 := by
    linear_combination ht
  have hh' := (mul_eq_zero.mp hh).resolve_left ha
  linear_combination hh'

end Hyperbolic
end NormEuclidean
