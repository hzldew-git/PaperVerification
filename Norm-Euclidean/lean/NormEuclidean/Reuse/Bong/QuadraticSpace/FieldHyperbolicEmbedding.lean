/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.QuadraticSpace.HyperbolicPlane
import Bong.QuadraticSpace.Isometry
import Bong.Bong.Representation

/-!
# A hyperbolic plane inside an isotropic quadratic space

The standard construction works over any field of characteristic zero.
It supplies the actual isometric representation needed to split a
hyperbolic plane before applying Witt cancellation.
-/

namespace Bong.QuadraticSpace

universe u v

variable {K : Type u} [Field K] [CharZero K]
  {W : Type v} [AddCommGroup W] [Module K W]

/-- A nonzero isotropic vector in a nondegenerate quadratic space extends
to an isometric copy of the standard hyperbolic plane. -/
theorem represents_hyperbolicPlane_one_of_isotropic
    (r : QuadraticSpace K W) (x : W)
    (hx : x ≠ 0) (hxzero : r.quadratic x = 0) :
    r.Represents (hyperbolicPlane (1 : Kˣ)) := by
  classical
  have hnot : ¬ ∀ y : W, r.bilin x y = 0 := by
    intro horth
    exact hx (r.nondegenerate.1 x horth)
  push Not at hnot
  obtain ⟨z0, hxz0⟩ := hnot
  let z : W := (r.bilin x z0)⁻¹ • z0
  have hxz : r.bilin x z = 1 := by
    simp [z, hxz0]
  have hzx : r.bilin z x = 1 := by
    rw [r.isSymm.eq]
    exact hxz
  have hxx : r.bilin x x = 0 := hxzero
  let lambda : K := r.bilin z z / 2
  let y : W := z - lambda • x
  have hxy : r.bilin x y = 1 := by
    simp only [y, LinearMap.BilinForm.sub_right,
      LinearMap.BilinForm.smul_right, hxz, hxx, mul_zero, sub_zero]
  have hyx : r.bilin y x = 1 := by
    rw [r.isSymm.eq]
    exact hxy
  have hyy : r.bilin y y = 0 := by
    simp only [y, LinearMap.BilinForm.sub_left,
      LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right, hxx, hxz, hzx, mul_zero,
      sub_zero, lambda]
    field_simp
    ring
  let f : (Fin 2 → K) →ₗ[K] W :=
    { toFun := fun v ↦ v 0 • x + v 1 • y
      map_add' := by
        intro v w
        simp only [Pi.add_apply, add_smul]
        abel
      map_smul' := by
        intro a v
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
          smul_add, smul_smul] }
  have hfInjective : Function.Injective f := by
    intro v w hvw
    have hone := congrArg (fun t ↦ r.bilin x t) hvw
    have hzero := congrArg (fun t ↦ r.bilin y t) hvw
    have hvone : v 1 = w 1 := by
      simpa only [f, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right,
        hxx, hxy, mul_zero, mul_one, zero_add] using hone
    have hvzero : v 0 = w 0 := by
      simpa only [f, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right,
        hyx, hyy, mul_one, mul_zero, add_zero] using hzero
    funext j
    fin_cases j
    · exact hvzero
    · exact hvone
  refine ⟨{
    toLinearMap := f
    injective := hfInjective
    map_bilin := ?_ }⟩
  intro v w
  change r.bilin (f v) (f w) = _
  rw [hyperbolicPlane_bilin_apply]
  simp only [f, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
    hxx, hxy, hyx, hyy, mul_zero, mul_one, one_mul,
    zero_add, add_zero, Units.val_one]
  ring

end Bong.QuadraticSpace
