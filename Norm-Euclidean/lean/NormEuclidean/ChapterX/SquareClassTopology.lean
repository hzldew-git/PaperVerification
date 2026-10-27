/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Openness of nonzero square classes

The proof is extracted from HeADC's `He2025SubspaceDescentTopology`,
lines 39-91, with the unnecessary quadratic-space imports removed.
The derivative of multiplication by a nonzero scalar times a square
is nonzero away from zero, so the inverse-function theorem applies.
-/

namespace NormEuclidean.SquareClassTopology

open scoped Topology

/-- Every nonzero square class is open in a complete normed field of characteristic zero. -/
theorem isOpen_squareClass {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [CharZero K] (A : Kˣ) : IsOpen {z : K | ∃ c : Kˣ, z = A.val * c.val ^ 2} := by
  let f : K → K := fun x ↦ A.val * x ^ 2
  let nonzero : Set K := {0}ᶜ
  have hopen : IsOpen nonzero := isOpen_compl_singleton
  have himage : IsOpen (f '' nonzero) := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxn : nonzero ∈ 𝓝 x := hopen.mem_nhds hx
    have hx0 : x ≠ 0 := hx
    have hd : A.val * ((2 : K) * x ^ (2 - 1)) ≠ 0 :=
      mul_ne_zero A.ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hx0))
    have hm : Filter.map f (𝓝 x) = 𝓝 (f x) := by
      simpa only [f] using ((hasStrictDerivAt_pow 2 x).const_mul A.val).map_nhds_eq hd
    rw [← hm]
    change f ⁻¹' (f '' nonzero) ∈ 𝓝 x
    exact Filter.mem_of_superset hxn (Set.subset_preimage_image f nonzero)
  have he : {z : K | ∃ c : Kˣ, z = A.val * c.val ^ 2} = f '' nonzero := by
    ext z
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c.val, c.ne_zero, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Units.mk0 x hx, rfl⟩
  rw [he]
  exact himage

end NormEuclidean.SquareClassTopology
