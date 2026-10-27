import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.Index
import Mathlib.Data.Real.Basic
import NormEuclidean.ChapterX.ProductNorm

/-!
# Actual residue-field norm-one groups

The quadratic field case has q+1 elements and the split case has q-1.
These are actual norm kernels, not postulated local density constants.
Lifting these residue counts to integral orthogonal-group densities is
a separate step, not asserted here.
-/

noncomputable section

namespace NormEuclidean.FiniteNormTorus

variable (k E : Type*) [Field k] [Field E] [Algebra k E] [Finite E]

/-- The kernel of the actual field norm on units. -/
def fieldKernel : Subgroup Eˣ := (Units.map (Algebra.norm k (S := E))).ker

/-- A quadratic finite-field norm kernel has exactly q+1 elements. -/
theorem fieldKernel_card (h : Module.finrank k E = 2) :
    Nat.card (fieldKernel k E) = Nat.card k + 1 := by
  letI : Finite k := Finite.of_injective _ (algebraMap k E).injective
  let f := Units.map (Algebra.norm k (S := E))
  have hs : f.range = ⊤ := MonoidHom.range_eq_top.mpr (FiniteField.unitsMap_norm_surjective k E)
  have hc := f.ker.card_mul_index
  rw [Subgroup.index_ker, hs, Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup kˣ) ≃* kˣ).toEquiv,
    Nat.card_units, Nat.card_units, Module.natCard_eq_pow_finrank (K := k) (V := E), h] at hc
  have hq : 1 < Nat.card k := Finite.one_lt_card
  change Nat.card f.ker = Nat.card k + 1
  apply Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hq)
  rw [hc]
  have hsub := Nat.sub_add_cancel (Nat.le_of_lt hq)
  have hsq : 1 ≤ Nat.card k ^ 2 := by nlinarith
  have hsquare := Nat.sub_add_cancel hsq
  nlinarith

variable [Finite k]

/-- The split quadratic norm on the product of the two unit groups. -/
def splitNorm : kˣ × kˣ →* kˣ where
  toFun x := x.1 * x.2
  map_one' := mul_one _
  map_mul' x y := by simp [mul_comm, mul_left_comm]

omit [Finite k] in
/-- The split norm is the determinant norm of the actual product algebra. -/
theorem splitNorm_eq_algebraNorm (u : kˣ × kˣ) :
    (splitNorm k u : k) = Algebra.norm k ((u.1 : k), (u.2 : k)) := by
  simp [ProductNorm.norm_prod, splitNorm]

/-- Its kernel is parametrized by u mapped to (u,u inverse). -/
def splitKernelEquiv : kˣ ≃ (splitNorm k).ker where
  toFun u := ⟨(u, u⁻¹), by simp [MonoidHom.mem_ker, splitNorm]⟩
  invFun u := u.1.1
  left_inv u := rfl
  right_inv u := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have h : u.1.1 * u.1.2 = 1 := u.2
      apply mul_left_cancel (a := u.1.1)
      simpa using h.symm

omit [Finite k] in
/-- The actual split norm kernel has exactly q-1 elements. -/
theorem splitKernel_card : Nat.card (splitNorm k).ker = Nat.card k - 1 := by
  rw [← Nat.card_congr (splitKernelEquiv k), Nat.card_units]

/-- The normalized nonsplit residue count is the Euler factor 1+1/q. -/
theorem fieldKernel_ratio (h : Module.finrank k E = 2) :
    (Nat.card (fieldKernel k E) : ℝ) / Nat.card k = 1 + 1 / Nat.card k := by
  rw [fieldKernel_card k E h, Nat.cast_add, Nat.cast_one, add_div, div_self]
  exact_mod_cast (Nat.card_pos : 0 < Nat.card k).ne'

/-- The normalized split residue count is the Euler factor 1-1/q. -/
theorem splitKernel_ratio :
    (Nat.card (splitNorm k).ker : ℝ) / Nat.card k = 1 - 1 / Nat.card k := by
  rw [splitKernel_card, Nat.cast_sub (Nat.le_of_lt Finite.one_lt_card),
    Nat.cast_one, sub_div, div_self]
  exact_mod_cast (Nat.card_pos : 0 < Nat.card k).ne'

end NormEuclidean.FiniteNormTorus
