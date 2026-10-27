import NormEuclidean.LocalNormCayley
import NormEuclidean.FiniteNormTorus
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.Tactic.FieldSimp

/-!
# Exact finite local norm-one densities

The finite-level density is the actual norm-one count divided by the
cardinality of the coefficient ring. The reduction formula is exact,
not an asymptotic lifting assumption. Split, nonsplit and ramified
residue parameters are distinguished. Orthogonal self-density requires
a further comparison, and no global mass identity is asserted here.
-/

noncomputable section

namespace NormEuclidean.LocalNormDensity

open LocalNormCayley
open scoped QuadraticAlgebra

variable {R : Type*} [CommRing R]

/-- Coordinate solutions with their actual quadratic equation. -/
def coordinateEquiv (d : R) :
    NormOne R d ≃ {p : R × R // p.1 ^ 2 - d * p.2 ^ 2 = 1} where
  toFun z := ⟨(z.val.re, z.val.im), norm_eq d z⟩
  invFun p := mk d p.val.1 p.val.2 p.property
  left_inv _ := rfl
  right_inv _ := rfl

/-- The coordinate norm equals the determinant algebra norm over any base ring. -/
theorem determinant_norm (d : R) (z : QuadraticAlgebra R d 0) :
    Algebra.norm R z = z.norm := by
  exact QuadraticAlgebra.det_toLinearMap_eq_norm z

/-- The coordinate group is the kernel of the actual determinant norm on units. -/
def determinantKernelEquiv (d : R) :
    NormOne R d ≃ (Units.map (Algebra.norm R (S := QuadraticAlgebra R d 0))).ker where
  toFun z := ⟨Unitary.toUnits z, by
    apply MonoidHom.mem_ker.mpr
    apply Units.ext
    exact (determinant_norm d z.val).trans (QuadraticAlgebra.norm_eq_one z.property)⟩
  invFun z := ⟨z.val.val, QuadraticAlgebra.mem_unitary (by
    have h := congrArg Units.val (MonoidHom.mem_ker.mp z.property)
    exact (determinant_norm d z.val.val).symm.trans h)⟩
  left_inv _ := rfl
  right_inv _ := by apply Subtype.ext; apply Units.ext; rfl

/-- The actual finite congruence-level norm-one density. -/
def density (R : Type*) [CommRing R] (d : R) : ℝ :=
  (Nat.card (NormOne R d) : ℝ) / Nat.card R

/-- Dividing the exact multiplicative and additive fiber counts cancels the
kernel ideal. This holds for any finite local level, with no Hensel input. -/
theorem density_reduction [Finite R] {k : Type*} [Field k]
    (f : R →+* k) [IsLocalHom f] (hf : Function.Surjective f)
    (h2 : IsUnit (2 : R)) (d : R) : density R d = density k (f d) := by
  letI : Finite k := Finite.of_surjective f hf
  have hm : (Nat.card (RingHom.ker f) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card (RingHom.ker f)).ne'
  unfold density
  rw [card_normOne f d hf h2, card_ring f hf, Nat.cast_mul, Nat.cast_mul]
  exact mul_div_mul_left _ _ hm

variable {k : Type*} [Field k]

private def splitUnit (s : k) (z : NormOne k (s ^ 2)) : kˣ where
  val := z.val.re + s * z.val.im
  inv := z.val.re - s * z.val.im
  val_inv := by linear_combination norm_eq (s ^ 2) z
  inv_val := by linear_combination norm_eq (s ^ 2) z

/-- The split norm-one group is exactly the unit group, using both inverse coordinates. -/
def splitEquiv (s : k) (hs : s ≠ 0) (h2 : (2 : k) ≠ 0) :
    NormOne k (s ^ 2) ≃ kˣ :=
  Equiv.ofBijective (splitUnit s) (by
    constructor
    · intro z w h
      have ha := congrArg Units.val h
      have hb := congrArg (fun u : kˣ ↦ (u⁻¹ : kˣ).val) h
      change z.val.re + s * z.val.im = w.val.re + s * w.val.im at ha
      change z.val.re - s * z.val.im = w.val.re - s * w.val.im at hb
      apply Subtype.ext
      apply QuadraticAlgebra.ext
      · apply mul_left_cancel₀ h2
        linear_combination ha + hb
      · apply mul_left_cancel₀ (mul_ne_zero h2 hs)
        linear_combination ha - hb
    · intro u
      let a := ((u : k) + (u⁻¹ : kˣ)) / 2
      let b := ((u : k) - (u⁻¹ : kˣ)) / (2 * s)
      have hn : a ^ 2 - s ^ 2 * b ^ 2 = 1 := by
        dsimp [a, b]
        field_simp
        linear_combination 4 * u.val_inv
      refine ⟨mk (s ^ 2) a b hn, ?_⟩
      apply Units.ext
      change a + s * b = (u : k)
      dsimp [a, b]
      field_simp
      ring)

/-- The split residue count is q-1. -/
theorem split_card (s : k) (hs : s ≠ 0) (h2 : (2 : k) ≠ 0) :
    Nat.card (NormOne k (s ^ 2)) = Nat.card k - 1 := by
  rw [Nat.card_congr (splitEquiv s hs h2), Nat.card_units]

/-- The nonsplit residue count uses the actual quadratic field norm kernel. -/
theorem nonsplit_card [Finite k] (d : k) (hd : ¬ IsSquare d) :
    Nat.card (NormOne k d) = Nat.card k + 1 := by
  letI : Fact (∀ r : k, r ^ 2 ≠ d + 0 * r) := ⟨by
    intro r hr
    apply hd
    exact ⟨r, by simpa [pow_two] using hr.symm⟩⟩
  letI : Field (QuadraticAlgebra k d 0) := inferInstance
  letI : Finite (QuadraticAlgebra k d 0) :=
    Finite.of_equiv (k × k) (QuadraticAlgebra.equivProd d 0).symm
  rw [Nat.card_congr (determinantKernelEquiv d)]
  exact FiniteNormTorus.fieldKernel_card k (QuadraticAlgebra k d 0)
    (QuadraticAlgebra.finrank_eq_two d 0)

/-- At zero residue parameter, both signs occur and the imaginary coordinate is free. -/
def ramifiedEquiv (h2 : (2 : k) ≠ 0) : (Bool × k) ≃ NormOne k 0 :=
  Equiv.ofBijective (fun p ↦ mk 0 (if p.1 then 1 else -1) p.2 (by
    cases p.1 <;> simp)) (by
    have hn : (1 : k) ≠ -1 := by intro h; apply h2; linear_combination h
    constructor
    · rintro ⟨b, x⟩ ⟨c, y⟩ h
      have ha := congrArg (fun z : NormOne k 0 ↦ z.val.re) h
      have hb := congrArg (fun z : NormOne k 0 ↦ z.val.im) h
      cases b <;> cases c <;> simp_all [mk]
    · intro z
      have hz : z.val.re ^ 2 = 1 := by simpa using norm_eq 0 z
      rcases sq_eq_one_iff.mp hz with h | h
      · exact ⟨(true, z.val.im), Subtype.ext (QuadraticAlgebra.ext h.symm rfl)⟩
      · exact ⟨(false, z.val.im), Subtype.ext (QuadraticAlgebra.ext h.symm rfl)⟩)

/-- The ramified residue norm-one count is 2q, not q. -/
theorem ramified_card (h2 : (2 : k) ≠ 0) :
    Nat.card (NormOne k 0) = 2 * Nat.card k := by
  rw [← Nat.card_congr (ramifiedEquiv h2), Nat.card_prod, Nat.card_eq_fintype_card]
  rfl

/-- The nonzero square parameter gives the split Euler factor. -/
theorem split_density [Finite k] (s : k) (hs : s ≠ 0) (h2 : (2 : k) ≠ 0) :
    density k (s ^ 2) = 1 - 1 / Nat.card k := by
  unfold density
  rw [split_card s hs h2, Nat.cast_sub (Nat.le_of_lt Finite.one_lt_card),
    Nat.cast_one, sub_div, div_self]
  exact_mod_cast (Nat.card_pos : 0 < Nat.card k).ne'

/-- The nonsquare parameter gives the unramified nonsplit Euler factor. -/
theorem nonsplit_density [Finite k] (d : k) (hd : ¬ IsSquare d) :
    density k d = 1 + 1 / Nat.card k := by
  unfold density
  rw [nonsplit_card d hd, Nat.cast_add, Nat.cast_one, add_div, div_self]
  exact_mod_cast (Nat.card_pos : 0 < Nat.card k).ne'

/-- For zero residue parameter the norm-group density is exactly two.
This does not assert the self-density of a degenerate integral Gram matrix. -/
theorem ramified_density [Finite k] (h2 : (2 : k) ≠ 0) : density k 0 = 2 := by
  unfold density
  rw [ramified_card h2, Nat.cast_mul, Nat.cast_ofNat, mul_div_cancel_right₀]
  exact_mod_cast (Nat.card_pos : 0 < Nat.card k).ne'

end NormEuclidean.LocalNormDensity
