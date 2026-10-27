import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic.LinearCombination

/-!
# Integral ternary representation from finite residue fields

Finite-field quadratic images supply a binary representation of every
residue value. A simple root in the third coordinate lifts that representation
over an actual Henselian local ring with finite residue field of odd characteristic.
-/

noncomputable section

namespace NormEuclidean.FiniteResidueRepresentation

open Polynomial

/-- Every binary diagonal form with nonzero coefficients over an odd finite
field represents every field element. -/
theorem finite_field_binary_represents {F : Type*} [Field F] [Finite F]
    (htwo : (2 : F) ≠ 0) (a b t : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ x y : F, a * x ^ 2 + b * y ^ 2 = t := by
  classical
  letI := Fintype.ofFinite F
  have hchar : ringChar F ≠ 2 := by
    intro h
    apply htwo
    exact (ringChar.spec F 2).mpr (by rw [h])
  let f : F[X] := C a * X ^ 2 + C 0 * X + C 0
  let g : F[X] := C b * X ^ 2 + C 0 * X + C (-t)
  obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic
    (f := f) (g := g) (degree_quadratic ha) (degree_quadratic hb)
    (FiniteField.odd_card_of_char_ne_two hchar)
  refine ⟨x, y, ?_⟩
  have h : a * x ^ 2 + (b * y ^ 2 - t) = 0 := by
    simpa [f, g, sub_eq_add_neg] using hxy
  linear_combination h

/-- A ternary unit diagonal form over a Henselian local ring with finite odd
residue field represents every integral element. No root-lifting law is supplied. -/
theorem henselian_ternary_represents {S : Type*} [CommRing S] [IsLocalRing S]
    [HenselianRing S (IsLocalRing.maximalIdeal S)]
    [Finite (IsLocalRing.ResidueField S)] (htwo : IsUnit (2 : S))
    (a b c : Sˣ) (t : S) :
    ∃ x y z : S, (a : S) * x ^ 2 + (b : S) * y ^ 2 + (c : S) * z ^ 2 = t := by
  let k := IsLocalRing.ResidueField S
  let r : S →+* k := IsLocalRing.residue S
  have htwoR : (2 : k) ≠ 0 := by
    simpa only [map_ofNat] using (htwo.map r).ne_zero
  obtain ⟨x₀, y₀, hxy₀⟩ := finite_field_binary_represents htwoR
    (r (a : S)) (r (b : S)) (r (t - (c : S)))
    ((a.isUnit.map r).ne_zero) ((b.isUnit.map r).ne_zero)
  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective x₀
  obtain ⟨y, hy⟩ := IsLocalRing.residue_surjective y₀
  have hxy : r ((a : S) * x ^ 2 + (b : S) * y ^ 2 + (c : S) - t) = 0 := by
    simp only [map_sub, map_add, map_mul, map_pow]
    change r x = x₀ at hx
    change r y = y₀ at hy
    rw [hx, hy]
    have h := hxy₀
    rw [map_sub] at h
    linear_combination h
  let f : S[X] := X ^ 2 + C (((c⁻¹ : Sˣ) : S) *
    ((a : S) * x ^ 2 + (b : S) * y ^ 2 - t))
  have hfmonic : f.Monic := monic_X_pow_add_C _ (by decide)
  have heval (z : S) : (c : S) * f.eval z =
      (a : S) * x ^ 2 + (b : S) * y ^ 2 + (c : S) * z ^ 2 - t := by
    simp only [f, eval_add, eval_pow, eval_X, eval_C, mul_add, ← mul_assoc]
    simp only [Units.mul_inv, one_mul]
    ring
  have hfzero : f.eval 1 ∈ IsLocalRing.maximalIdeal S := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    have h : r (c : S) * r (f.eval 1) = 0 := by
      rw [← map_mul, heval]
      simpa only [one_pow, mul_one] using hxy
    exact (mul_eq_zero.mp h).resolve_left ((c.isUnit.map r).ne_zero)
  have hfderivative : IsUnit
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal S) (f.derivative.eval 1)) := by
    have heq : f.derivative.eval 1 = (2 : S) := by
      dsimp only [f]
      rw [derivative_add, derivative_C]
      norm_num
    rw [heq]
    exact htwo.map _
  obtain ⟨z, hz, _⟩ := HenselianRing.is_henselian f hfmonic 1 hfzero hfderivative
  refine ⟨x, y, z, ?_⟩
  have h : (a : S) * x ^ 2 + (b : S) * y ^ 2 + (c : S) * z ^ 2 - t = 0 := by
    rw [← heval, hz, mul_zero]
  exact sub_eq_zero.mp h

end NormEuclidean.FiniteResidueRepresentation
