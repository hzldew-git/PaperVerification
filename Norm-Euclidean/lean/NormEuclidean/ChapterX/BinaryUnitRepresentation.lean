import NormEuclidean.ChapterX.FiniteResidueRepresentation
import NormEuclidean.ChapterX.CompletionHensel

/-!
# The binary unit representation input of O'Meara 92:1b

An odd finite residue field gives a nonzero coordinate for every nonzero
binary represented residue. Derivative-unit Hensel lifting in that coordinate
proves representation of every unit by a binary unit diagonal form.
No claim is made here for dyadic binary lattices.
-/

noncomputable section

namespace NormEuclidean.BinaryUnitRepresentation

open Polynomial IsDedekindDomain CompletedIntegralLattice

section Henselian

variable {S : Type*} [CommRing S] [IsLocalRing S]
  [HenselianRing S (IsLocalRing.maximalIdeal S)]

/-- Lift in a coordinate with nonzero residue; the other coordinate stays fixed. -/
theorem lift_first_coordinate (htwo : IsUnit (2 : S)) (a b : Sˣ) (t x y : S)
    (hx : IsUnit x)
    (hxy : IsLocalRing.residue S ((a : S) * x ^ 2 + (b : S) * y ^ 2 - t) = 0) :
    ∃ z : S, (a : S) * z ^ 2 + (b : S) * y ^ 2 = t := by
  let I := IsLocalRing.maximalIdeal S
  let r := IsLocalRing.residue S
  let f : S[X] := X ^ 2 + C (((a⁻¹ : Sˣ) : S) * ((b : S) * y ^ 2 - t))
  have hf : f.Monic := monic_X_pow_add_C _ (by decide)
  have heval (z : S) : (a : S) * f.eval z =
      (a : S) * z ^ 2 + (b : S) * y ^ 2 - t := by
    simp only [f, eval_add, eval_pow, eval_X, eval_C, mul_add, ← mul_assoc]
    simp only [Units.mul_inv, one_mul]
    ring
  have hfx : f.eval x ∈ I := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    have h : r (a : S) * r (f.eval x) = 0 := by rw [← map_mul, heval]; exact hxy
    exact (mul_eq_zero.mp h).resolve_left ((a.isUnit.map r).ne_zero)
  have hder : IsUnit (Ideal.Quotient.mk I (f.derivative.eval x)) := by
    have heq : f.derivative.eval x = 2 * x := by
      simp [f, pow_two]
      ring
    rw [heq]
    exact (htwo.mul hx).map _
  obtain ⟨z, hz, _⟩ := HenselianRing.is_henselian f hf x hfx hder
  refine ⟨z, sub_eq_zero.mp ?_⟩
  rw [← heval, hz, mul_zero]

/-- Binary unit diagonal forms represent every unit over a Henselian local
ring with finite odd residue field. Both coefficient and target units are literal. -/
theorem henselian_binary_represents_unit [Finite (IsLocalRing.ResidueField S)]
    (htwo : IsUnit (2 : S)) (a b t : Sˣ) :
    ∃ x y : S, (a : S) * x ^ 2 + (b : S) * y ^ 2 = (t : S) := by
  let k := IsLocalRing.ResidueField S
  let r : S →+* k := IsLocalRing.residue S
  have htwoR : (2 : k) ≠ 0 := by
    simpa only [map_ofNat] using (htwo.map r).ne_zero
  obtain ⟨x₀, y₀, hxy₀⟩ := FiniteResidueRepresentation.finite_field_binary_represents
    htwoR (r a) (r b) (r t) ((a.isUnit.map r).ne_zero) ((b.isUnit.map r).ne_zero)
  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective x₀
  obtain ⟨y, hy⟩ := IsLocalRing.residue_surjective y₀
  have hxy : r ((a : S) * x ^ 2 + (b : S) * y ^ 2 - (t : S)) = 0 := by
    simp only [map_sub, map_add, map_mul, map_pow]
    change r x = x₀ at hx
    change r y = y₀ at hy
    rw [hx, hy, hxy₀, sub_self]
  by_cases hx0 : x₀ = 0
  · have hy0 : y₀ ≠ 0 := by
      intro h
      have ht := (t.isUnit.map r).ne_zero
      exact ht (by simpa only [hx0, h, zero_pow (by decide : 2 ≠ 0),
        mul_zero, add_zero] using hxy₀.symm)
    have hyunit : IsUnit y := (IsLocalRing.residue_ne_zero_iff_isUnit y).mp (by rwa [hy])
    have hyx : r ((b : S) * y ^ 2 + (a : S) * x ^ 2 - (t : S)) = 0 := by
      rwa [add_comm] at hxy
    obtain ⟨z, hz⟩ := lift_first_coordinate htwo b a t y x hyunit hyx
    exact ⟨x, z, by rwa [add_comm] at hz⟩
  · have hxunit : IsUnit x := (IsLocalRing.residue_ne_zero_iff_isUnit x).mp (by rwa [hx])
    obtain ⟨z, hz⟩ := lift_first_coordinate htwo a b t x y hxunit hxy
    exact ⟨z, y, hz⟩

end Henselian

end NormEuclidean.BinaryUnitRepresentation
