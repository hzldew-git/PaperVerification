import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.LinearCombination

/-!
# Cayley coordinates for the actual quadratic norm-one group

The parameter is arbitrary. Only two is required to be a unit. Reduction
is taken along an actual surjective local homomorphism to a field. The
kernel is parametrized by the kernel ideal, including ramified parameters.
This is a norm-group statement; it does not identify a lattice mass.
-/

noncomputable section

namespace NormEuclidean.LocalNormCayley

open scoped Ring QuadraticAlgebra

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The actual norm-one group of `R[X]/(X²-d)`. -/
abbrev NormOne (R : Type*) [CommRing R] (d : R) :=
  unitary (QuadraticAlgebra R d 0)

/-- The coordinate norm equation for a norm-one element. -/
theorem norm_eq (d : R) (z : NormOne R d) :
    z.val.re ^ 2 - d * z.val.im ^ 2 = 1 := by
  simpa [QuadraticAlgebra.norm_def, pow_two, mul_assoc] using
    QuadraticAlgebra.norm_eq_one z.property

/-- Construct a norm-one element from its literal quadratic equation. -/
def mk (d a b : R) (h : a ^ 2 - d * b ^ 2 = 1) : NormOne R d :=
  ⟨⟨a, b⟩, QuadraticAlgebra.mem_unitary (by
    simpa [QuadraticAlgebra.norm_def, pow_two, mul_assoc] using h)⟩

/-- Coefficient reduction induces the actual norm-one group homomorphism. -/
def map (f : R →+* S) (d : R) : NormOne R d →* NormOne S (f d) where
  toFun z := mk (f d) (f z.val.re) (f z.val.im) (by
    simpa only [map_sub, map_pow, map_mul, map_one] using congrArg f (norm_eq d z))
  map_one' := by
    apply Subtype.ext
    apply QuadraticAlgebra.ext
    · exact f.map_one
    · exact f.map_zero
  map_mul' z w := by
    apply Subtype.ext
    ext <;> simp [mk, map_add, map_mul]

/-- The Cayley denominator and its inverse give an exact norm-one point. -/
def cayley (d t : R) (h : IsUnit (1 - d * t ^ 2)) : NormOne R d :=
  mk d ((1 + d * t ^ 2) * (1 - d * t ^ 2)⁻¹ʳ)
    (2 * t * (1 - d * t ^ 2)⁻¹ʳ) (by
      calc
        _ = ((1 - d * t ^ 2) * (1 - d * t ^ 2)⁻¹ʳ) ^ 2 := by ring
        _ = 1 := by rw [Ring.mul_inverse_cancel _ h]; ring)

private theorem denominator_eq (d : R) (z : NormOne R d)
    (hz : IsUnit (z.val.re + 1)) :
    1 - d * (z.val.im * (z.val.re + 1)⁻¹ʳ) ^ 2 =
      2 * (z.val.re + 1)⁻¹ʳ := by
  have hn := norm_eq d z
  have hi := Ring.mul_inverse_cancel _ hz
  linear_combination (z.val.re + 1)⁻¹ʳ ^ 2 * hn -
    (1 + (z.val.re - 1) * (z.val.re + 1)⁻¹ʳ) * hi

/-- The inverse Cayley coordinate has an invertible denominator. -/
theorem inverse_denominator_unit (d : R) (h2 : IsUnit (2 : R))
    (z : NormOne R d) (hz : IsUnit (z.val.re + 1)) :
    IsUnit (1 - d * (z.val.im * (z.val.re + 1)⁻¹ʳ) ^ 2) := by
  rw [denominator_eq d z hz]
  exact h2.mul hz.ringInverse

/-- Cayley reconstruction on the chart where the real coordinate plus one is a unit. -/
theorem cayley_inverse (d : R) (h2 : IsUnit (2 : R))
    (z : NormOne R d) (hz : IsUnit (z.val.re + 1)) :
    cayley d (z.val.im * (z.val.re + 1)⁻¹ʳ)
      (inverse_denominator_unit d h2 z hz) = z := by
  let v := (z.val.re + 1)⁻¹ʳ
  let t := z.val.im * v
  let D := 1 - d * t ^ 2
  have hi : (z.val.re + 1) * v = 1 := Ring.mul_inverse_cancel _ hz
  have hn := norm_eq d z
  have hD : IsUnit D := inverse_denominator_unit d h2 z hz
  have ha : 1 + d * t ^ 2 = z.val.re * D := by
    dsimp [D, t]
    linear_combination -(z.val.re + 1) * v ^ 2 * hn +
      (z.val.re - 1) * ((z.val.re + 1) * v + 1) * hi
  have hb : 2 * t = z.val.im * D := by
    dsimp [D, t]
    linear_combination -z.val.im * v ^ 2 * hn +
      z.val.im * (1 + (z.val.re - 1) * v) * hi
  apply Subtype.ext
  apply QuadraticAlgebra.ext
  · change (1 + d * t ^ 2) * D⁻¹ʳ = z.val.re
    rw [ha, Ring.mul_inverse_cancel_right _ _ hD]
  · change 2 * t * D⁻¹ʳ = z.val.im
    rw [hb, Ring.mul_inverse_cancel_right _ _ hD]

private theorem map_inverse (f : R →+* S) (x : R) (h : IsUnit x) :
    f x⁻¹ʳ = (f x)⁻¹ʳ := by
  simpa using (Ring.eq_mul_inverse_iff_mul_eq (f x⁻¹ʳ) 1 (f x) (h.map f)).mpr
    (by simp only [← map_mul, Ring.inverse_mul_cancel _ h, map_one])

/-- Cayley coordinates commute with coefficient homomorphisms. -/
theorem map_cayley (f : R →+* S) (d t : R) (h : IsUnit (1 - d * t ^ 2)) :
    map f d (cayley d t h) =
      cayley (f d) (f t) (by simpa using h.map f) := by
  apply Subtype.ext
  ext <;> simp [map, mk, cayley, map_inverse f _ h, map_ofNat]

private theorem cayley_chart (d t : R) (h2 : IsUnit (2 : R))
    (h : IsUnit (1 - d * t ^ 2)) :
    IsUnit ((cayley d t h).val.re + 1) := by
  have hi := Ring.mul_inverse_cancel _ h
  have he : (cayley d t h).val.re + 1 = 2 * (1 - d * t ^ 2)⁻¹ʳ := by
    change (1 + d * t ^ 2) * (1 - d * t ^ 2)⁻¹ʳ + 1 = _
    linear_combination -hi
  rw [he]
  exact h2.mul h.ringInverse

/-- The inverse coordinate recovers the Cayley parameter. -/
theorem cayley_coordinate (d t : R) (h2 : IsUnit (2 : R))
    (h : IsUnit (1 - d * t ^ 2)) :
    (cayley d t h).val.im * ((cayley d t h).val.re + 1)⁻¹ʳ = t := by
  have he : (cayley d t h).val.im = t * ((cayley d t h).val.re + 1) := by
    change 2 * t * (1 - d * t ^ 2)⁻¹ʳ =
      t * ((1 + d * t ^ 2) * (1 - d * t ^ 2)⁻¹ʳ + 1)
    linear_combination t * Ring.mul_inverse_cancel _ h
  rw [he, Ring.mul_inverse_cancel_right _ _ (cayley_chart d t h2 h)]

section Reduction

variable {k : Type*} [Field k] (f : R →+* k) [IsLocalHom f] (d : R)

private theorem unit_of_nonzero (x : R) (hx : f x ≠ 0) : IsUnit x :=
  isUnit_of_map_unit f x (isUnit_iff_ne_zero.mpr hx)

omit [IsLocalHom f] in
private theorem kernel_re (z : (map f d).ker) : f z.val.val.re = 1 := by
  exact congrArg (fun w : NormOne k (f d) ↦ w.val.re) (MonoidHom.mem_ker.mp z.property)

omit [IsLocalHom f] in
private theorem kernel_im (z : (map f d).ker) : f z.val.val.im = 0 := by
  exact congrArg (fun w : NormOne k (f d) ↦ w.val.im) (MonoidHom.mem_ker.mp z.property)

private theorem kernel_chart (h2 : IsUnit (2 : R)) (z : (map f d).ker) :
    IsUnit (z.val.val.re + 1) := by
  apply unit_of_nonzero f
  simpa [kernel_re f d z, map_ofNat, one_add_one_eq_two] using (h2.map f).ne_zero

private theorem parameter_unit (t : RingHom.ker f) : IsUnit (1 - d * t.val ^ 2) := by
  apply unit_of_nonzero f
  have ht : f t.val = 0 := t.property
  simp [ht]

/-- Exact parametrization of the reduction kernel by the kernel ideal. -/
def kernelEquiv (h2 : IsUnit (2 : R)) : (map f d).ker ≃ RingHom.ker f where
  toFun z := ⟨z.val.val.im * (z.val.val.re + 1)⁻¹ʳ, by
    change f (z.val.val.im * (z.val.val.re + 1)⁻¹ʳ) = 0
    rw [map_mul, kernel_im f d z, zero_mul]⟩
  invFun t := ⟨cayley d t.val (parameter_unit f d t), by
    apply MonoidHom.mem_ker.mpr
    rw [map_cayley]
    have ht : f t.val = 0 := t.property
    apply Subtype.ext
    ext <;> simp [cayley, mk, ht]⟩
  left_inv z := by
    apply Subtype.ext
    exact cayley_inverse d h2 z.val (kernel_chart f d h2 z)
  right_inv t := by
    apply Subtype.ext
    exact cayley_coordinate d t.val h2 (parameter_unit f d t)

/-- Every residue norm-one point lifts when two is a unit. This includes
the ramified parameter, where a residue point with real part minus one
need not have zero imaginary part. Negation moves it to the Cayley chart. -/
theorem map_surjective (hf : Function.Surjective f) (h2 : IsUnit (2 : R)) :
    Function.Surjective (map f d) := by
  have h2k : IsUnit (2 : k) := by simpa only [map_ofNat] using h2.map f
  have lift_chart (z : NormOne k (f d)) (hz : IsUnit (z.val.re + 1)) :
      ∃ w, map f d w = z := by
    obtain ⟨t, ht⟩ := hf (z.val.im * (z.val.re + 1)⁻¹ʳ)
    have hD : IsUnit (1 - d * t ^ 2) := by
      apply unit_of_nonzero f
      simpa [ht] using (inverse_denominator_unit (f d) h2k z hz).ne_zero
    refine ⟨cayley d t hD, ?_⟩
    rw [map_cayley]
    simpa only [ht] using cayley_inverse (f d) h2k z hz
  intro z
  by_cases hz : IsUnit (z.val.re + 1)
  · exact lift_chart z hz
  · have hz0 : z.val.re + 1 = 0 := by simpa only [isUnit_iff_ne_zero, not_not] using hz
    let negZ := mk (f d) (-z.val.re) (-z.val.im) (by simpa using norm_eq (f d) z)
    have hnz : IsUnit (negZ.val.re + 1) := by
      have he : negZ.val.re + 1 = 2 := by dsimp [negZ, mk]; linear_combination -hz0
      rw [he]
      exact h2k
    obtain ⟨w, hw⟩ := lift_chart negZ hnz
    refine ⟨mk d (-w.val.re) (-w.val.im) (by simpa using norm_eq d w), ?_⟩
    have ha := congrArg (fun u : NormOne k (f d) ↦ u.val.re) hw
    have hb := congrArg (fun u : NormOne k (f d) ↦ u.val.im) hw
    apply Subtype.ext
    apply QuadraticAlgebra.ext
    · change f (-w.val.re) = z.val.re
      change f w.val.re = -z.val.re at ha
      simp [ha]
    · change f (-w.val.im) = z.val.im
      change f w.val.im = -z.val.im at hb
      simp [hb]

/-- The exact norm-one count at a finite local level. -/
theorem card_normOne (hf : Function.Surjective f) (h2 : IsUnit (2 : R)) :
    Nat.card (NormOne R d) = Nat.card (RingHom.ker f) * Nat.card (NormOne k (f d)) := by
  have hc := (map f d).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (map_surjective f d hf h2),
    Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup (NormOne k (f d))) ≃*
      NormOne k (f d)).toEquiv, Nat.card_congr (kernelEquiv f d h2)] at hc
  exact hc.symm

omit [IsLocalHom f] in
/-- The same kernel ideal counts additive residue fibers. -/
theorem card_ring (hf : Function.Surjective f) :
    Nat.card R = Nat.card (RingHom.ker f) * Nat.card k := by
  have hc := f.toAddMonoidHom.ker.card_mul_index
  rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hf,
    Nat.card_congr (AddSubgroup.topEquiv : (⊤ : AddSubgroup k) ≃+ k).toEquiv] at hc
  exact hc.symm

end Reduction

end NormEuclidean.LocalNormCayley
