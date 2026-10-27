import NormEuclidean.GramScaling
import NormEuclidean.RamifiedBinaryDensity

/-!
# Split norm-one counts without division by two

The change of variables x=a+b retains its nontrivial lifting fibers.
For a finite local ring where two is a nonunit, the split norm-one density
is the actual number of square roots of one in the quotient by two.
This is an integral order calculation, not a maximal-order assertion.
-/

noncomputable section

namespace NormEuclidean.DyadicSplitNormDensity

open LocalNormCayley
open scoped QuadraticAlgebra

variable (R : Type*) [CommRing R]

/-- The actual quotient by two, including at nonreduced congruence levels. -/
abbrev TwoQuotient := R ⧸ Ideal.span ({(2 : R)} : Set R)

/-- Literal square roots of one, with no reducedness assumption. -/
def Roots (S : Type*) [CommRing S] := {x : S // x ^ 2 = 1}

/-- All scalar lifts of those roots through reduction modulo two. -/
def RootLifts := {x : R // (Ideal.Quotient.mk (Ideal.span ({(2 : R)} : Set R)) x) ^ 2 = 1}

private theorem rootLift_mem (z : NormOne R 1) :
    (Ideal.Quotient.mk (Ideal.span ({(2 : R)} : Set R)) (z.val.re + z.val.im)) ^ 2 = 1 := by
  have he : (z.val.re + z.val.im) ^ 2 - 1 = 2 * (z.val.im * (z.val.re + z.val.im)) := by
    linear_combination norm_eq 1 z
  have hm : (z.val.re + z.val.im) ^ 2 - 1 ∈ Ideal.span ({(2 : R)} : Set R) := by
    rw [he]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self (2 : R))
  exact sub_eq_zero.mp (by
    simpa only [map_sub, map_pow, map_one] using Ideal.Quotient.eq_zero_iff_mem.mpr hm)

/-- Exact split norm coordinates; no inverse of two is used. -/
def normFiberEquiv : NormOne R 1 ≃
    Σ x : RootLifts R, {b : R // x.val ^ 2 - 2 * x.val * b = 1} where
  toFun z := ⟨⟨z.val.re + z.val.im, rootLift_mem R z⟩,
    ⟨z.val.im, by linear_combination norm_eq 1 z⟩⟩
  invFun p := mk 1 (p.1.val - p.2.val) p.2.val (by linear_combination p.2.property)
  left_inv z := by
    apply Subtype.ext
    apply QuadraticAlgebra.ext
    · exact add_sub_cancel_right _ _
    · rfl
  right_inv p := by
    apply Sigma.subtype_ext
    · exact Subtype.ext (sub_add_cancel p.1.val p.2.val)
    · rfl

variable [IsLocalRing R]

/-- A root lift is an actual unit because the ideal of two lies in the maximal ideal. -/
theorem rootLift_isUnit (h2 : ¬ IsUnit (2 : R)) (x : RootLifts R) : IsUnit x.val := by
  let I := Ideal.span ({(2 : R)} : Set R)
  have hI : I ≠ ⊤ := by simpa [I, Ideal.span_singleton_eq_top] using h2
  letI : Nontrivial (TwoQuotient R) := Ideal.Quotient.nontrivial_iff.mpr hI
  let f := Ideal.Quotient.mk I
  letI : IsLocalHom f := IsLocalHom.of_surjective f Ideal.Quotient.mk_surjective
  apply isUnit_of_map_unit f
  have hx : (f x.val) ^ 2 = 1 := x.property
  have hm : f x.val * f x.val = 1 := by simpa only [pow_two] using hx
  exact ⟨⟨f x.val, f x.val, hm, hm⟩, rfl⟩

/-- Every admissible scalar lift has an actual split norm preimage. -/
theorem exists_imaginary (h2 : ¬ IsUnit (2 : R)) (x : RootLifts R) :
    ∃ b : R, x.val ^ 2 - 2 * x.val * b = 1 := by
  let u := (rootLift_isUnit R h2 x).unit
  have hu : (u : R) = x.val := (rootLift_isUnit R h2 x).unit_spec
  have hm : x.val ^ 2 - 1 ∈ Ideal.span ({(2 : R)} : Set R) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_pow, map_one, x.property, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hm
  refine ⟨(u⁻¹ : Rˣ).val * c, ?_⟩
  have hi : x.val * (u⁻¹ : Rˣ).val = 1 := by rw [← hu]; exact u.val_inv
  linear_combination hc - 2 * c * hi

/-- The imaginary-coordinate fiber is the actual annihilator of two. -/
def imaginaryFiberEquiv (h2 : ¬ IsUnit (2 : R)) (x : RootLifts R) :
    {b : R // x.val ^ 2 - 2 * x.val * b = 1} ≃
      BinaryCongruenceDensity.annihilator (2 : R) := by
  let b₀ := Classical.choose (exists_imaginary R h2 x)
  have hb₀ := Classical.choose_spec (exists_imaginary R h2 x)
  refine
    { toFun := fun b ↦ ⟨b.val - b₀, ?_⟩
      invFun := fun b ↦ ⟨b₀ + b.val, ?_⟩
      left_inv := fun b ↦ by apply Subtype.ext; dsimp; abel
      right_inv := fun b ↦ Subtype.ext (add_sub_cancel_left b₀ b.val) }
  · apply (BinaryCongruenceDensity.mem_annihilator 2 _).mpr
    apply (rootLift_isUnit R h2 x).mul_left_cancel (b := 2 * (b.val - b₀)) (c := 0)
    linear_combination hb₀ - b.property
  · have hb := (BinaryCongruenceDensity.mem_annihilator 2 b.val).mp b.property
    linear_combination hb₀ - x.val * hb

/-- The full split norm-one set retains both the scalar lifts and annihilator fibers. -/
def splitEquiv (h2 : ¬ IsUnit (2 : R)) :
    NormOne R 1 ≃ RootLifts R × BinaryCongruenceDensity.annihilator (2 : R) :=
  (normFiberEquiv R).trans ((Equiv.sigmaCongrRight (imaginaryFiberEquiv R h2)).trans
    (Equiv.sigmaEquivProd _ _))

/-- Root lifts are the additive reduction kernel times roots in the actual quotient. -/
def rootLiftsEquiv : RootLifts R ≃ Roots (TwoQuotient R) ×
    (Ideal.Quotient.mk (Ideal.span ({(2 : R)} : Set R))).toAddMonoidHom.ker :=
  GramScaling.preimageEquiv (Ideal.Quotient.mk _).toAddMonoidHom
    Ideal.Quotient.mk_surjective {x : TwoQuotient R | x ^ 2 = 1}

/-- Exact split norm-one count in a finite local ring of residue characteristic two. -/
theorem split_card [Finite R] (h2 : ¬ IsUnit (2 : R)) :
    Nat.card (NormOne R 1) = Nat.card R * Nat.card (Roots (TwoQuotient R)) := by
  rw [Nat.card_congr (splitEquiv R h2), Nat.card_prod,
    Nat.card_congr (rootLiftsEquiv R), Nat.card_prod, RamifiedBinaryDensity.annihilator_card]
  let f := (Ideal.Quotient.mk (Ideal.span ({(2 : R)} : Set R))).toAddMonoidHom
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hc := f.ker.card_mul_index
  rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hf,
    Nat.card_congr (AddSubgroup.topEquiv : (⊤ : AddSubgroup (TwoQuotient R)) ≃+ _).toEquiv] at hc
  linear_combination Nat.card (Roots (TwoQuotient R)) * hc

/-- The split norm-one density is the finite root count modulo two, including nilpotents. -/
theorem split_density [Finite R] (h2 : ¬ IsUnit (2 : R)) :
    LocalNormDensity.density R 1 = Nat.card (Roots (TwoQuotient R)) := by
  unfold LocalNormDensity.density
  rw [split_card R h2, Nat.cast_mul, mul_div_cancel_left₀]
  exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt Nat.card_pos)

end NormEuclidean.DyadicSplitNormDensity
