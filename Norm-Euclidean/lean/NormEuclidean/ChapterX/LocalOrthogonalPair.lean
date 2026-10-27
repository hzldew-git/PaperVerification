import NormEuclidean.ChapterX.LocalOrthogonalSplitting

/-!
# Two unit lines containing a primitive nonunit-norm vector

This is the elementary non-dyadic splitting calculation in 82:17 and
104:3. A unit mixed pairing supplies the two unit norms and the explicit
decomposition; neither a binary frame nor a representation law is assumed.
-/

noncomputable section

namespace NormEuclidean.LocalOrthogonalPair

variable {S M : Type*} [CommRing S] [IsLocalRing S] [AddCommGroup M] [Module S M]

/-- Adding a nonunit to a unit in a local ring preserves being a unit. -/
theorem isUnit_add_nonunit {a b : S} (ha : IsUnit a) (hb : ¬ IsUnit b) :
    IsUnit (a + b) := by
  by_contra hab
  let I := IsLocalRing.maximalIdeal S
  have hsum : a + b ∈ I := hab
  have hmem : a ∈ I := by simpa only [add_sub_cancel_right] using I.sub_mem hsum hb
  exact hmem ha

/-- A unit mixed pairing with a nonunit-norm vector gives a unit-norm
partner whose pairing with that vector is still a unit. -/
theorem exists_unit_partner (B : LinearMap.BilinForm S M) (hB : B.IsSymm)
    (htwo : IsUnit (2 : S)) (x y : M) (hx : ¬ IsUnit (B x x)) (hxy : IsUnit (B x y)) :
    ∃ e : M, IsUnit (B e e) ∧ IsUnit (B x e) := by
  by_cases hy : IsUnit (B y y)
  · exact ⟨y, hy, hxy⟩
  refine ⟨x + y, ?_, ?_⟩
  · have hdiag : ¬ IsUnit (B x x + B y y) := by
      intro h
      exact (IsLocalRing.isUnit_or_isUnit_of_isUnit_add h).elim hx hy
    have heq : B (x + y) (x + y) = 2 * B x y + (B x x + B y y) := by
      rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
        LinearMap.BilinForm.add_right, hB.eq y x]
      ring
    rw [heq]
    exact isUnit_add_nonunit (htwo.mul hxy) hdiag
  · rw [LinearMap.BilinForm.add_right, add_comm]
    exact isUnit_add_nonunit hxy hx

/-- Orthogonalization stays in the integral module and gives a second
unit norm. The original vector is explicitly in the span of the two lines. -/
theorem exists_orthogonal_pair (B : LinearMap.BilinForm S M) (hB : B.IsSymm)
    (htwo : IsUnit (2 : S)) (x y : M) (hx : ¬ IsUnit (B x x)) (hxy : IsUnit (B x y)) :
    ∃ (e f : M) (r : S), IsUnit (B e e) ∧ IsUnit (B f f) ∧ B e f = 0 ∧
      x = f + r • e := by
  obtain ⟨e, he, hxe⟩ := exists_unit_partner B hB htwo x y hx hxy
  let u := he.unit
  have hu : B e e = (u : S) := he.unit_spec.symm
  let r := B x e * (↑(u⁻¹) : S)
  let f := x - r • e
  have horth : B e f = 0 := by
    simp only [f, LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right,
      hB.eq e x, r, hu]
    rw [mul_assoc, Units.inv_mul, mul_one, sub_self]
  have hnorm : B f f = B x x - B x e ^ 2 * (↑(u⁻¹) : S) := by
    simp only [f, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hB.eq e x, r, hu]
    calc
      _ = B x x - 2 * (B x e ^ 2 * (↑(u⁻¹) : S)) +
          B x e ^ 2 * (↑(u⁻¹) : S) * ((↑(u⁻¹) : S) * ↑u) := by ring
      _ = _ := by rw [Units.inv_mul]; ring
  have hunit : IsUnit (B f f) := by
    rw [hnorm]
    have hterm : IsUnit (B x e ^ 2 * (↑(u⁻¹) : S)) := (hxe.pow 2).mul u⁻¹.isUnit
    have h := isUnit_add_nonunit hterm.neg hx
    simpa only [add_comm, sub_eq_add_neg] using h
  exact ⟨e, f, r, he, hunit, horth, by simp only [f, sub_add_cancel]⟩

end NormEuclidean.LocalOrthogonalPair
