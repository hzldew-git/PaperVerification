import NormEuclidean.ChapterX.GlobalSquare
import NormEuclidean.ChapterX.OddRamifiedNormIndices

/-!
# Square descent through a quadratic extension

The coordinate calculation underlying O'Meara 65:16 shows that a base
scalar becoming square in K(sqrt(b)) was already square or became square
after multiplication by b. Odd local unit square classes give the
corresponding nonsquare-product test used for prime selection.
-/

noncomputable section

namespace NormEuclidean.QuadraticSquareDescent

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm
open scoped NumberField QuadraticAlgebra

/-- A base square in a quadratic extension has one of the two expected square classes. -/
theorem square_base_iff {F : Type*} [Field F] [CharZero F]
    (b : Fˣ) (hb : ¬ IsSquare b) (a : Fˣ) :
    letI := quadraticExtensionField b hb
    IsSquare (Units.map (algebraMap F (QuadraticAlgebra F b.val 0)).toMonoidHom a) ↔
      IsSquare a ∨ IsSquare (a * b) := by
  letI := quadraticExtensionField b hb
  rw [GlobalSquare.unit_square_iff]
  constructor
  · rintro ⟨z, hz⟩
    have hre := congrArg QuadraticAlgebra.re hz
    have him := congrArg QuadraticAlgebra.im hz
    change a.val = z.re * z.re + b.val * z.im * z.im at hre
    change 0 = z.re * z.im + z.im * z.re + 0 * z.im * z.im at him
    have hzero : z.re = 0 ∨ z.im = 0 := by
      have h : (2 : F) * (z.re * z.im) = 0 := by linear_combination -him
      exact mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (by norm_num))
    rcases hzero with hr | hi
    · right
      apply (GlobalSquare.unit_square_iff (a * b)).mpr
      refine ⟨b.val * z.im, ?_⟩
      change a.val * b.val = _
      simp only [hr, zero_mul, zero_add] at hre
      rw [hre]
      ring
    · left
      apply (GlobalSquare.unit_square_iff a).mpr
      exact ⟨z.re, by simpa [hi] using hre⟩
  · intro h
    rcases h with h | h
    · exact (GlobalSquare.unit_square_iff _).mp (h.map _)
    · obtain ⟨r, hr⟩ := (GlobalSquare.unit_square_iff (a * b)).mp h
      refine ⟨⟨0, r / b.val⟩, ?_⟩
      have he : a.val * b.val = r * r := hr
      apply QuadraticAlgebra.ext
      · change a.val = 0 * 0 + b.val * (r / b.val) * (r / b.val)
        field_simp [b.ne_zero]
        linear_combination he
      · simp

variable {K : Type*} [Field K] [NumberField K]

/-- At an odd finite place, a product of two nonsquare units is a square. -/
theorem nonsquare_unit_product (p : HeightOneSpectrum (𝓞 K))
    (htwo : (2 : 𝓞 K) ∉ p.asIdeal) (a b : (p.adicCompletion K)ˣ)
    (ha : Valued.v a.val = 1) (hb : Valued.v b.val = 1)
    (hans : ¬ IsSquare a) (hbns : ¬ IsSquare b) : IsSquare (a * b) := by
  obtain ⟨d, _, _, hclass⟩ := OddRamifiedNormIndices.exists_unit_class p htwo
  have had : IsSquare (a * d) := (hclass a ha).resolve_left hans
  have hbd : IsSquare (b * d) := (hclass b hb).resolve_left hbns
  have hs := had.mul hbd
  have hdd : IsSquare (d * d) := ⟨d, rfl⟩
  have hh := hs.mul hdd.inv
  have heq : (a * d) * (b * d) * (d * d)⁻¹ = a * b := by
    calc
      _ = (a * b) * ((d * d) * (d * d)⁻¹) := by ac_rfl
      _ = _ := by simp
  rw [heq] at hh
  exact hh

end NormEuclidean.QuadraticSquareDescent
