import NormEuclidean.ChapterX.SUnitNormArithmetic
import NormEuclidean.ChapterX.SUnitNormFiniteness
import NormEuclidean.ChapterX.NormFiberAssembly

/-!
# Base-valued envelopes of balanced quadratic elements

When two and the quadratic parameter are valuation units, equal valuations
of z and its conjugate force the value of z to equal the maximum of the
values of its two base coordinates. This permits a base scalar adjustment
without assuming a ramification-index theorem.
-/

noncomputable section

namespace NormEuclidean.BalancedQuadraticValuations

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm SUnitNormArithmetic
open scoped NumberField WithZero QuadraticAlgebra

/-- Balanced conjugate valuations equal the envelope of the base coordinates. -/
theorem value_eq_max {F : Type*} [Field F] [CharZero F] (theta : F)
    (v : Valuation (QuadraticAlgebra F theta 0) ℤᵐ⁰)
    (htwo : v 2 = 1) (homega : v ω = 1) (z : QuadraticAlgebra F theta 0)
    (hbalanced : v z = v (star z)) :
    v z = max (v (algebraMap F _ z.re)) (v (algebraMap F _ z.im)) := by
  let a := algebraMap F (QuadraticAlgebra F theta 0) z.re
  let b := algebraMap F (QuadraticAlgebra F theta 0) z.im * ω
  have hz : z = a + b := by ext <;> simp [a, b]
  have ha : (2 : QuadraticAlgebra F theta 0) * a = z + star z := by
    ext <;> simp [a] <;> ring
  have hb : (2 : QuadraticAlgebra F theta 0) * b = z - star z := by
    ext <;> simp [b] <;> ring
  have hba : v b = v (algebraMap F _ z.im) := by rw [map_mul, homega, mul_one]
  have hleA : v a ≤ v z := by
    have h := v.map_add z (star z)
    rw [← ha, map_mul, htwo, one_mul, ← hbalanced, max_self] at h
    exact h
  have hleB : v b ≤ v z := by
    have h := v.map_sub z (star z)
    rw [← hb, map_mul, htwo, one_mul, ← hbalanced, max_self] at h
    exact h
  apply le_antisymm
  · calc
      v z = v (a + b) := congrArg v hz
      _ ≤ max (v a) (v b) := v.map_add a b
      _ = _ := congrArg (max (v a)) hba
  · exact max_le hleA (hba ▸ hleB)

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- The two-coordinate envelope is attained by a nonzero base coordinate. -/
theorem exists_coordinate_envelope (z : K × K) (hz : z ≠ 0)
    (p : HeightOneSpectrum (𝓞 K)) :
    ∃ a : Kˣ, p.valuation K a.val = max (p.valuation K z.1) (p.valuation K z.2) := by
  by_cases h : p.valuation K z.1 ≤ p.valuation K z.2
  · have hne : z.2 ≠ 0 := by
      intro hy
      have hxv : p.valuation K z.1 = 0 := le_antisymm
        (by simpa only [hy, map_zero] using h) bot_le
      have hx : z.1 = 0 := (Valuation.zero_iff (p.valuation K)).mp hxv
      exact hz (Prod.ext hx hy)
    exact ⟨Units.mk0 z.2 hne, (max_eq_right h).symm⟩
  · have hne : z.1 ≠ 0 := by
      intro hx
      exact h (by simp only [hx, map_zero]; exact bot_le)
    exact ⟨Units.mk0 z.1 hne, (max_eq_left (le_of_not_ge h)).symm⟩

end NormEuclidean.BalancedQuadraticValuations
