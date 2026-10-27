import NormEuclidean.ChapterX.MinkowskiSmallVector
import NormEuclidean.ChapterX.BoundedRepresentedValues
import NormEuclidean.ChapterX.ClassFinitenessInduction

/-!
# The anisotropic branches of 103:3 and 103:4

Actual Minkowski small vectors close finite represented-value coverage for a
fixed globally anisotropic regular space. Orthogonal complements remain
anisotropic, so rank induction gives actual finite ordinary class representatives.
The isotropic branch is not asserted or passed in as a disguised assumption.
-/

noncomputable section

namespace NormEuclidean.AnisotropicClassFiniteness

open Module ClassFinitenessInduction ProjectedComplement
open scoped nonZeroDivisors

universe u v

variable {K : Type v} {V : Type u} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [Invertible (2 : K)] in
/-- The full finite represented-value conclusion of 103:3 for the globally
anisotropic branch. Small-vector existence is proved internally. -/
theorem bounded_value_coverage (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hanis : ∀ x : V, Q x = 0 → x = 0)
    (hpos : 0 < Module.finrank K V)
    (c : FractionalIdeal (integerSubring K)⁰ K) (hc : c ≠ 0) :
    BoundedValueCoverage Q c := by
  let b := Module.finBasis K V
  obtain ⟨R, hR, hsmall⟩ := MinkowskiSmallVector.exists_uniform_small_vector Q hQ
    (Module.finrank K V) b hpos c hc
  obtain ⟨Φ, hΦ, hzero, hvalues⟩ :=
    BoundedRepresentedValues.exists_finite_values_of_small_vectors Q _ b R hR.le hanis
  refine ⟨Φ, hΦ, hzero, ?_⟩
  intro L hs hvol
  obtain ⟨x, hx, hx0, hxsmall⟩ := hsmall L hs hvol
  exact ⟨x, hx, hvalues L x hx hx0 hxsmall⟩

/-- In a fixed anisotropic regular space, integral-scale lattices above a
nonzero volume ideal have finitely many actual ordinary isometry classes.
There is no supplied represented-value or lower-rank finiteness premise. -/
theorem finite_volume_classes (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hanis : ∀ x : V, Q x = 0 → x = 0)
    (c : FractionalIdeal (integerSubring K)⁰ K) (hc : c ≠ 0) :
    HasFiniteVolumeClassRepresentatives Q c := by
  have h (n : ℕ) : ∀ (W : Type u) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
      (P : QuadraticForm K W), P.polarBilin.Nondegenerate →
        (∀ x : W, P x = 0 → x = 0) → Module.finrank K W = n →
          ∀ c : FractionalIdeal (integerSubring K)⁰ K, c ≠ 0 →
            HasFiniteVolumeClassRepresentatives P c := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ _ P hP hA hdim c hc
      by_cases hn0 : n = 0
      · exact finite_volume_classes_rank_zero P (hdim.trans hn0) c
      by_cases hn1 : n = 1
      · exact finite_volume_classes_rank_one P hP (hdim.trans hn1) c hc
      have htwo : 2 ≤ Module.finrank K W := by omega
      apply finite_volume_classes_step P hP htwo c
        (bounded_value_coverage P hP hA (by omega) c hc)
      intro y hy0
      let U := complement P y
      have hdimU := complement_finrank P y hy0
      have hlt : Module.finrank K U < n := by
        change Module.finrank K (complement P y) < n
        omega
      have hregular := complement_regular P hP y hy0
      have hanisU : ∀ x : U, (P.comp U.subtype) x = 0 → x = 0 := by
        intro x hx
        apply Subtype.ext
        exact hA x hx
      have hnonzero : FractionalIdeal.spanSingleton (integerSubring K)⁰
          (P y ^ (2 * Module.finrank K W)) * c ≠ 0 :=
        mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (pow_ne_zero _ hy0)) hc
      exact ih (Module.finrank K U) hlt U (P.comp U.subtype) hregular hanisU rfl _ hnonzero
  exact h (Module.finrank K V) V Q hQ hanis rfl c hc

end NormEuclidean.AnisotropicClassFiniteness
