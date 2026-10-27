import NormEuclidean.ChapterX.IsotropicValues
import NormEuclidean.ChapterX.AnisotropicClassFiniteness

/-!
# Number-field 103:3 and ordinary bounded-volume class finiteness

The anisotropic Minkowski argument and the actual isotropic common-value
construction cover every positive-dimensional regular number-field space.
The proved geometric rank induction now has no arithmetic coverage premise.
Zero dimension is a class-finiteness base and has no nonzero-value assertion.
-/

noncomputable section

namespace NormEuclidean.ClassFiniteness

open ClassFinitenessInduction
open scoped nonZeroDivisors

universe u v

variable {K : Type v} {V : Type u} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [Invertible (2 : K)] in
/-- The actual 103:3 represented-value coverage for every regular number-field
space of positive dimension, with both arithmetic branches proved internally. -/
theorem bounded_value_coverage (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hpos : 0 < Module.finrank K V)
    (c : FractionalIdeal (integerSubring K)⁰ K) (hc : c ≠ 0) :
    BoundedValueCoverage Q c := by
  classical
  by_cases hA : Q.Anisotropic
  · exact AnisotropicClassFiniteness.bounded_value_coverage Q hQ hA hpos c hc
  · obtain ⟨e, he, hiso⟩ := Q.not_anisotropic_iff_exists.mp hA
    exact IsotropicValues.bounded_value_coverage Q hQ e he hiso c hc

/-- Actual ordinary class representatives for all integral-scale lattices
above a fixed nonzero volume ideal on a fixed regular number-field space. -/
theorem finite_volume_classes (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (c : FractionalIdeal (integerSubring K)⁰ K) (hc : c ≠ 0) :
    HasFiniteVolumeClassRepresentatives Q c := by
  apply finite_volume_classes_of_bounded_value_coverage
    (fun W _ _ _ P hP hdim d hd ↦ bounded_value_coverage P hP (by omega) d hd) V Q hQ c hc

end NormEuclidean.ClassFiniteness
