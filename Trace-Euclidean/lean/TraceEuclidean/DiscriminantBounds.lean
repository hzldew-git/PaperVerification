import TraceEuclidean.GlobalLatticeClass
import TraceEuclidean.GeometricBounds
import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-!
Discriminant bounds needed in the global finiteness argument.
-/

namespace TraceEuclidean

open scoped NumberField

noncomputable section

/-- The totally-real Minkowski lower bound for degree `d`. -/
def totallyRealMinkowskiDiscriminantLowerBound (d : ℕ) : ℝ :=
  (d : ℝ) ^ (2 * d) / (d.factorial : ℝ) ^ 2

/-- The lower bound is positive in positive degree. -/
theorem totallyRealMinkowskiDiscriminantLowerBound_pos
    {d : ℕ} (hd : 0 < d) :
    0 < totallyRealMinkowskiDiscriminantLowerBound d := by
  unfold totallyRealMinkowskiDiscriminantLowerBound
  positivity

/--
The exact intermediate volume bound obtained before applying the two Gamma
estimates in Lemma 3.4 of the manuscript.
-/
def minkowskiTraceVolumeBound (t : ℝ) (n d : ℕ) : ℝ :=
  euclideanUnitBallVolume (n * d) ^ (2 : ℕ) * t ^ (n * d) /
    totallyRealMinkowskiDiscriminantLowerBound d ^ n

/-- Scaling the trace radius by two multiplies the intermediate bound by `2^(nd)`. -/
theorem minkowskiTraceVolumeBound_two_mul
    (t : ℝ) (n d : ℕ) :
    minkowskiTraceVolumeBound (2 * t) n d =
      2 ^ (n * d) * minkowskiTraceVolumeBound t n d := by
  unfold minkowskiTraceVolumeBound
  rw [mul_pow]
  ring

namespace GlobalLatticePresentation

/--
The exact totally-real specialization of mathlib's Minkowski discriminant
lower bound used in the manuscript.
-/
theorem minkowski_discriminant_lower_bound
    (P : GlobalLatticePresentation) :
    totallyRealMinkowskiDiscriminantLowerBound P.degree ≤
      ((|P.field.discriminant| : ℤ) : ℝ) := by
  letI : NumberField.IsTotallyReal P.field.1 := P.totallyReal
  simpa [totallyRealMinkowskiDiscriminantLowerBound,
    GlobalLatticePresentation.degree, NumberFieldCode.discriminant,
    NumberField.IsTotallyReal.nrComplexPlaces_eq_zero] using
      (NumberField.abs_discr_ge' P.field.1)

end GlobalLatticePresentation

namespace GlobalLatticeClass

/-- The Minkowski lower bound for the selected field of a quotient class. -/
theorem minkowski_discriminant_lower_bound (c : GlobalLatticeClass) :
    totallyRealMinkowskiDiscriminantLowerBound c.degree ≤
      ((|c.fieldCode.discriminant| : ℤ) : ℝ) := by
  simpa only [fieldCode, representative_degree] using
    c.representative.minkowski_discriminant_lower_bound

end GlobalLatticeClass

end

end TraceEuclidean
