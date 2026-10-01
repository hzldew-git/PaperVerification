import TraceEuclidean.AnalyticTableBridge
import TraceEuclidean.DegreeFiveFrontierClassification

/-!
# Closed degree-five minimum-discriminant row

The sharpened Hunter construction and the exhaustive proof-bearing Rolle
frontier prove the quintic minimum `14641`.  This module packages that result
in the coded-number-field interface used by Section 4 and moves the remaining
exact-minimum input to degrees six through nine.
-/

namespace TraceEuclidean

noncomputable section

/-- Every totally real coded quintic field has absolute discriminant at least
`14641`. -/
theorem coded_degree_five_discriminant_ge_14641
    (K : CodedNumberField)
    (hreal : NumberField.IsTotallyReal K.1)
    (hdegree : Module.finrank ℚ K.1 = 5) :
    (14641 : ℝ) ≤ ((|K.discriminant| : ℤ) : ℝ) := by
  by_contra hnot
  have hlt : ((|K.discriminant| : ℤ) : ℝ) < 14641 :=
    lt_of_not_ge hnot
  exact no_totallyRealQuinticField_discriminant_lt_14641
    K.1 hreal hdegree hlt

/-- The internal quintic theorem and residual degree-six through degree-nine
input imply the former degree-five through degree-nine interface. -/
theorem degreeFiveToNineMinimumInput_of_sixToNine
    (hMin : DegreeSixToNineMinimumInput) :
    DegreeFiveToNineMinimumInput := by
  intro K hreal
  dsimp only
  intro hd5 hd9
  by_cases hdegree : Module.finrank ℚ K.1 = 5
  · simpa [hdegree, minimumDiscriminant] using
      coded_degree_five_discriminant_ge_14641 K hreal hdegree
  · exact hMin K hreal (by omega) hd9

end

end TraceEuclidean
