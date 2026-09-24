import DedekindZeta.ZetaRegularization
import TraceEuclidean.V15DedekindZetaZeros
import TraceEuclidean.V15DedekindZetaJensenCount

/-!
# Constructing the regularized Dedekind zeta used by the zero theory

The number-field theta/Mellin argument gives an entire function which agrees
with `(s-1) ζ_K(s)` on `Re s > 1`. This closes the existence premise of the
previously conditional zero-theory interface.
-/

namespace TraceEuclidean

noncomputable section

/-- The actual entire regularization of Dedekind zeta supplied by the
number-field theta/Mellin construction. -/
def v15ConstructedDedekindZetaRegularization (K : Type*) [Field K] [NumberField K] :
    V15DedekindZetaRegularization K where
  value := DedekindZeta.ZetaRegularization.dedekindZetaRegularized K
  analytic := DedekindZeta.ZetaRegularization.dedekindZetaRegularized_analyticOn K
  agrees_right := by
    intro s hs
    exact DedekindZeta.ZetaRegularization.dedekindZetaRegularized_eq K hs

/-- The number-field regularization is available uniformly for every coded
field used by the Odlyzko argument. -/
def v15ConstructedRegularizationFamily (K : CodedNumberField) :
    V15DedekindZetaRegularization K.1 :=
  v15ConstructedDedekindZetaRegularization K.1

/-- The Table 4 reduction now needs a circle growth estimate and the explicit
formula, but no assumed existence of a Dedekind-zeta regularization. -/
theorem v15_odlyzkoTable4_of_constructed_circle_growth
    (center : CodedNumberField → ℂ)
    (hCenter : ∀ K, (v15ConstructedRegularizationFamily K).value (center K) ≠ 0)
    (A : CodedNumberField → ℝ) (hA : ∀ K, 0 ≤ A K)
    (hGrowth : ∀ K : CodedNumberField, ∀ T : ℝ, 0 ≤ T →
      ∀ z ∈ Metric.sphere (center K) (2 * (‖center K‖ + T + 2)),
        ‖(v15ConstructedRegularizationFamily K).value z‖ ≤
          Real.exp (A K * (1 + T) ^ 2))
    (hFormula : V15OdlyzkoExplicitFormulaInput
      (fun K ↦ (∑' o : V15DedekindZetaZeroOccurrence
        (v15ConstructedRegularizationFamily K), v15OdlyzkoPhi o.value).re))
    (hAB : V15OdlyzkoABIntegralCertificate) :
    V15OdlyzkoTable4ExplicitCorrectionInput := by
  exact v15_odlyzkoTable4ExplicitCorrectionInput_of_circle_growth
    v15ConstructedRegularizationFamily center hCenter A hA hGrowth hFormula hAB

end
end TraceEuclidean
