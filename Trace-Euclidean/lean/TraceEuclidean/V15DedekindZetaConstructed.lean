import DedekindZeta.ZetaRegularization
import TraceEuclidean.V15DedekindZetaZeros
import TraceEuclidean.V15DedekindZetaJensenCount
import TraceEuclidean.V15AnalyticMellinBridge

/-!
# Constructing the regularized Dedekind zeta used by the zero theory

The number-field theta/Mellin argument gives an entire function which agrees
with `(s-1) ζ_K(s)` on `Re s > 1`. This closes the existence premise of the
previously conditional zero-theory interface.
-/

namespace TraceEuclidean

noncomputable section

open NumberField DedekindZeta.ConeRadialReduction DedekindZeta.MellinPrinciple
open scoped nonZeroDivisors

/-- Each continued partial zeta has the expected reflected dual radial
Mellin expression away from the former pole locations. Assembling the
completed zeta functional equation additionally requires reindexing the
dual fractional ideals across the class group. -/
theorem v15_completedPartialZeta_reflected_radial
    (K : Type*) [Field K] [NumberField K]
    (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) (s : ℂ)
    (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    DedekindZeta.GlobalContinuation.completedPartialZetaContinuation K 𝔞 s =
      (1 / (NumberField.Units.torsionOrder K : ℂ)) *
        (Ideal.absNorm 𝔞 : ℂ) ^ s *
          (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2)) *
            (((DedekindZeta.Theta.covolume K 𝔞 : ℂ)⁻¹) *
              mellinContinuation (radialThetaDual K 𝔞) (radialTheta K 𝔞)
                (surfaceVolume K) (surfaceVolume K)
                (((DedekindZeta.Theta.covolume K 𝔞 : ℂ)⁻¹)⁻¹)
                1 (1 - s)) := by
  obtain ⟨c, α, hpair⟩ :=
    exists_isMellinPair_radialTheta (K := K) 𝔞 hne
  unfold DedekindZeta.GlobalContinuation.completedPartialZetaContinuation
  rw [V15AnalyticMellin.mellinContinuation_reflection hpair s hs₀ hs₁]
  simp only [Complex.ofReal_one, sub_eq_add_neg, add_comm]

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
