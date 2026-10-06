import TraceEuclidean.MellinGrowthCore
import TraceEuclidean.OdlyzkoNumerical

/-!
# Odlyzko consequences of the Mellin growth estimates

This file keeps the zero-summability and certified numerical consequences
separate from the analytic growth core used by the Landau contour argument.
-/

namespace TraceEuclidean.MellinGrowth

noncomputable section

open Filter Set Asymptotics NumberField

/-- The theta--Mellin construction supplies the coarse quadratic zero count
needed for the Odlyzko zero sum, without an additional analytic input. -/
theorem exists_constructedDedekindZeta_quadraticCountInput
    (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 ≤ C ∧
      TraceEuclidean.DedekindZetaZeroOccurrence.QuadraticCountInput
        (TraceEuclidean.constructedDedekindZetaRegularization K) C := by
  obtain ⟨c, A, hc, hA, hGrowth⟩ :=
    exists_completedZetaPoleRemoved_circle_growth K
  let C : ℝ :=
    (A + |Real.log
      ‖DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K c‖|) /
        Real.log 2
  have hC : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg (add_nonneg hA (abs_nonneg _))
      (le_of_lt (Real.log_pos (by norm_num)))
  refine ⟨C, hC, ?_⟩
  exact
    TraceEuclidean.DedekindZetaZeroOccurrence.quadraticCount_of_completed_circle_growth
      (K := K) c hc A hA hGrowth

/-- The Odlyzko test function is absolutely summable over the actual zeros of
the constructed ordinary Dedekind-zeta regularization. -/
theorem constructedDedekindZeta_odlyzkoPhi_summable
    (K : Type*) [Field K] [NumberField K] :
    Summable (fun o : TraceEuclidean.DedekindZetaZeroOccurrence
      (TraceEuclidean.constructedDedekindZetaRegularization K) ↦
        TraceEuclidean.odlyzkoPhi o.value) := by
  obtain ⟨c, A, hc, hA, hGrowth⟩ :=
    exists_completedZetaPoleRemoved_circle_growth K
  exact
    TraceEuclidean.DedekindZetaZeroOccurrence.phi_summable_of_completed_circle_growth
      (K := K) c hc A hA hGrowth

/-- After the theta--Mellin growth argument and the certified numerical
integrals, the literature's explicit formula is the sole remaining premise for
the Table 4 correction. -/
theorem odlyzkoTable4_of_constructed_explicitFormula
    (hFormula : TraceEuclidean.OdlyzkoExplicitFormulaInput
      (fun K ↦ (∑' o : TraceEuclidean.DedekindZetaZeroOccurrence
        (TraceEuclidean.constructedRegularizationFamily K),
          TraceEuclidean.odlyzkoPhi o.value).re)) :
    TraceEuclidean.OdlyzkoTable4ExplicitCorrectionInput := by
  have hExist : ∀ K : TraceEuclidean.CodedNumberField,
      ∃ c : ℂ, ∃ A : ℝ,
        DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K.1 c ≠ 0 ∧
        0 ≤ A ∧
        ∀ T : ℝ, 0 ≤ T →
          ∀ z ∈ Metric.sphere c (2 * (‖c‖ + T + 2)),
            ‖DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K.1 z‖ ≤
              Real.exp (A * (1 + T) ^ 2) := by
    intro K
    exact exists_completedZetaPoleRemoved_circle_growth K.1
  choose center A hCenter hA hGrowth using hExist
  exact TraceEuclidean.odlyzkoTable4_of_constructed_completed_circle_growth
    center hCenter A hA hGrowth hFormula
      TraceEuclidean.OdlyzkoNumerical.abIntegralCertificate

end
end TraceEuclidean.MellinGrowth
