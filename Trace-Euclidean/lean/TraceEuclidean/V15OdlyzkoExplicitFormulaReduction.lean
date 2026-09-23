import TraceEuclidean.V15OdlyzkoAnalyticBridge
import TraceEuclidean.V15OdlyzkoPhiEndpoint
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Source-exact analytic inputs for Odlyzko's Table 4 row

Odlyzko's 1990 survey, equation (2.3), separates the explicit formula into
two archimedean integrals, the exact endpoint error, a zero contribution,
and a prime-ideal contribution.  The elementary endpoint and prime terms
are proved elsewhere in this project.  This module records the remaining
analytic statements with their exact normalizations and proves that they
imply the previously used Table 4 interface.

This module does not assert the analytic inputs.
-/

namespace TraceEuclidean

noncomputable section
open MeasureTheory

/-- The archimedean integral multiplied by the field degree in (2.3). -/
def v15OdlyzkoSinhIntegral : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ),
    (1 - v15OdlyzkoF4 x) / (2 * Real.sinh (x / 2))

/-- The archimedean integral multiplied by the number of real places in (2.3). -/
def v15OdlyzkoCoshIntegral : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ),
    (1 - v15OdlyzkoF4 x) / (2 * Real.cosh (x / 2))

/-- The exact logarithmic constant per complex-signature dimension. -/
def v15OdlyzkoArchLogB : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) -
    v15OdlyzkoSinhIntegral

/-- The exact logarithmic constant per real place. -/
def v15OdlyzkoArchLogA : ℝ :=
  Real.pi / 2 + v15OdlyzkoArchLogB - v15OdlyzkoCoshIntegral

/-- A strict certificate for both table constants.  Integrability is included
so that the numerical inequalities cannot rely on the Bochner integral's
fallback value for a nonintegrable function. -/
def V15OdlyzkoABIntegralCertificate : Prop :=
  IntegrableOn
      (fun x : ℝ ↦ (1 - v15OdlyzkoF4 x) / (2 * Real.sinh (x / 2)))
      (Set.Ioi 0) ∧
    IntegrableOn
      (fun x : ℝ ↦ (1 - v15OdlyzkoF4 x) / (2 * Real.cosh (x / 2)))
      (Set.Ioi 0) ∧
    Real.log (36347 / 1000 : ℝ) < v15OdlyzkoArchLogA ∧
    Real.log (16593 / 1000 : ℝ) < v15OdlyzkoArchLogB

/-- Equation (2.3) with the exact `b=4` endpoint term and complete prime
correction.  The parameter `Z` must be supplied by a convergent paired-zero
sum in the source's normalization. -/
def V15OdlyzkoExplicitFormulaInput (Z : CodedNumberField → ℝ) : Prop :=
  ∀ K : CodedNumberField,
    Real.log (((|K.discriminant| : ℤ) : ℝ)) =
      (NumberField.InfinitePlace.nrRealPlaces K.1 : ℝ) * Real.pi / 2 +
      (Module.finrank ℚ K.1 : ℝ) *
        (Real.eulerMascheroniConstant + Real.log (8 * Real.pi)) -
      (Module.finrank ℚ K.1 : ℝ) * v15OdlyzkoSinhIntegral -
      (NumberField.InfinitePlace.nrRealPlaces K.1 : ℝ) *
        v15OdlyzkoCoshIntegral -
      4 * (∫ x in Set.Ioi (0 : ℝ),
        v15OdlyzkoF4 x * Real.cosh (x / 2)) +
      Z K + v15OdlyzkoPrimeCorrection K.1

/-- The explicit formula, nonnegative zero term, and certified strict
archimedean constants imply the exact-error Table 4 inequality with the
already formalized complete prime-ideal correction. -/
theorem v15_odlyzkoTable4ExplicitCorrectionInput_of_sourceFormula
    (Z : CodedNumberField → ℝ)
    (hFormula : V15OdlyzkoExplicitFormulaInput Z)
    (hZeros : ∀ K, 0 ≤ Z K)
    (hAB : V15OdlyzkoABIntegralCertificate) :
    V15OdlyzkoTable4ExplicitCorrectionInput := by
  intro K
  let r : ℕ := NumberField.InfinitePlace.nrRealPlaces K.1
  let c : ℕ := 2 * NumberField.InfinitePlace.nrComplexPlaces K.1
  have hrank : r + c = Module.finrank ℚ K.1 := by
    simpa [r, c] using
      (NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K.1)
  have hpos : 0 < r + c := by
    rw [hrank]
    exact Module.finrank_pos
  have hA : Real.log (36347 / 1000 : ℝ) < v15OdlyzkoArchLogA := hAB.2.2.1
  have hB : Real.log (16593 / 1000 : ℝ) < v15OdlyzkoArchLogB := hAB.2.2.2
  have hStrict :
      (r : ℝ) * Real.log (36347 / 1000 : ℝ) +
        (c : ℝ) * Real.log (16593 / 1000 : ℝ) <
      (r : ℝ) * v15OdlyzkoArchLogA +
        (c : ℝ) * v15OdlyzkoArchLogB := by
    have ha := mul_le_mul_of_nonneg_left hA.le (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
    have hb := mul_le_mul_of_nonneg_left hB.le (Nat.cast_nonneg c : (0 : ℝ) ≤ c)
    by_cases hr : r = 0
    · have hcpos : (0 : ℝ) < c := by
        exact_mod_cast (by omega : 0 < c)
      have hb' := mul_lt_mul_of_pos_left hB hcpos
      simp [hr] at ha ⊢
      linarith
    · have hrpos : (0 : ℝ) < r := by
        exact_mod_cast (Nat.pos_of_ne_zero hr)
      have ha' := mul_lt_mul_of_pos_left hA hrpos
      linarith
  have hdegree : (Module.finrank ℚ K.1 : ℝ) = (r : ℝ) + (c : ℝ) := by
    exact_mod_cast hrank.symm
  have hLogD :
      Real.log (((|K.discriminant| : ℤ) : ℝ)) =
        (r : ℝ) * v15OdlyzkoArchLogA +
          (c : ℝ) * v15OdlyzkoArchLogB -
          (32 / 3 : ℝ) + Z K + v15OdlyzkoPrimeCorrection K.1 := by
    have h := hFormula K
    rw [show 4 * (∫ x in Set.Ioi (0 : ℝ),
        v15OdlyzkoF4 x * Real.cosh (x / 2)) = (32 / 3 : ℝ) from
      v15OdlyzkoF4_archimedean_error_integral] at h
    change Real.log (((|K.discriminant| : ℤ) : ℝ)) =
      (r : ℝ) * Real.pi / 2 +
      (Module.finrank ℚ K.1 : ℝ) *
        (Real.eulerMascheroniConstant + Real.log (8 * Real.pi)) -
      (Module.finrank ℚ K.1 : ℝ) * v15OdlyzkoSinhIntegral -
      (r : ℝ) * v15OdlyzkoCoshIntegral -
      (32 / 3 : ℝ) + Z K + v15OdlyzkoPrimeCorrection K.1 at h
    rw [hdegree] at h
    rw [h]
    unfold v15OdlyzkoArchLogA v15OdlyzkoArchLogB
    ring
  have hLogLower :
      (r : ℝ) * Real.log (36347 / 1000 : ℝ) +
        (c : ℝ) * Real.log (16593 / 1000 : ℝ) +
        (v15OdlyzkoPrimeCorrection K.1 - (32 / 3 : ℝ)) <
      Real.log (((|K.discriminant| : ℤ) : ℝ)) := by
    rw [hLogD]
    linarith [hStrict, hZeros K]
  have hDpos : 0 < (((|K.discriminant| : ℤ) : ℝ)) := by
    have hz : K.discriminant ≠ 0 := NumberField.discr_ne_zero K.1
    exact_mod_cast (abs_pos.mpr hz : (0 : ℤ) < |K.discriminant|)
  have hExp := Real.exp_lt_exp.mpr hLogLower
  rw [Real.exp_log hDpos] at hExp
  have hTarget :
      Real.exp ((r : ℝ) * Real.log (36347 / 1000 : ℝ) +
        (c : ℝ) * Real.log (16593 / 1000 : ℝ) +
        (v15OdlyzkoPrimeCorrection K.1 - (32 / 3 : ℝ))) =
      (36347 / 1000 : ℝ) ^ r * (16593 / 1000 : ℝ) ^ c *
        Real.exp (v15OdlyzkoPrimeCorrection K.1 - (32 / 3 : ℝ)) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul,
      Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 36347 / 1000),
      Real.exp_log (by norm_num : (0 : ℝ) < 16593 / 1000)]
  rw [hTarget] at hExp
  exact hExp

/-- When the explicit formula supplies a summable enumeration of zero terms
inside the critical strip, the already proved `Phi` sign theorem discharges
the remaining zero-sign premise of the source-formula reduction. -/
theorem v15_odlyzkoTable4ExplicitCorrectionInput_of_enumeratedZeros
    (zeros : CodedNumberField → ℕ → ℂ)
    (hStrip : ∀ K i, 0 ≤ (zeros K i).re ∧ (zeros K i).re ≤ 1)
    (hSummable : ∀ K, Summable (fun i ↦ v15OdlyzkoPhi (zeros K i)))
    (hFormula : V15OdlyzkoExplicitFormulaInput
      (fun K ↦ (∑' i, v15OdlyzkoPhi (zeros K i)).re))
    (hAB : V15OdlyzkoABIntegralCertificate) :
    V15OdlyzkoTable4ExplicitCorrectionInput := by
  apply v15_odlyzkoTable4ExplicitCorrectionInput_of_sourceFormula
    (fun K ↦ (∑' i, v15OdlyzkoPhi (zeros K i)).re) hFormula _ hAB
  intro K
  exact v15OdlyzkoPhi_zero_tsum_re_nonneg (zeros K) (hStrip K)
    (hSummable K)

end
end TraceEuclidean
