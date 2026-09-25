import TraceEuclidean.V15OdlyzkoEndpointContour
import TraceEuclidean.V15OdlyzkoNumerical
import TraceEuclidean.V15OdlyzkoVerticalLimit
import TraceEuclidean.V15AnalyticTableBridge
import TraceEuclidean.V15PNorm
import TraceEuclidean.V15RankOneIntegral

/-!
# Closing the Odlyzko discriminant inequality

This module combines the completed-zeta contour inequality with the exact
endpoint, archimedean, and prime-power transforms.  It produces the strict
Table 4 discriminant inequality without taking the Stark--Weil explicit
formula as an additional input.
-/

namespace TraceEuclidean

noncomputable section

open Complex Filter MeasureTheory Set Topology

/-- The ordinary Dedekind-zeta contribution on the right vertical line. -/
def v15OdlyzkoPrimeLineIntegrand
    (K : Type*) [Field K] [NumberField K] (t : ℝ) : ℂ :=
  v15OdlyzkoPhi ((2 : ℂ) + (t : ℂ) * I) *
    logDeriv (NumberField.dedekindZeta K)
      ((2 : ℂ) + (t : ℂ) * I)

/-- On the right line, the folded completed-zeta integrand is the sum of
twice the endpoint, archimedean, and ordinary-zeta contributions. -/
theorem v15OdlyzkoCompletedVerticalPair_decomposition
    (K : Type*) [Field K] [NumberField K] (t : ℝ) :
    v15OdlyzkoCompletedVerticalPair K t =
      2 * v15OdlyzkoEndpointIntegrand
          ((2 : ℂ) + (t : ℂ) * I) +
        2 * v15OdlyzkoArchimedeanIntegrand K
          ((2 : ℂ) + (t : ℂ) * I) +
        2 * v15OdlyzkoPrimeLineIntegrand K t := by
  let s : ℂ := (2 : ℂ) + (t : ℂ) * I
  have hs : 1 < s.re := by simp [s]
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
  rw [v15OdlyzkoCompletedVerticalPair_eq_two_mul]
  change
    2 * (v15OdlyzkoPhi s *
        logDeriv
          (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s) =
      2 * v15OdlyzkoEndpointIntegrand s +
        2 * v15OdlyzkoArchimedeanIntegrand K s +
        2 * (v15OdlyzkoPhi s *
          logDeriv (NumberField.dedekindZeta K) s)
  rw [DedekindZeta.LogDeriv.logDeriv_completedZetaPoleRemoved K hs]
  rw [v15OdlyzkoEndpointIntegrand,
    v15OdlyzkoEndpointPolynomial_logDeriv hs0 hs1]
  simp only [v15OdlyzkoArchimedeanIntegrand]
  ring

/-- Twice the right-line archimedean contribution is absolutely
integrable. -/
theorem v15OdlyzkoArchimedean_twice_right_integrable
    (K : Type*) [Field K] [NumberField K] :
    Integrable (fun t : ℝ ↦ 2 * v15OdlyzkoArchimedeanIntegrand K
      ((2 : ℂ) + (t : ℂ) * I)) volume := by
  have h := v15OdlyzkoArchimedeanIntegrand_vertical_integrable K
    (σ := (2 : ℝ)) (by norm_num) (by norm_num)
  have h' : Integrable (fun t : ℝ ↦
      v15OdlyzkoArchimedeanIntegrand K
        ((2 : ℂ) + (t : ℂ) * I)) volume := by
    simpa using h
  exact h'.const_mul 2

/-- Twice the ordinary-zeta right-line contribution is absolutely
integrable.  This follows from the completed decomposition and the already
proved integrability of its other two summands. -/
theorem v15OdlyzkoPrimeLine_twice_integrable
    (K : Type*) [Field K] [NumberField K] :
    Integrable (fun t : ℝ ↦ 2 * v15OdlyzkoPrimeLineIntegrand K t)
      volume := by
  have hPair := v15OdlyzkoCompletedVerticalPair_integrable K
  have hEndpoint := v15OdlyzkoEndpoint_twice_right_integrable
  have hArch := v15OdlyzkoArchimedean_twice_right_integrable K
  apply ((hPair.sub hEndpoint).sub hArch).congr
  filter_upwards with t
  change v15OdlyzkoCompletedVerticalPair K t -
      2 * v15OdlyzkoEndpointIntegrand ((2 : ℂ) + (t : ℂ) * I) -
      2 * v15OdlyzkoArchimedeanIntegrand K
        ((2 : ℂ) + (t : ℂ) * I) =
    2 * v15OdlyzkoPrimeLineIntegrand K t
  rw [v15OdlyzkoCompletedVerticalPair_decomposition K t]
  ring

/-- The full folded vertical integral splits into the three source-normalized
pieces. -/
theorem v15OdlyzkoCompletedVerticalPair_integral_decomposition
    (K : Type*) [Field K] [NumberField K] :
    (∫ t : ℝ, v15OdlyzkoCompletedVerticalPair K t) =
      (∫ t : ℝ, 2 * v15OdlyzkoEndpointIntegrand
          ((2 : ℂ) + (t : ℂ) * I)) +
        (∫ t : ℝ, 2 * v15OdlyzkoArchimedeanIntegrand K
          ((2 : ℂ) + (t : ℂ) * I)) +
        ∫ t : ℝ, 2 * v15OdlyzkoPrimeLineIntegrand K t := by
  have hEndpoint := v15OdlyzkoEndpoint_twice_right_integrable
  have hArch := v15OdlyzkoArchimedean_twice_right_integrable K
  have hPrime := v15OdlyzkoPrimeLine_twice_integrable K
  calc
    (∫ t : ℝ, v15OdlyzkoCompletedVerticalPair K t) =
        ∫ t : ℝ,
          (2 * v15OdlyzkoEndpointIntegrand
              ((2 : ℂ) + (t : ℂ) * I) +
            2 * v15OdlyzkoArchimedeanIntegrand K
              ((2 : ℂ) + (t : ℂ) * I)) +
            2 * v15OdlyzkoPrimeLineIntegrand K t := by
      apply integral_congr_ae
      filter_upwards with t
      rw [v15OdlyzkoCompletedVerticalPair_decomposition K t]
    _ = _ := by
      let f : ℝ → ℂ := fun t ↦ 2 * v15OdlyzkoEndpointIntegrand
        ((2 : ℂ) + (t : ℂ) * I)
      let g : ℝ → ℂ := fun t ↦ 2 * v15OdlyzkoArchimedeanIntegrand K
        ((2 : ℂ) + (t : ℂ) * I)
      let p : ℝ → ℂ := fun t ↦ 2 * v15OdlyzkoPrimeLineIntegrand K t
      have hfg := integral_add hEndpoint hArch
      have hfgp := integral_add (hEndpoint.add hArch) hPrime
      change (∫ t : ℝ, (f + g + p) t) = _
      change (∫ t : ℝ, (f + g + p) t) =
        (∫ t : ℝ, f t) + (∫ t : ℝ, g t) + ∫ t : ℝ, p t
      change (∫ t : ℝ, (f + g) t) =
        (∫ t : ℝ, f t) + ∫ t : ℝ, g t at hfg
      change (∫ t : ℝ, (f + g + p) t) =
        (∫ t : ℝ, (f + g) t) + ∫ t : ℝ, p t at hfgp
      rw [hfgp, hfg]

/-- The normalized ordinary-zeta integral is minus the complete prime-ideal
correction. -/
theorem v15OdlyzkoPrimeLine_normalized_integral
    (K : Type*) [Field K] [NumberField K] :
    (1 / (2 * Real.pi) : ℂ) *
        (∫ t : ℝ, 2 * v15OdlyzkoPrimeLineIntegrand K t) =
      -(v15OdlyzkoPrimeCorrection K : ℂ) := by
  have hPrime :=
    v15OdlyzkoPhi_mul_logDeriv_dedekindZeta_integral K 2 (by norm_num)
  change (1 / (2 * Real.pi) : ℂ) *
      (∫ t : ℝ, 2 *
        (v15OdlyzkoPhi ((2 : ℂ) + (t : ℂ) * I) *
          logDeriv (NumberField.dedekindZeta K)
            ((2 : ℂ) + (t : ℂ) * I))) = _
  rw [integral_const_mul]
  have hPrime' :
      (∫ t : ℝ,
        v15OdlyzkoPhi ((2 : ℂ) + (t : ℂ) * I) *
          logDeriv (NumberField.dedekindZeta K)
            ((2 : ℂ) + (t : ℂ) * I)) =
        -((Real.pi * v15OdlyzkoPrimeCorrection K : ℝ) : ℂ) := by
    simpa using hPrime
  rw [hPrime']
  have hPi : (Real.pi : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr Real.pi_pos.ne'
  push_cast
  field_simp [hPi]

/-- After `1/(2π)` normalization, the real part of the two archimedean
copies is the exact discriminant-and-signature expression. -/
theorem v15OdlyzkoArchimedean_normalized_integral_re
    (K : Type*) [Field K] [NumberField K] :
    ((1 / (2 * Real.pi) : ℂ) *
        (∫ t : ℝ, 2 * v15OdlyzkoArchimedeanIntegrand K
          ((2 : ℂ) + (t : ℂ) * I))).re =
      Real.log (((|NumberField.discr K| : ℤ) : ℝ)) -
        (NumberField.InfinitePlace.nrRealPlaces K : ℝ) *
          v15OdlyzkoArchLogA -
        2 * (NumberField.InfinitePlace.nrComplexPlaces K : ℝ) *
          v15OdlyzkoArchLogB := by
  have hArch := v15OdlyzkoArchimedean_right_twice_re_integral K
  have hCoeff :
      (1 / (2 * Real.pi) : ℂ) =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hCoeff]
  rw [integral_const_mul]
  norm_num [Complex.mul_re]
  norm_num at hArch
  have hPi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hPi]
  nlinarith

/-- Exact evaluation of the real part of the normalized folded vertical
integral in terms of the discriminant, signature, endpoint error, and prime
correction. -/
theorem v15OdlyzkoCompletedVerticalPair_normalized_integral_re
    (K : Type*) [Field K] [NumberField K] :
    ((1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ, v15OdlyzkoCompletedVerticalPair K t).re =
      32 / 3 +
        (Real.log (((|NumberField.discr K| : ℤ) : ℝ)) -
          (NumberField.InfinitePlace.nrRealPlaces K : ℝ) *
            v15OdlyzkoArchLogA -
          2 * (NumberField.InfinitePlace.nrComplexPlaces K : ℝ) *
            v15OdlyzkoArchLogB) -
        v15OdlyzkoPrimeCorrection K := by
  rw [v15OdlyzkoCompletedVerticalPair_integral_decomposition K]
  simp only [mul_add, Complex.add_re]
  rw [v15OdlyzkoEndpoint_normalized_integral,
    v15OdlyzkoArchimedean_normalized_integral_re K,
    v15OdlyzkoPrimeLine_normalized_integral K]
  norm_num
  ring

/-- The completed-zeta contour and positivity of its finite zero sums imply
the exact Odlyzko logarithmic discriminant lower bound. -/
theorem v15Odlyzko_discriminant_log_lower_bound
    (K : Type*) [Field K] [NumberField K] :
    (NumberField.InfinitePlace.nrRealPlaces K : ℝ) *
          v15OdlyzkoArchLogA +
        2 * (NumberField.InfinitePlace.nrComplexPlaces K : ℝ) *
          v15OdlyzkoArchLogB +
        v15OdlyzkoPrimeCorrection K - 32 / 3 ≤
      Real.log (((|NumberField.discr K| : ℤ) : ℝ)) := by
  have hNonneg := v15OdlyzkoCompletedVerticalPair_integral_re_nonneg K
  rw [v15OdlyzkoCompletedVerticalPair_normalized_integral_re K] at hNonneg
  linarith

/-- The contour lower bound and any certified strict bounds for the two
archimedean constants imply the exact-error Table 4 interface. -/
theorem v15_odlyzkoTable4ExplicitCorrectionInput_of_contour
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
  have hA :
      Real.log (36347 / 1000 : ℝ) < v15OdlyzkoArchLogA := hAB.2.1
  have hB :
      Real.log (16593 / 1000 : ℝ) < v15OdlyzkoArchLogB := hAB.2.2
  have hStrict :
      (r : ℝ) * Real.log (36347 / 1000 : ℝ) +
          (c : ℝ) * Real.log (16593 / 1000 : ℝ) <
        (r : ℝ) * v15OdlyzkoArchLogA +
          (c : ℝ) * v15OdlyzkoArchLogB := by
    have ha := mul_le_mul_of_nonneg_left hA.le
      (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
    have hb := mul_le_mul_of_nonneg_left hB.le
      (Nat.cast_nonneg c : (0 : ℝ) ≤ c)
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
  have hWeak :
      (r : ℝ) * v15OdlyzkoArchLogA +
          (c : ℝ) * v15OdlyzkoArchLogB +
          v15OdlyzkoPrimeCorrection K.1 - 32 / 3 ≤
        Real.log (((|K.discriminant| : ℤ) : ℝ)) := by
    simpa [r, c, NumberFieldCode.discriminant] using
      v15Odlyzko_discriminant_log_lower_bound K.1
  have hLogLower :
      (r : ℝ) * Real.log (36347 / 1000 : ℝ) +
          (c : ℝ) * Real.log (16593 / 1000 : ℝ) +
          (v15OdlyzkoPrimeCorrection K.1 - (32 / 3 : ℝ)) <
        Real.log (((|K.discriminant| : ℤ) : ℝ)) := by
    linarith
  have hDpos : 0 < (((|K.discriminant| : ℤ) : ℝ)) := by
    have hz : K.discriminant ≠ 0 := NumberField.discr_ne_zero K.1
    exact_mod_cast (abs_pos.mpr hz : (0 : ℤ) < |K.discriminant|)
  have hExp := Real.exp_lt_exp.mpr hLogLower
  rw [Real.exp_log hDpos] at hExp
  have hTarget :
      Real.exp ((r : ℝ) * Real.log (36347 / 1000 : ℝ) +
          (c : ℝ) * Real.log (16593 / 1000 : ℝ) +
          (v15OdlyzkoPrimeCorrection K.1 - (32 / 3 : ℝ))) =
        (36347 / 1000 : ℝ) ^ r *
          (16593 / 1000 : ℝ) ^ c *
          Real.exp (v15OdlyzkoPrimeCorrection K.1 - (32 / 3 : ℝ)) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul,
      Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 36347 / 1000),
      Real.exp_log (by norm_num : (0 : ℝ) < 16593 / 1000)]
  rw [hTarget] at hExp
  exact hExp

/-- Fully internal construction of the exact-error Table 4 input. -/
theorem v15_odlyzkoTable4ExplicitCorrectionInput_closed :
    V15OdlyzkoTable4ExplicitCorrectionInput :=
  v15_odlyzkoTable4ExplicitCorrectionInput_of_contour
    V15OdlyzkoNumerical.abIntegralCertificate

/-- The rounded Table 4 description used by the downstream v15 theorems now
follows without an analytic literature-input hypothesis. -/
theorem v15_odlyzkoTable4DescriptionInput_closed :
    V15OdlyzkoTable4DescriptionInput :=
  v15_odlyzkoTable4DescriptionInput_of_explicitCorrection
    v15_odlyzkoTable4ExplicitCorrectionInput_closed

/-- The Section 4 discriminant input after the internally proved Table 4
part is combined with the three cited small-degree estimates. -/
theorem v15_sectionFourDiscriminantInput_of_smallDegreeLiterature
    (hMin : V15DegreeTwoToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput) :
    V15SectionFourDiscriminantInput :=
  v15_sectionFourDiscriminantInput_of_literature hMin hTen hEleven
    v15_odlyzkoTable4DescriptionInput_closed

/-- The Section 4 discriminant input with both the analytic Table 4 range and
the quadratic minimum discharged internally.  The remaining literature inputs
cover degrees three through eleven. -/
theorem v15_sectionFourDiscriminantInput_of_reduced_smallDegreeLiterature
    (hMin : V15DegreeThreeToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput) :
    V15SectionFourDiscriminantInput :=
  v15_sectionFourDiscriminantInput_of_reduced_literature
    hMin hTen hEleven v15_odlyzkoTable4DescriptionInput_closed

/-- Membership in the manuscript's 24-row classic table after reducing the
external discriminant input to degrees three through eleven. -/
theorem v15_classic_pair_mem_of_reduced_smallDegreeLiterature
    (hMin : V15DegreeThreeToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput)
    (c : GlobalLatticeClass)
    (hE : c.IsClassicTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15ClassicAdmissiblePairs :=
  v15_classic_pair_mem_of_reduced_literature
    hMin hTen hEleven v15_odlyzkoTable4DescriptionInput_closed c hE

/-- Membership in the manuscript's 63-row integral table after reducing the
external discriminant input to degrees three through eleven. -/
theorem v15_integral_pair_mem_of_reduced_smallDegreeLiterature
    (hMin : V15DegreeThreeToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput)
    (c : GlobalLatticeClass)
    (hE : c.IsIntegralTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15IntegralAdmissiblePairs :=
  v15_integral_pair_mem_of_reduced_literature
    hMin hTen hEleven v15_odlyzkoTable4DescriptionInput_closed
    v15_rank_one_classic_input c hE

/-- The Section 4 discriminant input after replacing the cubic exact-minimum
table row by the normalized Hunter certificate. -/
theorem v15_sectionFourDiscriminantInput_of_hunterCertificate_closed
    (hHunter : V15DegreeThreeHunterCertificateInput)
    (hMin : V15DegreeFourToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput) :
    V15SectionFourDiscriminantInput :=
  v15_sectionFourDiscriminantInput_of_hunterCertificate
    hHunter hMin hTen hEleven v15_odlyzkoTable4DescriptionInput_closed

/-- Membership in the classic table from the cubic Hunter certificate and
the remaining degree-four to degree-eleven source inputs. -/
theorem v15_classic_pair_mem_of_hunterCertificate_closed
    (hHunter : V15DegreeThreeHunterCertificateInput)
    (hMin : V15DegreeFourToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput)
    (c : GlobalLatticeClass)
    (hE : c.IsClassicTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15ClassicAdmissiblePairs :=
  v15_classic_pair_mem_of_hunterCertificate
    hHunter hMin hTen hEleven v15_odlyzkoTable4DescriptionInput_closed c hE

/-- Membership in the integral table from the cubic Hunter certificate and
the remaining degree-four to degree-eleven source inputs. -/
theorem v15_integral_pair_mem_of_hunterCertificate_closed
    (hHunter : V15DegreeThreeHunterCertificateInput)
    (hMin : V15DegreeFourToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput)
    (c : GlobalLatticeClass)
    (hE : c.IsIntegralTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15IntegralAdmissiblePairs :=
  v15_integral_pair_mem_of_hunterCertificate
    hHunter hMin hTen hEleven v15_odlyzkoTable4DescriptionInput_closed
    v15_rank_one_classic_input c hE

/-- Theorem 1.2's global classic finiteness endpoint with the Table 4 analytic
input discharged by the internal contour proof. -/
theorem v15_classic_finite_closed :
    {c : GlobalLatticeClass |
      c.IsClassicTraceEuclidean (c.degree : ℝ)}.Finite :=
  v15_classic_finite_of_odlyzko_table4_description
    v15_odlyzkoTable4DescriptionInput_closed

/-- Theorem 1.3's global integral finiteness endpoint with both the Table 4
analytic input and the rank-one bridge discharged internally. -/
theorem v15_integral_finite_closed :
    {c : GlobalLatticeClass |
      c.IsIntegralTraceEuclidean (c.degree : ℝ)}.Finite :=
  v15_integral_finite_of_odlyzko_table4_description_source
    v15_odlyzkoTable4DescriptionInput_closed

/-- Corollary 1.6's finiteness endpoint for every supported power-mean
exponent, with the Table 4 analytic input discharged internally. -/
theorem v15_pnorm_finite_closed (p : V15PNormExponent) :
    {c : GlobalLatticeClass |
      ∃ P : GlobalLatticePresentation,
        (Quotient.mk _ P : GlobalLatticeClass) = c ∧
          P.IsV15PNormEuclidean p}.Finite :=
  v15_pnorm_finite_of_odlyzko_table4_description
    v15_odlyzkoTable4DescriptionInput_closed p

end

end TraceEuclidean
