import TraceEuclidean.OdlyzkoEndpointContour
import TraceEuclidean.OdlyzkoNumerical
import TraceEuclidean.OdlyzkoVerticalLimit
import TraceEuclidean.AnalyticTableBridge
import TraceEuclidean.PNorm
import TraceEuclidean.RankOneIntegral

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
def odlyzkoPrimeLineIntegrand
    (K : Type*) [Field K] [NumberField K] (t : ℝ) : ℂ :=
  odlyzkoPhi ((2 : ℂ) + (t : ℂ) * I) *
    logDeriv (NumberField.dedekindZeta K)
      ((2 : ℂ) + (t : ℂ) * I)

/-- On the right line, the folded completed-zeta integrand is the sum of
twice the endpoint, archimedean, and ordinary-zeta contributions. -/
theorem odlyzkoCompletedVerticalPair_decomposition
    (K : Type*) [Field K] [NumberField K] (t : ℝ) :
    odlyzkoCompletedVerticalPair K t =
      2 * odlyzkoEndpointIntegrand
          ((2 : ℂ) + (t : ℂ) * I) +
        2 * odlyzkoArchimedeanIntegrand K
          ((2 : ℂ) + (t : ℂ) * I) +
        2 * odlyzkoPrimeLineIntegrand K t := by
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
  rw [odlyzkoCompletedVerticalPair_eq_two_mul]
  change
    2 * (odlyzkoPhi s *
        logDeriv
          (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s) =
      2 * odlyzkoEndpointIntegrand s +
        2 * odlyzkoArchimedeanIntegrand K s +
        2 * (odlyzkoPhi s *
          logDeriv (NumberField.dedekindZeta K) s)
  rw [DedekindZeta.LogDeriv.logDeriv_completedZetaPoleRemoved K hs]
  rw [odlyzkoEndpointIntegrand,
    odlyzkoEndpointPolynomial_logDeriv hs0 hs1]
  simp only [odlyzkoArchimedeanIntegrand]
  ring

/-- Twice the right-line archimedean contribution is absolutely
integrable. -/
theorem odlyzkoArchimedean_twice_right_integrable
    (K : Type*) [Field K] [NumberField K] :
    Integrable (fun t : ℝ ↦ 2 * odlyzkoArchimedeanIntegrand K
      ((2 : ℂ) + (t : ℂ) * I)) volume := by
  have h := odlyzkoArchimedeanIntegrand_vertical_integrable K
    (σ := (2 : ℝ)) (by norm_num) (by norm_num)
  have h' : Integrable (fun t : ℝ ↦
      odlyzkoArchimedeanIntegrand K
        ((2 : ℂ) + (t : ℂ) * I)) volume := by
    simpa using h
  exact h'.const_mul 2

/-- Twice the ordinary-zeta right-line contribution is absolutely
integrable.  This follows from the completed decomposition and the already
proved integrability of its other two summands. -/
theorem odlyzkoPrimeLine_twice_integrable
    (K : Type*) [Field K] [NumberField K] :
    Integrable (fun t : ℝ ↦ 2 * odlyzkoPrimeLineIntegrand K t)
      volume := by
  have hPair := odlyzkoCompletedVerticalPair_integrable K
  have hEndpoint := odlyzkoEndpoint_twice_right_integrable
  have hArch := odlyzkoArchimedean_twice_right_integrable K
  apply ((hPair.sub hEndpoint).sub hArch).congr
  filter_upwards with t
  change odlyzkoCompletedVerticalPair K t -
      2 * odlyzkoEndpointIntegrand ((2 : ℂ) + (t : ℂ) * I) -
      2 * odlyzkoArchimedeanIntegrand K
        ((2 : ℂ) + (t : ℂ) * I) =
    2 * odlyzkoPrimeLineIntegrand K t
  rw [odlyzkoCompletedVerticalPair_decomposition K t]
  ring

/-- The full folded vertical integral splits into the three source-normalized
pieces. -/
theorem odlyzkoCompletedVerticalPair_integral_decomposition
    (K : Type*) [Field K] [NumberField K] :
    (∫ t : ℝ, odlyzkoCompletedVerticalPair K t) =
      (∫ t : ℝ, 2 * odlyzkoEndpointIntegrand
          ((2 : ℂ) + (t : ℂ) * I)) +
        (∫ t : ℝ, 2 * odlyzkoArchimedeanIntegrand K
          ((2 : ℂ) + (t : ℂ) * I)) +
        ∫ t : ℝ, 2 * odlyzkoPrimeLineIntegrand K t := by
  have hEndpoint := odlyzkoEndpoint_twice_right_integrable
  have hArch := odlyzkoArchimedean_twice_right_integrable K
  have hPrime := odlyzkoPrimeLine_twice_integrable K
  calc
    (∫ t : ℝ, odlyzkoCompletedVerticalPair K t) =
        ∫ t : ℝ,
          (2 * odlyzkoEndpointIntegrand
              ((2 : ℂ) + (t : ℂ) * I) +
            2 * odlyzkoArchimedeanIntegrand K
              ((2 : ℂ) + (t : ℂ) * I)) +
            2 * odlyzkoPrimeLineIntegrand K t := by
      apply integral_congr_ae
      filter_upwards with t
      rw [odlyzkoCompletedVerticalPair_decomposition K t]
    _ = _ := by
      let f : ℝ → ℂ := fun t ↦ 2 * odlyzkoEndpointIntegrand
        ((2 : ℂ) + (t : ℂ) * I)
      let g : ℝ → ℂ := fun t ↦ 2 * odlyzkoArchimedeanIntegrand K
        ((2 : ℂ) + (t : ℂ) * I)
      let p : ℝ → ℂ := fun t ↦ 2 * odlyzkoPrimeLineIntegrand K t
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
theorem odlyzkoPrimeLine_normalized_integral
    (K : Type*) [Field K] [NumberField K] :
    (1 / (2 * Real.pi) : ℂ) *
        (∫ t : ℝ, 2 * odlyzkoPrimeLineIntegrand K t) =
      -(odlyzkoPrimeCorrection K : ℂ) := by
  have hPrime :=
    odlyzkoPhi_mul_logDeriv_dedekindZeta_integral K 2 (by norm_num)
  change (1 / (2 * Real.pi) : ℂ) *
      (∫ t : ℝ, 2 *
        (odlyzkoPhi ((2 : ℂ) + (t : ℂ) * I) *
          logDeriv (NumberField.dedekindZeta K)
            ((2 : ℂ) + (t : ℂ) * I))) = _
  rw [integral_const_mul]
  have hPrime' :
      (∫ t : ℝ,
        odlyzkoPhi ((2 : ℂ) + (t : ℂ) * I) *
          logDeriv (NumberField.dedekindZeta K)
            ((2 : ℂ) + (t : ℂ) * I)) =
        -((Real.pi * odlyzkoPrimeCorrection K : ℝ) : ℂ) := by
    simpa using hPrime
  rw [hPrime']
  have hPi : (Real.pi : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr Real.pi_pos.ne'
  push_cast
  field_simp [hPi]

/-- After `1/(2π)` normalization, the real part of the two archimedean
copies is the exact discriminant-and-signature expression. -/
theorem odlyzkoArchimedean_normalized_integral_re
    (K : Type*) [Field K] [NumberField K] :
    ((1 / (2 * Real.pi) : ℂ) *
        (∫ t : ℝ, 2 * odlyzkoArchimedeanIntegrand K
          ((2 : ℂ) + (t : ℂ) * I))).re =
      Real.log (((|NumberField.discr K| : ℤ) : ℝ)) -
        (NumberField.InfinitePlace.nrRealPlaces K : ℝ) *
          odlyzkoArchLogA -
        2 * (NumberField.InfinitePlace.nrComplexPlaces K : ℝ) *
          odlyzkoArchLogB := by
  have hArch := odlyzkoArchimedean_right_twice_re_integral K
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
theorem odlyzkoCompletedVerticalPair_normalized_integral_re
    (K : Type*) [Field K] [NumberField K] :
    ((1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ, odlyzkoCompletedVerticalPair K t).re =
      32 / 3 +
        (Real.log (((|NumberField.discr K| : ℤ) : ℝ)) -
          (NumberField.InfinitePlace.nrRealPlaces K : ℝ) *
            odlyzkoArchLogA -
          2 * (NumberField.InfinitePlace.nrComplexPlaces K : ℝ) *
            odlyzkoArchLogB) -
        odlyzkoPrimeCorrection K := by
  rw [odlyzkoCompletedVerticalPair_integral_decomposition K]
  simp only [mul_add, Complex.add_re]
  rw [odlyzkoEndpoint_normalized_integral,
    odlyzkoArchimedean_normalized_integral_re K,
    odlyzkoPrimeLine_normalized_integral K]
  norm_num
  ring

/-- The completed-zeta contour and positivity of its finite zero sums imply
the exact Odlyzko logarithmic discriminant lower bound. -/
theorem odlyzko_discriminant_log_lower_bound
    (K : Type*) [Field K] [NumberField K] :
    (NumberField.InfinitePlace.nrRealPlaces K : ℝ) *
          odlyzkoArchLogA +
        2 * (NumberField.InfinitePlace.nrComplexPlaces K : ℝ) *
          odlyzkoArchLogB +
        odlyzkoPrimeCorrection K - 32 / 3 ≤
      Real.log (((|NumberField.discr K| : ℤ) : ℝ)) := by
  have hNonneg := odlyzkoCompletedVerticalPair_integral_re_nonneg K
  rw [odlyzkoCompletedVerticalPair_normalized_integral_re K] at hNonneg
  linarith

/-- The contour lower bound and any certified strict bounds for the two
archimedean constants imply the exact-error Table 4 interface. -/
theorem odlyzkoTable4ExplicitCorrectionInput_of_contour
    (hAB : OdlyzkoABIntegralCertificate) :
    OdlyzkoTable4ExplicitCorrectionInput := by
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
      Real.log (36347 / 1000 : ℝ) < odlyzkoArchLogA := hAB.2.1
  have hB :
      Real.log (16593 / 1000 : ℝ) < odlyzkoArchLogB := hAB.2.2
  have hStrict :
      (r : ℝ) * Real.log (36347 / 1000 : ℝ) +
          (c : ℝ) * Real.log (16593 / 1000 : ℝ) <
        (r : ℝ) * odlyzkoArchLogA +
          (c : ℝ) * odlyzkoArchLogB := by
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
      (r : ℝ) * odlyzkoArchLogA +
          (c : ℝ) * odlyzkoArchLogB +
          odlyzkoPrimeCorrection K.1 - 32 / 3 ≤
        Real.log (((|K.discriminant| : ℤ) : ℝ)) := by
    simpa [r, c, NumberFieldCode.discriminant] using
      odlyzko_discriminant_log_lower_bound K.1
  have hLogLower :
      (r : ℝ) * Real.log (36347 / 1000 : ℝ) +
          (c : ℝ) * Real.log (16593 / 1000 : ℝ) +
          (odlyzkoPrimeCorrection K.1 - (32 / 3 : ℝ)) <
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
          (odlyzkoPrimeCorrection K.1 - (32 / 3 : ℝ))) =
        (36347 / 1000 : ℝ) ^ r *
          (16593 / 1000 : ℝ) ^ c *
          Real.exp (odlyzkoPrimeCorrection K.1 - (32 / 3 : ℝ)) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul,
      Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 36347 / 1000),
      Real.exp_log (by norm_num : (0 : ℝ) < 16593 / 1000)]
  rw [hTarget] at hExp
  exact hExp

/-- Fully internal construction of the exact-error Table 4 input. -/
theorem odlyzkoTable4ExplicitCorrectionInput_closed :
    OdlyzkoTable4ExplicitCorrectionInput :=
  odlyzkoTable4ExplicitCorrectionInput_of_contour
    OdlyzkoNumerical.abIntegralCertificate

/-- The rounded Table 4 description used by the downstream  theorems now
follows without an analytic literature-input hypothesis. -/
theorem odlyzkoTable4DescriptionInput_closed :
    OdlyzkoTable4DescriptionInput :=
  odlyzkoTable4DescriptionInput_of_explicitCorrection
    odlyzkoTable4ExplicitCorrectionInput_closed

/-- The Section 4 discriminant input after the internally proved Table 4
part is combined with the three cited small-degree estimates. -/
theorem sectionFourDiscriminantInput_of_smallDegreeLiterature
    (hMin : DegreeTwoToNineMinimumInput)
    (hTen : DegreeTenRootDiscriminantInput)
    (hEleven : DegreeElevenRootDiscriminantInput) :
    SectionFourDiscriminantInput :=
  sectionFourDiscriminantInput_of_literature hMin hTen hEleven
    odlyzkoTable4DescriptionInput_closed

/-- The Section 4 discriminant input with both the analytic Table 4 range and
the quadratic minimum discharged internally.  The remaining literature inputs
cover degrees three through eleven. -/
theorem sectionFourDiscriminantInput_of_reduced_smallDegreeLiterature
    (hMin : DegreeThreeToNineMinimumInput)
    (hTen : DegreeTenRootDiscriminantInput)
    (hEleven : DegreeElevenRootDiscriminantInput) :
    SectionFourDiscriminantInput :=
  sectionFourDiscriminantInput_of_reduced_literature
    hMin hTen hEleven odlyzkoTable4DescriptionInput_closed

/-- Membership in the manuscript's 24-row classic table after reducing the
external discriminant input to degrees three through eleven. -/
theorem classic_pair_mem_of_reduced_smallDegreeLiterature
    (hMin : DegreeThreeToNineMinimumInput)
    (hTen : DegreeTenRootDiscriminantInput)
    (hEleven : DegreeElevenRootDiscriminantInput)
    (c : GlobalLatticeClass)
    (hE : c.IsClassicTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ classicAdmissiblePairs :=
  classic_pair_mem_of_reduced_literature
    hMin hTen hEleven odlyzkoTable4DescriptionInput_closed c hE

/-- Membership in the manuscript's 63-row integral table after reducing the
external discriminant input to degrees three through eleven. -/
theorem integral_pair_mem_of_reduced_smallDegreeLiterature
    (hMin : DegreeThreeToNineMinimumInput)
    (hTen : DegreeTenRootDiscriminantInput)
    (hEleven : DegreeElevenRootDiscriminantInput)
    (c : GlobalLatticeClass)
    (hE : c.IsIntegralTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ integralAdmissiblePairs :=
  integral_pair_mem_of_reduced_literature
    hMin hTen hEleven odlyzkoTable4DescriptionInput_closed
    rank_one_classic_input c hE

/-- The Section 4 discriminant input after replacing the cubic exact-minimum
table row by the normalized Hunter certificate. -/
theorem sectionFourDiscriminantInput_of_hunterCertificate_closed
    (hHunter : DegreeThreeHunterCertificateInput)
    (hMin : DegreeFourToNineMinimumInput)
    (hTen : DegreeTenRootDiscriminantInput)
    (hEleven : DegreeElevenRootDiscriminantInput) :
    SectionFourDiscriminantInput :=
  sectionFourDiscriminantInput_of_hunterCertificate
    hHunter hMin hTen hEleven odlyzkoTable4DescriptionInput_closed

/-- Membership in the classic table from the cubic Hunter certificate and
the remaining degree-four to degree-eleven source inputs. -/
theorem classic_pair_mem_of_hunterCertificate_closed
    (hHunter : DegreeThreeHunterCertificateInput)
    (hMin : DegreeFourToNineMinimumInput)
    (hTen : DegreeTenRootDiscriminantInput)
    (hEleven : DegreeElevenRootDiscriminantInput)
    (c : GlobalLatticeClass)
    (hE : c.IsClassicTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ classicAdmissiblePairs :=
  classic_pair_mem_of_hunterCertificate
    hHunter hMin hTen hEleven odlyzkoTable4DescriptionInput_closed c hE

/-- Membership in the integral table from the cubic Hunter certificate and
the remaining degree-four to degree-eleven source inputs. -/
theorem integral_pair_mem_of_hunterCertificate_closed
    (hHunter : DegreeThreeHunterCertificateInput)
    (hMin : DegreeFourToNineMinimumInput)
    (hTen : DegreeTenRootDiscriminantInput)
    (hEleven : DegreeElevenRootDiscriminantInput)
    (c : GlobalLatticeClass)
    (hE : c.IsIntegralTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ integralAdmissiblePairs :=
  integral_pair_mem_of_hunterCertificate
    hHunter hMin hTen hEleven odlyzkoTable4DescriptionInput_closed
    rank_one_classic_input c hE

/-- Theorem 1.2's global classic finiteness endpoint with the Table 4 analytic
input discharged by the internal contour proof. -/
theorem classic_finite_closed :
    {c : GlobalLatticeClass |
      c.IsClassicTraceEuclidean (c.degree : ℝ)}.Finite :=
  classic_finite_of_odlyzko_table4_description
    odlyzkoTable4DescriptionInput_closed

/-- Theorem 1.3's global integral finiteness endpoint with both the Table 4
analytic input and the rank-one bridge discharged internally. -/
theorem integral_finite_closed :
    {c : GlobalLatticeClass |
      c.IsIntegralTraceEuclidean (c.degree : ℝ)}.Finite :=
  integral_finite_of_odlyzko_table4_description_source
    odlyzkoTable4DescriptionInput_closed

/-- Corollary 1.6's finiteness endpoint for every supported power-mean
exponent, with the Table 4 analytic input discharged internally. -/
theorem pnorm_finite_closed (p : PNormExponent) :
    {c : GlobalLatticeClass |
      ∃ P : GlobalLatticePresentation,
        (Quotient.mk _ P : GlobalLatticeClass) = c ∧
          P.IsPNormEuclidean p}.Finite :=
  pnorm_finite_of_odlyzko_table4_description
    odlyzkoTable4DescriptionInput_closed p

end

end TraceEuclidean
