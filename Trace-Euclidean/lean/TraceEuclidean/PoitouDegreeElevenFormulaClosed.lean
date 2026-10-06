import TraceEuclidean.PoitouCompactLimit
import TraceEuclidean.PoitouDegreeElevenClosed

/-!
# Unconditional Poitou formula in degree eleven

This module passes the unconditional compact-kernel discriminant inequality
to the expanding-cutoff limit.  It discharges the formerly external
`PoitouDegreeElevenFormulaInput` from the completed Dedekind-zeta contour,
endpoint, archimedean, and prime-ideal evaluations proved in the preceding
modules.
-/

namespace TraceEuclidean

noncomputable section

open Complex Filter MeasureTheory Set Topology

namespace PoitouKernel

open TraceEuclidean.PoitouDegreeEleven

private theorem log_four_mul_pi_identity :
    Real.log (4 * Real.pi) = 2 * Real.log 2 + Real.log Real.pi := by
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) Real.pi_ne_zero]
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
  norm_num

/-- Poitou's specialized degree-eleven explicit-formula inequality, with no
explicit-formula hypothesis left as an input. -/
theorem poitouDegreeElevenFormulaInput_closed :
    PoitouDegreeElevenFormulaInput := by
  intro K hreal hdegree
  letI : NumberField.IsTotallyReal K.1 := hreal
  let A : ℕ → ℝ := fun n ↦
    let R : ℝ := (n : ℝ) + 1
    let hR : 0 < R := by positivity
    let Q := poitouCompactExplicitFormulaKernel poitouY R (by
      norm_num [poitouY]) hR
    Real.eulerMascheroniConstant + Real.log Real.pi -
        Q.realGaussIntegral - (Q.phi 0 + Q.phi 1).re / 11
  have hA (n : ℕ) :
      A n ≤ Real.log (((|K.discriminant| : ℤ) : ℝ)) / 11 := by
    let R : ℝ := (n : ℝ) + 1
    let hR : 0 < R := by positivity
    let Q := poitouCompactExplicitFormulaKernel poitouY R (by
      norm_num [poitouY]) hR
    have hQ0 : Q.kernel 0 = 1 := by
      dsimp only [Q]
      exact poitouCompactExplicitFormulaKernel_zero
        (by norm_num [poitouY]) hR
    have hsource := Q.discriminant_log_lower_bound_totallyReal hQ0 K.1
    have hprime := Q.primeCorrection_nonneg K.1
    have hplacesNat :
        NumberField.InfinitePlace.nrRealPlaces K.1 = 11 := by
      rw [← NumberField.IsTotallyReal.finrank K.1]
      exact hdegree
    have hplaces :
        (NumberField.InfinitePlace.nrRealPlaces K.1 : ℝ) = 11 := by
      exact_mod_cast hplacesNat
    rw [hplaces] at hsource
    change
      11 * (Real.log Real.pi + Real.eulerMascheroniConstant -
          Q.realGaussIntegral) + Q.primeCorrection K.1 -
          (Q.phi 0 + Q.phi 1).re ≤
        Real.log (((|K.discriminant| : ℤ) : ℝ)) at hsource
    change
      Real.eulerMascheroniConstant + Real.log Real.pi -
          Q.realGaussIntegral - (Q.phi 0 + Q.phi 1).re / 11 ≤
        Real.log (((|K.discriminant| : ℤ) : ℝ)) / 11
    nlinarith
  have hGauss := poitouCompactRealGaussIntegral_tendsto
  have hEndpointComplex := poitouCompactPhi_zero_add_one_tendsto
    (y := poitouY) (by norm_num [poitouY])
  have hEndpoint : Tendsto
      (fun n : ℕ ↦
        let R : ℝ := (n : ℝ) + 1
        let hR : 0 < R := by positivity
        ((poitouCompactExplicitFormulaKernel poitouY R (by
          norm_num [poitouY]) hR).phi 0 +
          (poitouCompactExplicitFormulaKernel poitouY R (by
            norm_num [poitouY]) hR).phi 1).re)
      atTop (𝓝 (12 * Real.pi / (5 * Real.sqrt poitouY))) := by
    have h := (Complex.continuous_re.tendsto
      (((12 * Real.pi / (5 * Real.sqrt poitouY) : ℝ) : ℂ))).comp
        hEndpointComplex
    convert h using 1
    · funext n
      simp only [Function.comp_apply, Complex.add_re]
    · congr 1
  have hLimitRaw : Tendsto A atTop
      (𝓝 (Real.eulerMascheroniConstant + Real.log Real.pi -
        (poitouCorrectionIntegral poitouY - (2 * Real.log 2 + 1)) -
        (12 * Real.pi / (5 * Real.sqrt poitouY)) / 11)) := by
    have hconst : Tendsto
        (fun _ : ℕ ↦ Real.eulerMascheroniConstant + Real.log Real.pi)
        atTop (𝓝 (Real.eulerMascheroniConstant + Real.log Real.pi)) :=
      tendsto_const_nhds
    have h := (hconst.sub hGauss).sub (hEndpoint.div_const 11)
    convert h using 1
  have hLimit : Tendsto A atTop
      (𝓝 (Real.eulerMascheroniConstant + Real.log (4 * Real.pi) + 1 -
        poitouL1 poitouY -
        12 * Real.pi / (55 * Real.sqrt poitouY))) := by
    convert hLimitRaw using 1
    rw [poitouL1_eq_correctionIntegral, log_four_mul_pi_identity]
    ring
  exact le_of_tendsto' hLimit hA

/-- The optimized degree-eleven root-discriminant input, now discharged from
the closed Poitou formula and the already certified numerical series bound. -/
theorem degreeElevenRootDiscriminantInput_poitou_closed :
    DegreeElevenRootDiscriminantInput :=
  PoitouDegreeElevenClosed.degreeElevenRootDiscriminantInput_of_poitouFormula
    poitouDegreeElevenFormulaInput_closed

end PoitouKernel

end
end TraceEuclidean
