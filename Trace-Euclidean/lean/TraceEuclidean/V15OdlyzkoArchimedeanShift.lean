import TraceEuclidean.Analytic.DigammaStirling
import TraceEuclidean.Analytic.VerticalLineShift
import TraceEuclidean.V15OdlyzkoArchimedeanBridge
import TraceEuclidean.V15OdlyzkoFourthDecayCriterion
import DedekindZeta.ArchimedeanLogDeriv
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Shifting the Odlyzko archimedean integral to the critical line

This file supplies the analytic estimates needed to move the right-line
archimedean integral to `Re(s) = 1 / 2`.  The first step is a uniform
logarithmic growth bound for the digamma function on the relevant strip.
-/

namespace TraceEuclidean

noncomputable section

open Complex Filter MeasureTheory Set Topology

variable {K : Type*} [Field K] [NumberField K]

/-- The digamma function is holomorphic on the positive half-plane. -/
lemma v15_digamma_differentiableAt_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.digamma s := by
  have hzero : ∀ m : ℕ, s ≠ -(m : ℂ) := by
    intro m h
    rw [h] at hs
    simp only [Complex.neg_re, Complex.natCast_re] at hs
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hopen : IsOpen {w : ℂ | 0 < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hGamma : AnalyticAt ℂ Complex.Gamma s := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [hopen.mem_nhds hs] with w hw
    refine Complex.differentiableAt_Gamma w fun m ↦ ?_
    intro h
    rw [h] at hw
    simp only [Complex.neg_re, Complex.natCast_re] at hw
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hGammaNe : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hzero
  have hDigamma : AnalyticAt ℂ Complex.digamma s := by
    have hDeriv : AnalyticAt ℂ (deriv Complex.Gamma) s := hGamma.deriv
    have hQuot := hDeriv.div hGamma hGammaNe
    exact hQuot.congr (by
      filter_upwards with w
      rw [Complex.digamma_def, logDeriv_apply]
      rfl)
  exact hDigamma.differentiableAt

/-- Coarse uniform digamma growth on the strip used to shift the
archimedean term. -/
theorem exists_v15_digamma_growth_strip :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 2 →
      ‖Complex.digamma s‖ ≤ C * Real.log (2 + |s.im|) := by
  have hK : IsCompact
      (Complex.reProdIm (Set.Icc (1 / 4 : ℝ) 2)
        (Set.Icc (-(1 / 2) : ℝ) (1 / 2))) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hcontK : ContinuousOn Complex.digamma
      (Complex.reProdIm (Set.Icc (1 / 4 : ℝ) 2)
        (Set.Icc (-(1 / 2) : ℝ) (1 / 2))) := by
    intro s hs
    have hsre : 1 / 4 ≤ s.re := (Complex.mem_reProdIm.mp hs).1.1
    exact (v15_digamma_differentiableAt_of_re_pos (by linarith)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcontK
  have hM0 : (0 : ℝ) ≤ M := by
    have h := hM (1 / 2 : ℂ) (by
      rw [Complex.mem_reProdIm]
      constructor
      · simp only [Complex.div_ofNat_re, Complex.one_re]
        norm_num
      · simp only [Complex.div_ofNat_im, Complex.one_im]
        norm_num)
    exact le_trans (norm_nonneg _) h
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set K₀ : ℝ := 14 + Real.pi + Real.log 4 with hK₀
  have hK₀0 : (0 : ℝ) < K₀ := by positivity
  refine ⟨max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1,
    by positivity, fun s hre1 hre2 ↦ ?_⟩
  have hlogmono : Real.log 2 ≤ Real.log (2 + |s.im|) := by
    apply Real.log_le_log (by norm_num)
    linarith [abs_nonneg s.im]
  have hlogpos : (0 : ℝ) < Real.log (2 + |s.im|) :=
    lt_of_lt_of_le hlog2 hlogmono
  rcases le_or_gt |s.im| (1 / 2) with him | him
  · have hsK : s ∈ Complex.reProdIm (Set.Icc (1 / 4 : ℝ) 2)
        (Set.Icc (-(1 / 2) : ℝ) (1 / 2)) := by
      rw [Complex.mem_reProdIm]
      refine ⟨⟨hre1, hre2⟩, ?_⟩
      rw [Set.mem_Icc]
      constructor
      · linarith [neg_abs_le s.im]
      · linarith [le_abs_self s.im]
    calc
      ‖Complex.digamma s‖ ≤ M := hM s hsK
      _ = (M / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ (max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1) *
          Real.log (2 + |s.im|) := by
        apply mul_le_mul ?_ hlogmono hlog2.le (by positivity)
        calc
          M / Real.log 2 ≤ max (M / Real.log 2) (1 + K₀ / Real.log 2) :=
            le_max_left _ _
          _ ≤ max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1 := by linarith

  · have hsre0 : (0 : ℝ) < s.re := by linarith
    have hst := Zeta23.StirlingVert.digamma_stirling
      (w := s) hsre0 (by linarith)
    have hsnormLo : (1 / 4 : ℝ) ≤ ‖s‖ :=
      le_trans hre1 (le_trans (le_abs_self _) (Complex.abs_re_le_norm s))
    have hsnorm0 : (0 : ℝ) < ‖s‖ := by linarith
    have hs0 : s ≠ 0 := by
      intro h
      rw [h, norm_zero] at hsnorm0
      exact lt_irrefl 0 hsnorm0
    have hsnormHi : ‖s‖ ≤ 2 + |s.im| := by
      calc
        ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ ≤ 2 + |s.im| := by
          have : |s.re| ≤ 2 := by
            rw [abs_le]
            constructor <;> linarith
          linarith
    have hlogS : ‖Complex.log s‖ ≤ |Real.log ‖s‖| + Real.pi := by
      calc
        ‖Complex.log s‖ ≤ |(Complex.log s).re| + |(Complex.log s).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        _ ≤ |Real.log ‖s‖| + Real.pi := by
          rw [Complex.log_re, Complex.log_im]
          linarith [Complex.abs_arg_le_pi s, abs_nonneg (Complex.arg s)]
    have hlogAbs : |Real.log ‖s‖| ≤
        Real.log 4 + Real.log (2 + |s.im|) := by
      rcases le_or_gt (Real.log ‖s‖) 0 with hneg | hpos
      · have h1 : Real.log (1 / 4 : ℝ) ≤ Real.log ‖s‖ :=
          Real.log_le_log (by norm_num) hsnormLo
        have h2 : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
          rw [show (1 / 4 : ℝ) = 4⁻¹ by norm_num, Real.log_inv]
        rw [abs_of_nonpos hneg]
        have h3 : (0 : ℝ) ≤ Real.log (2 + |s.im|) := by
          apply Real.log_nonneg
          linarith [abs_nonneg s.im]
        linarith
      · rw [abs_of_pos hpos]
        have h1 : Real.log ‖s‖ ≤ Real.log (2 + |s.im|) :=
          Real.log_le_log hsnorm0 hsnormHi
        have h2 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
        linarith
    have hinvS : ‖(1 / 2 : ℂ) / s‖ ≤ 2 := by
      rw [norm_div]
      have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
        rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
      rw [hhalf, div_le_iff₀ hsnorm0]
      linarith
    have him2 : 3 / s.im ^ 2 ≤ 12 := by
      have h1 : (1 / 4 : ℝ) ≤ s.im ^ 2 := by
        have h2 : (1 / 2 : ℝ) ≤ |s.im| := him.le
        nlinarith [abs_nonneg s.im, sq_abs s.im]
      rw [div_le_iff₀ (by nlinarith)]
      nlinarith
    have htot : ‖Complex.digamma s‖ ≤ Real.log (2 + |s.im|) + K₀ := by
      have h1 : ‖Complex.digamma s‖ ≤
          ‖Complex.digamma s - Complex.log s + (1 / 2 : ℂ) / s‖ +
            ‖Complex.log s‖ + ‖(1 / 2 : ℂ) / s‖ := by
        have h2 : Complex.digamma s =
            (Complex.digamma s - Complex.log s + (1 / 2 : ℂ) / s) +
              Complex.log s - (1 / 2 : ℂ) / s := by ring
        calc
          ‖Complex.digamma s‖ =
              ‖(Complex.digamma s - Complex.log s + (1 / 2 : ℂ) / s) +
                Complex.log s - (1 / 2 : ℂ) / s‖ := by rw [← h2]
          _ ≤ ‖(Complex.digamma s - Complex.log s + (1 / 2 : ℂ) / s) +
                Complex.log s‖ + ‖(1 / 2 : ℂ) / s‖ := norm_sub_le _ _
          _ ≤ ‖Complex.digamma s - Complex.log s + (1 / 2 : ℂ) / s‖ +
                ‖Complex.log s‖ + ‖(1 / 2 : ℂ) / s‖ := by
            linarith [norm_add_le
              (Complex.digamma s - Complex.log s + (1 / 2 : ℂ) / s)
              (Complex.log s)]
      rw [hK₀]
      calc
        ‖Complex.digamma s‖ ≤
            ‖Complex.digamma s - Complex.log s + (1 / 2 : ℂ) / s‖ +
              ‖Complex.log s‖ + ‖(1 / 2 : ℂ) / s‖ := h1
        _ ≤ 3 / s.im ^ 2 + (|Real.log ‖s‖| + Real.pi) + 2 := by
          linarith [hst, hlogS, hinvS]
        _ ≤ 12 + ((Real.log 4 + Real.log (2 + |s.im|)) + Real.pi) + 2 := by
          linarith [him2, hlogAbs]
        _ = Real.log (2 + |s.im|) + (14 + Real.pi + Real.log 4) := by ring
    calc
      ‖Complex.digamma s‖ ≤ Real.log (2 + |s.im|) + K₀ := htot
      _ ≤ Real.log (2 + |s.im|) +
          (K₀ / Real.log 2) * Real.log (2 + |s.im|) := by
        have h3 : K₀ / Real.log 2 * Real.log 2 ≤
            K₀ / Real.log 2 * Real.log (2 + |s.im|) :=
          mul_le_mul_of_nonneg_left hlogmono (by positivity)
        have h4 : K₀ / Real.log 2 * Real.log 2 = K₀ := by field_simp
        linarith
      _ = (1 + K₀ / Real.log 2) * Real.log (2 + |s.im|) := by ring
      _ ≤ (max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1) *
          Real.log (2 + |s.im|) := by
        apply mul_le_mul_of_nonneg_right ?_ hlogpos.le
        calc
          1 + K₀ / Real.log 2 ≤ max (M / Real.log 2) (1 + K₀ / Real.log 2) :=
            le_max_right _ _
          _ ≤ max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1 := by linarith
/-- The logarithmic derivative of the archimedean factor is holomorphic on
the positive half-plane. -/
lemma v15_logDeriv_ZInfty_differentiableAt_of_re_pos
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (logDeriv (DedekindZeta.ZInfty K)) s := by
  let g : ℂ → ℂ := fun u ↦
    Complex.log (((|NumberField.discr K| : ℤ) : ℂ)) / 2 +
      (NumberField.InfinitePlace.nrRealPlaces K : ℂ) *
        (-Complex.log (Real.pi : ℂ) / 2 + Complex.digamma (u / 2) / 2) +
      (NumberField.InfinitePlace.nrComplexPlaces K : ℂ) *
        (-Complex.log (2 * (Real.pi : ℂ)) + Complex.digamma u)
  have hhalf : 0 < (s / 2).re := by simp; linarith
  have hdiffHalf : DifferentiableAt ℂ (fun u : ℂ ↦ Complex.digamma (u / 2)) s :=
    (v15_digamma_differentiableAt_of_re_pos hhalf).comp s
      (differentiableAt_id.div_const 2)
  have hdiffS : DifferentiableAt ℂ Complex.digamma s :=
    v15_digamma_differentiableAt_of_re_pos hs
  have hdiff : DifferentiableAt ℂ g s := by
    have hA : DifferentiableAt ℂ
        (fun _ : ℂ ↦ Complex.log (((|NumberField.discr K| : ℤ) : ℂ)) / 2) s :=
      differentiableAt_const _
    have hR : DifferentiableAt ℂ
        (fun u : ℂ ↦ (NumberField.InfinitePlace.nrRealPlaces K : ℂ) *
          (-Complex.log (Real.pi : ℂ) / 2 + Complex.digamma (u / 2) / 2)) s :=
      (differentiableAt_const _).mul
        ((differentiableAt_const _).add (hdiffHalf.div_const 2))
    have hC : DifferentiableAt ℂ
        (fun u : ℂ ↦ (NumberField.InfinitePlace.nrComplexPlaces K : ℂ) *
          (-Complex.log (2 * (Real.pi : ℂ)) + Complex.digamma u)) s :=
      (differentiableAt_const _).mul ((differentiableAt_const _).add hdiffS)
    exact (hA.add hR).add hC
  have hopen : IsOpen {u : ℂ | 0 < u.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have heq : logDeriv (DedekindZeta.ZInfty K) =ᶠ[𝓝 s] g := by
    filter_upwards [hopen.mem_nhds hs] with u hu
    exact DedekindZeta.ArchimedeanLogDeriv.logDeriv_ZInfty K hu
  exact hdiff.congr_of_eventuallyEq heq

/-- The archimedean logarithmic derivative has at most logarithmic growth on
the strip from the critical line to the absolute-convergence line. -/
theorem exists_v15_logDeriv_ZInfty_growth_strip
    (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 →
      ‖logDeriv (DedekindZeta.ZInfty K) s‖ ≤
        C * Real.log (2 + |s.im|) := by
  obtain ⟨Cψ, hCψ, hψ⟩ := exists_v15_digamma_growth_strip
  let A : ℝ :=
    ‖Complex.log (((|NumberField.discr K| : ℤ) : ℂ)) / 2‖
  let B : ℝ := ‖-Complex.log (Real.pi : ℂ) / 2‖
  let E : ℝ := ‖-Complex.log (2 * (Real.pi : ℂ))‖
  let r : ℝ := NumberField.InfinitePlace.nrRealPlaces K
  let c : ℝ := NumberField.InfinitePlace.nrComplexPlaces K
  let C : ℝ := 1 + A / Real.log 2 +
    r * (B / Real.log 2 + Cψ / 2) +
    c * (E / Real.log 2 + Cψ)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0 ≤ A := norm_nonneg _
  have hB : 0 ≤ B := norm_nonneg _
  have hE : 0 ≤ E := norm_nonneg _
  have hr : 0 ≤ r := by
    dsimp only [r]
    positivity
  have hc : 0 ≤ c := by
    dsimp only [c]
    positivity
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, fun s hs0 hs1 ↦ ?_⟩
  have hspos : 0 < s.re := by linarith
  have hhalfRe0 : 1 / 4 ≤ (s / 2).re := by simp; linarith
  have hhalfRe1 : (s / 2).re ≤ 2 := by simp; linarith
  have hψhalf := hψ (s / 2) hhalfRe0 hhalfRe1
  have hψs := hψ s (by linarith) hs1
  have himHalf : |(s / 2).im| ≤ |s.im| := by
    rw [Complex.div_ofNat_im]
    rw [abs_div]
    norm_num
  have hlogMono : Real.log (2 + |(s / 2).im|) ≤
      Real.log (2 + |s.im|) := by
    apply Real.log_le_log
    · linarith [abs_nonneg (s / 2).im]
    · linarith
  have hlogLower : Real.log 2 ≤ Real.log (2 + |s.im|) := by
    apply Real.log_le_log (by norm_num)
    linarith [abs_nonneg s.im]
  have hlogNonneg : 0 ≤ Real.log (2 + |s.im|) :=
    hlog2.le.trans hlogLower
  have hψhalf' : ‖Complex.digamma (s / 2)‖ ≤
      Cψ * Real.log (2 + |s.im|) := by
    exact hψhalf.trans (mul_le_mul_of_nonneg_left hlogMono hCψ.le)
  rw [DedekindZeta.ArchimedeanLogDeriv.logDeriv_ZInfty K hspos]
  have hNorm :
      ‖Complex.log (((|NumberField.discr K| : ℤ) : ℂ)) / 2 +
          (NumberField.InfinitePlace.nrRealPlaces K : ℂ) *
            (-Complex.log (Real.pi : ℂ) / 2 +
              Complex.digamma (s / 2) / 2) +
          (NumberField.InfinitePlace.nrComplexPlaces K : ℂ) *
            (-Complex.log (2 * (Real.pi : ℂ)) + Complex.digamma s)‖ ≤
        A + r * (B + ‖Complex.digamma (s / 2)‖ / 2) +
          c * (E + ‖Complex.digamma s‖) := by
    calc
      _ ≤ ‖Complex.log (((|NumberField.discr K| : ℤ) : ℂ)) / 2‖ +
          ‖(NumberField.InfinitePlace.nrRealPlaces K : ℂ) *
            (-Complex.log (Real.pi : ℂ) / 2 +
              Complex.digamma (s / 2) / 2)‖ +
          ‖(NumberField.InfinitePlace.nrComplexPlaces K : ℂ) *
            (-Complex.log (2 * (Real.pi : ℂ)) + Complex.digamma s)‖ := by
        linarith [norm_add_le
          (Complex.log (((|NumberField.discr K| : ℤ) : ℂ)) / 2 +
            (NumberField.InfinitePlace.nrRealPlaces K : ℂ) *
              (-Complex.log (Real.pi : ℂ) / 2 +
                Complex.digamma (s / 2) / 2))
          ((NumberField.InfinitePlace.nrComplexPlaces K : ℂ) *
            (-Complex.log (2 * (Real.pi : ℂ)) + Complex.digamma s)),
          norm_add_le
            (Complex.log (((|NumberField.discr K| : ℤ) : ℂ)) / 2)
            ((NumberField.InfinitePlace.nrRealPlaces K : ℂ) *
              (-Complex.log (Real.pi : ℂ) / 2 +
                Complex.digamma (s / 2) / 2))]
      _ ≤ A + r * (B + ‖Complex.digamma (s / 2)‖ / 2) +
          c * (E + ‖Complex.digamma s‖) := by
        dsimp only [A, B, E, r, c]
        simp only [norm_mul, Complex.norm_natCast]
        gcongr
        · calc
            ‖-Complex.log (Real.pi : ℂ) / 2 +
                Complex.digamma (s / 2) / 2‖ ≤
                ‖-Complex.log (Real.pi : ℂ) / 2‖ +
                  ‖Complex.digamma (s / 2) / 2‖ := norm_add_le _ _
            _ = ‖-Complex.log (Real.pi : ℂ) / 2‖ +
                ‖Complex.digamma (s / 2)‖ / 2 := by
              rw [norm_div]
              norm_num
        · exact norm_add_le _ _
  calc
    _ ≤ A + r * (B + ‖Complex.digamma (s / 2)‖ / 2) +
        c * (E + ‖Complex.digamma s‖) := hNorm
    _ ≤ A + r * (B + (Cψ * Real.log (2 + |s.im|)) / 2) +
        c * (E + Cψ * Real.log (2 + |s.im|)) := by
      gcongr
    _ ≤ (A / Real.log 2 +
          r * (B / Real.log 2 + Cψ / 2) +
          c * (E / Real.log 2 + Cψ)) *
        Real.log (2 + |s.im|) := by
      have hAlog : A ≤ (A / Real.log 2) * Real.log (2 + |s.im|) := by
        calc
          A = (A / Real.log 2) * Real.log 2 := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hlogLower (div_nonneg hA hlog2.le)
      have hBlog : B ≤ (B / Real.log 2) * Real.log (2 + |s.im|) := by
        calc
          B = (B / Real.log 2) * Real.log 2 := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hlogLower (div_nonneg hB hlog2.le)
      have hElog : E ≤ (E / Real.log 2) * Real.log (2 + |s.im|) := by
        calc
          E = (E / Real.log 2) * Real.log 2 := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hlogLower (div_nonneg hE hlog2.le)
      nlinarith
    _ ≤ C * Real.log (2 + |s.im|) := by
      dsimp only [C]
      nlinarith

/-- The archimedean part of the completed-zeta contour integrand. -/
def v15OdlyzkoArchimedeanIntegrand
    (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  v15OdlyzkoPhi s * logDeriv (DedekindZeta.ZInfty K) s

/-- Fourth-power transform decay absorbs the logarithmic growth of the
archimedean logarithmic derivative uniformly on the shift strip. -/
theorem exists_v15OdlyzkoArchimedean_strip_majorant
    (K : Type*) [Field K] [NumberField K] :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 →
      ‖v15OdlyzkoArchimedeanIntegrand K s‖ ≤
        M / (1 + |s.im|) ^ 2 := by
  obtain ⟨D, hD, hPhi⟩ := v15OdlyzkoPhi_exists_wideFourthPowerBound
  obtain ⟨C, hC, hLog⟩ := exists_v15_logDeriv_ZInfty_growth_strip K
  refine ⟨D * C, mul_nonneg hD hC.le, fun s hs0 hs1 ↦ ?_⟩
  let u : ℝ := 1 + |s.im|
  have hu : 0 < u := by dsimp only [u]; positivity
  have hPhi' : ‖v15OdlyzkoPhi s‖ ≤ D / u ^ 4 := by
    simpa only [u] using hPhi s (by linarith) hs1
  have hLog' : ‖logDeriv (DedekindZeta.ZInfty K) s‖ ≤
      C * Real.log (2 + |s.im|) := hLog s hs0 hs1
  have hLogPow : Real.log (2 + |s.im|) ≤ u ^ 2 := by
    have hbase := Real.log_le_sub_one_of_pos
      (show 0 < 2 + |s.im| by positivity)
    have huOne : 1 ≤ u := by dsimp only [u]; linarith [abs_nonneg s.im]
    have huSq : u ≤ u ^ 2 := by nlinarith
    dsimp only [u] at hbase ⊢
    linarith
  rw [v15OdlyzkoArchimedeanIntegrand, norm_mul]
  calc
    ‖v15OdlyzkoPhi s‖ * ‖logDeriv (DedekindZeta.ZInfty K) s‖ ≤
        (D / u ^ 4) * (C * Real.log (2 + |s.im|)) :=
      mul_le_mul hPhi' hLog' (norm_nonneg _)
        (div_nonneg hD (pow_nonneg hu.le 4))
    _ ≤ (D / u ^ 4) * (C * u ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hLogPow hC.le)
        (div_nonneg hD (pow_nonneg hu.le 4))
    _ = D * C / u ^ 2 := by field_simp

/-- The archimedean contour integrand is holomorphic throughout the strip
between `Re(s) = 1 / 2` and `Re(s) = 2`. -/
lemma v15OdlyzkoArchimedeanIntegrand_differentiableAt
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (v15OdlyzkoArchimedeanIntegrand K) s := by
  exact v15OdlyzkoPhi_differentiable.differentiableAt.mul
    (v15_logDeriv_ZInfty_differentiableAt_of_re_pos K hs)

/-- The archimedean contour integrand is integrable on each vertical line in
the shift strip. -/
theorem v15OdlyzkoArchimedeanIntegrand_vertical_integrable
    (K : Type*) [Field K] [NumberField K] {σ : ℝ}
    (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 2) :
    Integrable (fun t : ℝ ↦
      v15OdlyzkoArchimedeanIntegrand K (σ + t * I)) volume := by
  obtain ⟨M, -, hMajorant⟩ :=
    exists_v15OdlyzkoArchimedean_strip_majorant K
  apply Analytic.integrable_line
  · intro t
    apply v15OdlyzkoArchimedeanIntegrand_differentiableAt
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, mul_one, sub_self, add_zero]
    linarith
  · exact v15OdlyzkoCriticalMajorant_two_integrable M
  · intro t
    have h := hMajorant ((σ : ℂ) + (t : ℂ) * I)
      (by norm_num at hσ0 ⊢; exact hσ0)
      (by norm_num at hσ1 ⊢; exact hσ1)
    simpa using h

/-- The common quadratic-tail majorant for the vertical-line shift. -/
def v15OdlyzkoQuadraticMajorant (M t : ℝ) : ℝ :=
  M / (1 + |t|) ^ 2

lemma v15OdlyzkoQuadraticMajorant_integrable (M : ℝ) :
    Integrable (v15OdlyzkoQuadraticMajorant M) volume := by
  change Integrable (fun t : ℝ ↦ M / (1 + |t|) ^ 2) volume
  exact v15OdlyzkoCriticalMajorant_two_integrable M

lemma v15OdlyzkoQuadraticMajorant_tendsto_atTop (M : ℝ) :
    Tendsto (v15OdlyzkoQuadraticMajorant M) atTop (𝓝 0) := by
  have hbase : Tendsto (fun t : ℝ ↦ 1 + |t|) atTop atTop :=
    tendsto_const_nhds.add_atTop tendsto_abs_atTop_atTop
  change Tendsto (fun t : ℝ ↦ M / (1 + |t|) ^ 2) atTop (𝓝 0)
  exact tendsto_const_nhds.div_atTop
    ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hbase)

lemma v15OdlyzkoQuadraticMajorant_tendsto_atBot (M : ℝ) :
    Tendsto (v15OdlyzkoQuadraticMajorant M) atBot (𝓝 0) := by
  have hbase : Tendsto (fun t : ℝ ↦ 1 + |t|) atBot atTop :=
    tendsto_const_nhds.add_atTop tendsto_abs_atBot_atTop
  change Tendsto (fun t : ℝ ↦ M / (1 + |t|) ^ 2) atBot (𝓝 0)
  exact tendsto_const_nhds.div_atTop
    ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hbase)

/-- The right-line archimedean integral equals its critical-line value. -/
theorem v15OdlyzkoArchimedean_right_eq_critical
    (K : Type*) [Field K] [NumberField K] :
    (∫ t : ℝ, v15OdlyzkoArchimedeanIntegrand K
      ((2 : ℂ) + (t : ℂ) * I)) =
      ∫ t : ℝ, v15OdlyzkoArchimedeanIntegrand K
        ((1 / 2 : ℂ) + (t : ℂ) * I) := by
  obtain ⟨M, -, hMajorant⟩ :=
    exists_v15OdlyzkoArchimedean_strip_majorant K
  have hdiff : ∀ s : ℂ, (1 / 2 : ℝ) ≤ s.re → s.re ≤ 2 →
      DifferentiableAt ℂ (v15OdlyzkoArchimedeanIntegrand K) s := by
    intro s hs0 _
    exact v15OdlyzkoArchimedeanIntegrand_differentiableAt K (by linarith)
  have hbound : ∀ (σ t : ℝ), (1 / 2 : ℝ) ≤ σ → σ ≤ 2 →
      ‖v15OdlyzkoArchimedeanIntegrand K ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        v15OdlyzkoQuadraticMajorant M t := by
    intro σ t hs0 hs1
    change ‖v15OdlyzkoArchimedeanIntegrand K ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      M / (1 + |t|) ^ 2
    simpa using hMajorant ((σ : ℂ) + (t : ℂ) * I)
      (by norm_num at hs0 ⊢; exact hs0)
      (by norm_num at hs1 ⊢; exact hs1)
  have hshift := Analytic.vertical_line_shift
    (f := v15OdlyzkoArchimedeanIntegrand K)
    (a := (1 / 2 : ℝ)) (b := 2) (by norm_num) hdiff
    (v15OdlyzkoQuadraticMajorant_integrable M) hbound
    (v15OdlyzkoQuadraticMajorant_tendsto_atTop M)
    (v15OdlyzkoQuadraticMajorant_tendsto_atBot M)
  norm_num at hshift ⊢
  exact hshift

/-- On the critical line, twice the real part on the upper parameter equals
the real part of the symmetric archimedean bracket. -/
theorem v15_logDeriv_ZInfty_critical_twice_re
    (K : Type*) [Field K] [NumberField K] (t : ℝ) :
    2 * (logDeriv (DedekindZeta.ZInfty K)
          ((1 / 2 : ℂ) + (t : ℂ) * I)).re =
      (logDeriv (DedekindZeta.ZInfty K)
          ((1 / 2 : ℂ) + (t : ℂ) * I) +
        logDeriv (DedekindZeta.ZInfty K)
          ((1 / 2 : ℂ) - (t : ℂ) * I)).re := by
  rw [v15OdlyzkoArchimedeanBracket_re_eq K t]
  rw [DedekindZeta.ArchimedeanLogDeriv.logDeriv_ZInfty K (by norm_num)]
  simp [Complex.log_re, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  ring

/-- Pointwise identification of the shifted integrand with the real
archimedean bracket already evaluated in the source normalization. -/
theorem v15OdlyzkoArchimedean_critical_twice_re
    (K : Type*) [Field K] [NumberField K] (t : ℝ) :
    2 * (v15OdlyzkoArchimedeanIntegrand K
        ((1 / 2 : ℂ) + (t : ℂ) * I)).re =
      v15OdlyzkoCriticalReal t *
        (logDeriv (DedekindZeta.ZInfty K)
            ((1 / 2 : ℂ) + (t : ℂ) * I) +
          logDeriv (DedekindZeta.ZInfty K)
            ((1 / 2 : ℂ) - (t : ℂ) * I)).re := by
  rw [v15OdlyzkoArchimedeanIntegrand, Complex.mul_re,
    v15OdlyzkoPhi_critical_im_eq_zero]
  simp only [v15OdlyzkoCriticalReal]
  rw [← v15_logDeriv_ZInfty_critical_twice_re K t]
  ring

/-- Exact real part of the two archimedean copies contributed by the folded
right vertical side. -/
theorem v15OdlyzkoArchimedean_right_twice_re_integral
    (K : Type*) [Field K] [NumberField K] :
    2 * (∫ t : ℝ, v15OdlyzkoArchimedeanIntegrand K
        ((2 : ℂ) + (t : ℂ) * I)).re =
      2 * Real.pi *
        (Real.log (((|NumberField.discr K| : ℤ) : ℝ)) -
          (NumberField.InfinitePlace.nrRealPlaces K : ℝ) *
            v15OdlyzkoArchLogA -
          2 * (NumberField.InfinitePlace.nrComplexPlaces K : ℝ) *
            v15OdlyzkoArchLogB) := by
  rw [v15OdlyzkoArchimedean_right_eq_critical K]
  have hint := v15OdlyzkoArchimedeanIntegrand_vertical_integrable K
    (σ := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hint' : Integrable (fun t : ℝ ↦
      v15OdlyzkoArchimedeanIntegrand K
        ((1 / 2 : ℂ) + (t : ℂ) * I)) volume := by
    convert hint using 1 <;> norm_num
  have hre :
      (∫ t : ℝ, (v15OdlyzkoArchimedeanIntegrand K
          ((1 / 2 : ℂ) + (t : ℂ) * I)).re) =
        (∫ t : ℝ, v15OdlyzkoArchimedeanIntegrand K
          ((1 / 2 : ℂ) + (t : ℂ) * I)).re :=
    integral_re hint'
  calc
    2 * (∫ t : ℝ, v15OdlyzkoArchimedeanIntegrand K
        ((1 / 2 : ℂ) + (t : ℂ) * I)).re =
        2 * ∫ t : ℝ, (v15OdlyzkoArchimedeanIntegrand K
          ((1 / 2 : ℂ) + (t : ℂ) * I)).re := congrArg (2 * ·) hre.symm
    _ = ∫ t : ℝ, 2 * (v15OdlyzkoArchimedeanIntegrand K
        ((1 / 2 : ℂ) + (t : ℂ) * I)).re := by rw [integral_const_mul]
    _ = ∫ t : ℝ, v15OdlyzkoCriticalReal t *
          (logDeriv (DedekindZeta.ZInfty K)
              ((1 / 2 : ℂ) + (t : ℂ) * I) +
            logDeriv (DedekindZeta.ZInfty K)
              ((1 / 2 : ℂ) - (t : ℂ) * I)).re := by
      apply integral_congr_ae
      filter_upwards with t
      exact v15OdlyzkoArchimedean_critical_twice_re K t
    _ = _ := v15OdlyzkoCritical_mul_archimedeanBracket_re_integral K

end

end TraceEuclidean
