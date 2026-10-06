import TraceEuclidean.OdlyzkoContourFinite
import TraceEuclidean.DedekindZetaGoodHeights
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# A weight-generic completed-zeta contour inequality

The original contour implementation specialized every intermediate theorem
to one Odlyzko weight.  This file isolates the exact properties actually
used by the argument: entire differentiability, reflection symmetry,
nonnegative real part on the closed critical strip, and uniform fourth-power
decay on the contour strip.  The resulting theorem can be instantiated by
Poitou's Gaussian-regularized transforms.
-/

namespace TraceEuclidean

noncomputable section

open Complex Set Filter Topology MeasureTheory

/-- Analytic data required of a source-normalized explicit-formula weight. -/
structure CompletedExplicitFormulaWeight where
  phi : ℂ → ℂ
  differentiable : Differentiable ℂ phi
  one_sub : ∀ s : ℂ, phi (1 - s) = phi s
  re_nonneg_closedStrip : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → 0 ≤ (phi s).re
  wideFourthPowerBound : ∃ D : ℝ, 0 ≤ D ∧ ∀ s : ℂ,
    -1 ≤ s.re → s.re ≤ 2 →
      ‖phi s‖ ≤ D / (1 + |s.im|) ^ 4

namespace CompletedExplicitFormulaWeight

variable (W : CompletedExplicitFormulaWeight)
variable {K : Type*} [Field K] [NumberField K]

/-- Completed-zeta logarithmic-derivative integrand for a generic weight. -/
def completedIntegrand
    (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  W.phi s *
    logDeriv (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s

/-- The two symmetric vertical sides folded onto `Re(s)=2`. -/
def completedVerticalPair
    (K : Type*) [Field K] [NumberField K] (t : ℝ) : ℂ :=
  (W.phi ((2 : ℂ) + (t : ℂ) * I) +
      W.phi ((-1 : ℂ) - (t : ℂ) * I)) *
    logDeriv (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K)
      ((2 : ℂ) + (t : ℂ) * I)

private theorem completedZetaPoleRemoved_analyticOn_rectangle
    (K : Type*) [Field K] [NumberField K] (z w : ℂ) :
    AnalyticOnNhd ℂ
      (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K)
      (Rectangle z w) :=
  (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved_analyticOn K).mono
    (subset_univ _)

private theorem phi_analyticOn_rectangle (z w : ℂ) :
    AnalyticOnNhd ℂ W.phi (Rectangle z w) := by
  intro s _
  exact W.differentiable.analyticAt s

/-- A boundary-zero-free rectangle has the exact generic weighted residue
identity for its finite completed-zeta zero set. -/
theorem exists_weighted_rectangle
    {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hborder : ∀ s ∈ RectangleBorder z w,
      DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s ≠ 0) :
    ∃ Z : Finset ℂ,
      (Z : Set ℂ) =
        Rectangle z w ∩
          (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ⁻¹'
            ({0} : Set ℂ) ∧
      RectangleIntegral'
          (fun s ↦ W.phi s *
            logDeriv
              (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s)
          z w =
        ∑ ρ ∈ Z,
          (analyticOrderNatAt
            (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ρ : ℂ) *
              W.phi ρ := by
  let F := DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K
  have hzBorder : z ∈ RectangleBorder z w :=
    Or.inl (Or.inl (Or.inl ⟨left_mem_uIcc, rfl⟩))
  have hzRectangle : z ∈ Rectangle z w :=
    rectangleBorder_subset_rectangle z w hzBorder
  have hzNonzero : F z ≠ 0 := hborder z hzBorder
  have hfinite : (Rectangle z w ∩ F ⁻¹' ({0} : Set ℂ)).Finite :=
    Analytic.finite_zeros_rectangle
      (completedZetaPoleRemoved_analyticOn_rectangle K z w)
      hzRectangle hzNonzero
  let Z : Finset ℂ := hfinite.toFinset
  have hZset : (Z : Set ℂ) = Rectangle z w ∩ F ⁻¹' ({0} : Set ℂ) :=
    hfinite.coe_toFinset
  refine ⟨Z, hZset, ?_⟩
  apply Analytic.rectangleIntegral'_mul_logDeriv hre him
    (completedZetaPoleRemoved_analyticOn_rectangle K z w)
    (phi_analyticOn_rectangle W z w) hborder Z
  · intro s hs
    change F s = 0 ↔ s ∈ Z
    simp only [Z, Set.Finite.mem_toFinset, mem_inter_iff, mem_preimage,
      mem_singleton_iff, hs, true_and]
  · intro s hs
    have hs' : s ∈ Rectangle z w ∩ F ⁻¹' ({0} : Set ℂ) := by
      rw [← hZset]
      exact hs
    exact hs'.1

private theorem zero_weight_re_nonneg
    {s : ℂ}
    (hs : DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s = 0) :
    0 ≤ ((analyticOrderNatAt
      (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s : ℂ) *
        W.phi s).re := by
  have hstrip := completedZetaPoleRemoved_zero_mem_closedStrip
    (K := K) hs
  rw [Complex.mul_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  exact mul_nonneg (Nat.cast_nonneg _)
    (W.re_nonneg_closedStrip s hstrip.1 hstrip.2)

private theorem zero_finset_re_nonneg
    (Z : Finset ℂ)
    (hZ : ∀ s ∈ Z,
      DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s = 0) :
    0 ≤ (∑ s ∈ Z,
      (analyticOrderNatAt
        (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s : ℂ) *
          W.phi s).re := by
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro s hs
  exact zero_weight_re_nonneg W (hZ s hs)

/-- Generic fourth-power decay and the existing good-height logarithmic
derivative estimate make both horizontal contour integrals vanish. -/
theorem horizontal_vanish_of_good_heights
    (K : Type*) [Field K] [NumberField K]
    {Cg : ℝ} (hCg : 0 ≤ Cg) {R : ℕ → ℝ}
    (hR : ∀ n : ℕ,
      (n : ℝ) + 1 ≤ R n ∧ R n ≤ 2 * ((n : ℝ) + 1) ∧
      ∀ s : ℂ, (s.im = R n ∨ s.im = -R n) →
        -1 ≤ s.re → s.re ≤ 2 →
        DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s ≠ 0 ∧
        ‖logDeriv
          (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s‖ ≤
            Cg * ((n : ℝ) + 2) ^ 3) :
    Tendsto (fun n : ℕ ↦ HIntegral (W.completedIntegrand K)
      (-1) 2 (R n)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ ↦ HIntegral (W.completedIntegrand K)
      (-1) 2 (-(R n))) atTop (𝓝 0) := by
  obtain ⟨D, hD, hDecay⟩ := W.wideFourthPowerBound
  have hint : ∀ (n : ℕ) (y : ℝ), (y = R n ∨ y = -R n) →
      ‖HIntegral (W.completedIntegrand K) (-1) 2 y‖ ≤
        3 * D * Cg / ((n : ℝ) + 2) := by
    intro n y hy
    obtain ⟨hRlower, -, hgood⟩ := hR n
    have hRnonneg : 0 ≤ R n := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hyAbs : |y| = R n := by
      rcases hy with h | h
      · rw [h, abs_of_nonneg hRnonneg]
      · rw [h, abs_neg, abs_of_nonneg hRnonneg]
    let u : ℝ := (n : ℝ) + 2
    have hu : 0 < u := by dsimp [u]; positivity
    have huR : u ≤ 1 + R n := by dsimp [u]; linarith
    have hRplus : 0 < 1 + R n := lt_of_lt_of_le hu huR
    have hPow : u ^ 4 ≤ (1 + R n) ^ 4 :=
      pow_le_pow_left₀ hu.le huR 4
    have hDiv : D / (1 + R n) ^ 4 ≤ D / u ^ 4 := by
      rw [div_le_div_iff₀ (pow_pos hRplus 4) (pow_pos hu 4)]
      exact mul_le_mul_of_nonneg_left hPow hD
    unfold HIntegral
    have hIntegral :
        ‖∫ x in (-1 : ℝ)..2,
          W.completedIntegrand K ((x : ℂ) + (y : ℂ) * I)‖ ≤
          (D * Cg / u) * |(2 : ℝ) - (-1)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Set.uIoc_of_le (by norm_num)] at hx
      let s : ℂ := (x : ℂ) + (y : ℂ) * I
      have hsre : s.re = x := by simp [s]
      have hsim : s.im = R n ∨ s.im = -R n := by
        have hsimy : s.im = y := by simp [s]
        rcases hy with h | h
        · left; rw [hsimy, h]
        · right; rw [hsimy, h]
      have hPhi : ‖W.phi s‖ ≤ D / (1 + R n) ^ 4 := by
        have h := hDecay s (by rw [hsre]; linarith [hx.1])
          (by rw [hsre]; linarith [hx.2])
        have hsimy : s.im = y := by simp [s]
        simpa only [hsimy, hyAbs] using h
      obtain ⟨-, hLog⟩ := hgood s hsim
        (by rw [hsre]; linarith [hx.1])
        (by rw [hsre]; linarith [hx.2])
      have hLogNonneg : 0 ≤ Cg * u ^ 3 :=
        mul_nonneg hCg (pow_nonneg hu.le 3)
      rw [completedIntegrand, norm_mul]
      calc
        ‖W.phi s‖ *
              ‖logDeriv
                (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s‖
            ≤ (D / (1 + R n) ^ 4) * (Cg * u ^ 3) :=
          mul_le_mul hPhi (by simpa only [u] using hLog)
            (norm_nonneg _) (div_nonneg hD (pow_nonneg hRplus.le 4))
        _ ≤ (D / u ^ 4) * (Cg * u ^ 3) :=
          mul_le_mul_of_nonneg_right hDiv hLogNonneg
        _ = D * Cg / u := by field_simp
    calc
      ‖∫ x in (-1 : ℝ)..2,
          W.completedIntegrand K ((x : ℂ) + (y : ℂ) * I)‖
          ≤ (D * Cg / u) * |(2 : ℝ) - (-1)| := hIntegral
      _ = 3 * D * Cg / ((n : ℝ) + 2) := by
        rw [show |(2 : ℝ) - (-1)| = 3 by norm_num]
        dsimp [u]
        ring
  have hMajorant : Tendsto
      (fun n : ℕ ↦ 3 * D * Cg / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  exact ⟨
    squeeze_zero_norm (fun n ↦ hint n (R n) (Or.inl rfl)) hMajorant,
    squeeze_zero_norm (fun n ↦ hint n (-(R n)) (Or.inr rfl)) hMajorant⟩

private theorem quadraticMajorant_integrable (D : ℝ) :
    Integrable (fun t : ℝ ↦ D / (1 + |t|) ^ 2) volume := by
  have hbase :
      Integrable (fun t : ℝ ↦ D * (1 + ‖t‖) ^ (-(2 : ℝ))) volume :=
    (integrable_one_add_norm (E := ℝ) (μ := volume)
      (r := (2 : ℝ)) (by norm_num)).const_mul D
  convert hbase using 1
  funext t
  rw [Real.norm_eq_abs, div_eq_mul_inv]
  congr 1
  rw [Real.rpow_neg (by positivity)]
  congr 1
  exact (Real.rpow_natCast (1 + |t|) 2).symm

private lemma right_vertical_mem_landau_inner_ball (c : ℂ) (t : ℝ) :
    (2 : ℂ) + (t : ℂ) * I ∈ Metric.closedBall c
      (83 / 100 * dedekindZetaLandauRadius c t) := by
  have hcre : |c.re| ≤ ‖c‖ := Complex.abs_re_le_norm c
  have hcim : |c.im| ≤ ‖c‖ := Complex.abs_im_le_norm c
  rw [Metric.mem_closedBall, dist_eq_norm]
  calc
    ‖(2 : ℂ) + (t : ℂ) * I - c‖ ≤
        |((2 : ℂ) + (t : ℂ) * I - c).re| +
          |((2 : ℂ) + (t : ℂ) * I - c).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = |2 - c.re| + |t - c.im| := by simp
    _ ≤ (2 + |c.re|) + (|t| + |c.im|) := by
      have htwo : |(2 : ℝ)| = 2 := by norm_num
      simpa [htwo] using add_le_add (abs_sub (2 : ℝ) c.re) (abs_sub t c.im)
    _ ≤ 2 + ‖c‖ + (|t| + ‖c‖) := by linarith
    _ ≤ 83 / 100 * dedekindZetaLandauRadius c t := by
      dsimp [dedekindZetaLandauRadius]
      nlinarith [norm_nonneg c, abs_nonneg t]

private theorem exists_right_vertical_quadratic_bound
    (K : Type*) [Field K] [NumberField K] :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ t : ℝ,
      ‖logDeriv
        (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K)
        ((2 : ℂ) + (t : ℂ) * I)‖ ≤ Cv * (1 + |t|) ^ 2 := by
  classical
  let F := DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K
  obtain ⟨c, C, hC, hLandau⟩ :=
    exists_completedZetaPoleRemoved_polynomial_landau_data K
  refine ⟨2 * C, by positivity, ?_⟩
  intro t
  obtain ⟨Z, hZ, hCount, hError⟩ := hLandau t
  let s : ℂ := (2 : ℂ) + (t : ℂ) * I
  have hsInner : s ∈ Metric.closedBall c
      (83 / 100 * dedekindZetaLandauRadius c t) := by
    simpa only [s] using right_vertical_mem_landau_inner_ball c t
  have hsRe : s.re = 2 := by simp [s]
  have hsNonzero : F s ≠ 0 := by
    apply completedZetaPoleRemoved_ne_zero_of_one_lt_re
    rw [hsRe]
    norm_num
  have hRegular := hError s hsInner hsNonzero
  have hTerm : ∀ ρ ∈ Z,
      ‖(analyticOrderNatAt F ρ : ℂ) / (s - ρ)‖ ≤
        (analyticOrderNatAt F ρ : ℝ) := by
    intro ρ hρ
    have hρSet : ρ ∈ (Z : Set ℂ) := hρ
    rw [hZ] at hρSet
    have hstrip := completedZetaPoleRemoved_zero_mem_closedStrip
      (K := K) hρSet.2
    have hre : 1 ≤ |(s - ρ).re| := by
      rw [Complex.sub_re, hsRe, abs_of_nonneg]
      · linarith [hstrip.2]
      · linarith [hstrip.2]
    have hdist : 1 ≤ ‖s - ρ‖ :=
      hre.trans (Complex.abs_re_le_norm (s - ρ))
    have hdistPos : 0 < ‖s - ρ‖ := lt_of_lt_of_le zero_lt_one hdist
    rw [norm_div, Complex.norm_natCast]
    apply (div_le_iff₀ hdistPos).2
    have hOrder : 0 ≤ (analyticOrderNatAt F ρ : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hZeroSum :
      ‖∑ ρ ∈ Z, (analyticOrderNatAt F ρ : ℂ) / (s - ρ)‖ ≤
        C * (1 + |t|) ^ 2 := by
    calc
      _ ≤ ∑ ρ ∈ Z, ‖(analyticOrderNatAt F ρ : ℂ) / (s - ρ)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z, (analyticOrderNatAt F ρ : ℝ) := by
        exact Finset.sum_le_sum fun ρ hρ ↦ hTerm ρ hρ
      _ ≤ C * (1 + |t|) ^ 2 := hCount
  calc
    ‖logDeriv F s‖ ≤
        ‖logDeriv F s -
          ∑ ρ ∈ Z, (analyticOrderNatAt F ρ : ℂ) / (s - ρ)‖ +
        ‖∑ ρ ∈ Z, (analyticOrderNatAt F ρ : ℂ) / (s - ρ)‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ C * (1 + |t|) ^ 2 + C * (1 + |t|) ^ 2 :=
      add_le_add hRegular hZeroSum
    _ = (2 * C) * (1 + |t|) ^ 2 := by ring

private theorem logDeriv_right_continuous
    (K : Type*) [Field K] [NumberField K] :
    Continuous (fun t : ℝ ↦
      logDeriv (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K)
        ((2 : ℂ) + (t : ℂ) * I)) := by
  let F := DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K
  let g : ℝ → ℂ := fun u ↦ (2 : ℂ) + (u : ℂ) * I
  change Continuous ((fun z : ℂ ↦ deriv F z / F z) ∘ g)
  have hLine : Continuous g := by
    dsimp only [g]
    fun_prop
  refine continuous_iff_continuousAt.mpr fun t ↦ ?_
  have hAnalytic : AnalyticAt ℂ F (g t) :=
    DedekindZeta.GlobalContinuation.completedZetaPoleRemoved_analyticOn K
      (g t) (mem_univ (g t))
  have hFne : F (g t) ≠ 0 := by
    apply completedZetaPoleRemoved_ne_zero_of_one_lt_re
    simp [g]
  have hQuot : ContinuousAt (fun z : ℂ ↦ deriv F z / F z) (g t) :=
    hAnalytic.deriv.continuousAt.div hAnalytic.continuousAt hFne
  exact hQuot.comp hLine.continuousAt

/-- A generic weight with fourth-power decay is absolutely integrable against
the completed-zeta logarithmic derivative on the line `Re(s)=2`. -/
theorem completedIntegrand_right_vertical_integrable
    (K : Type*) [Field K] [NumberField K] :
    Integrable (fun t : ℝ ↦
      W.completedIntegrand K ((2 : ℂ) + (t : ℂ) * I)) volume := by
  obtain ⟨D, hD, hPhi⟩ := W.wideFourthPowerBound
  obtain ⟨Cv, hCv, hLog⟩ := exists_right_vertical_quadratic_bound K
  apply (quadraticMajorant_integrable (D * Cv)).mono'
  · exact ((W.differentiable.continuous.comp
      (by fun_prop : Continuous
        (fun t : ℝ ↦ (2 : ℂ) + (t : ℂ) * I))).mul
      (logDeriv_right_continuous K)).aestronglyMeasurable
  · filter_upwards with t
    let u : ℝ := 1 + |t|
    have hu : 0 < u := by dsimp [u]; positivity
    have hPhi' : ‖W.phi ((2 : ℂ) + (t : ℂ) * I)‖ ≤ D / u ^ 4 := by
      have h := hPhi ((2 : ℂ) + (t : ℂ) * I) (by norm_num) (by norm_num)
      convert h using 1 <;> norm_num [u]
    have hLog' :
        ‖logDeriv
          (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K)
          ((2 : ℂ) + (t : ℂ) * I)‖ ≤ Cv * u ^ 2 := by
      simpa only [u] using hLog t
    rw [completedIntegrand, norm_mul]
    calc
      _ ≤ (D / u ^ 4) * (Cv * u ^ 2) :=
        mul_le_mul hPhi' hLog' (norm_nonneg _) (by positivity)
      _ = D * Cv / u ^ 2 := by field_simp

/-- Reflection symmetry folds the two vertical sides to twice the right-hand
integrand. -/
theorem completedVerticalPair_eq_two_mul
    (K : Type*) [Field K] [NumberField K] (t : ℝ) :
    W.completedVerticalPair K t =
      2 * W.completedIntegrand K ((2 : ℂ) + (t : ℂ) * I) := by
  have hreflect :
      ((-1 : ℂ) - (t : ℂ) * I) =
        1 - ((2 : ℂ) + (t : ℂ) * I) := by ring
  rw [completedVerticalPair, completedIntegrand, hreflect, W.one_sub]
  ring

theorem completedVerticalPair_integrable
    (K : Type*) [Field K] [NumberField K] :
    Integrable (W.completedVerticalPair K) volume := by
  have h := (W.completedIntegrand_right_vertical_integrable K).const_mul (2 : ℂ)
  apply h.congr
  filter_upwards with t
  exact (W.completedVerticalPair_eq_two_mul K t).symm

theorem completedVerticalPair_tendsto
    (K : Type*) [Field K] [NumberField K]
    {R : ℕ → ℝ} (hR : Tendsto R atTop atTop) :
    Tendsto (fun n : ℕ ↦ ∫ t in (-(R n))..R n,
      W.completedVerticalPair K t) atTop
      (𝓝 (∫ t : ℝ, W.completedVerticalPair K t)) := by
  exact intervalIntegral_tendsto_integral
    (W.completedVerticalPair_integrable K)
    (tendsto_neg_atTop_atBot.comp hR) hR

/-- The functional equation folds the left vertical side onto `Re(s)=2`. -/
theorem completedIntegrand_verticals_eq
    (K : Type*) [Field K] [NumberField K] (R : ℝ) :
    VIntegral (W.completedIntegrand K) 2 (-R) R -
        VIntegral (W.completedIntegrand K) (-1) (-R) R =
      I • ∫ t in (-R)..R, W.completedVerticalPair K t := by
  let F := DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K
  let L := logDeriv F
  have hLc : Continuous
      (fun t : ℝ ↦ L ((2 : ℂ) + (t : ℂ) * I)) := by
    simpa only [L, F] using logDeriv_right_continuous K
  have hPhiRight : Continuous
      (fun t : ℝ ↦ W.phi ((2 : ℂ) + (t : ℂ) * I)) :=
    W.differentiable.continuous.comp (by fun_prop)
  have hPhiReflect : Continuous
      (fun t : ℝ ↦ W.phi ((-1 : ℂ) - (t : ℂ) * I)) :=
    W.differentiable.continuous.comp (by fun_prop)
  have hleft : ∀ y : ℝ,
      W.phi ((-1 : ℂ) + (y : ℂ) * I) *
          L ((-1 : ℂ) + (y : ℂ) * I) =
        -(W.phi ((-1 : ℂ) - ((-y : ℝ) : ℂ) * I) *
          L ((2 : ℂ) + ((-y : ℝ) : ℂ) * I)) := by
    intro y
    have hs :
        ((-1 : ℂ) + (y : ℂ) * I) =
          1 - ((2 : ℂ) + ((-y : ℝ) : ℂ) * I) := by
      push_cast
      ring
    change
      W.phi ((-1 : ℂ) + (y : ℂ) * I) *
          logDeriv F ((-1 : ℂ) + (y : ℂ) * I) =
        -(W.phi ((-1 : ℂ) - ((-y : ℝ) : ℂ) * I) *
          logDeriv F ((2 : ℂ) + ((-y : ℝ) : ℂ) * I))
    rw [hs, DedekindZeta.LogDeriv.logDeriv_completedZetaPoleRemoved_one_sub]
    have hreflect :
        (1 : ℂ) - ((2 : ℂ) + ((-y : ℝ) : ℂ) * I) =
          (-1 : ℂ) - ((-y : ℝ) : ℂ) * I := by ring
    rw [hreflect]
    ring
  have hI1 : IntervalIntegrable
      (fun t : ℝ ↦ W.phi ((2 : ℂ) + (t : ℂ) * I) *
        L ((2 : ℂ) + (t : ℂ) * I)) volume (-R) R :=
    (hPhiRight.mul hLc).intervalIntegrable _ _
  have hI2 : IntervalIntegrable
      (fun t : ℝ ↦ W.phi ((-1 : ℂ) - (t : ℂ) * I) *
        L ((2 : ℂ) + (t : ℂ) * I)) volume (-R) R :=
    (hPhiReflect.mul hLc).intervalIntegrable _ _
  have hfold :
      (∫ y in (-R)..R,
        W.phi ((-1 : ℂ) + (y : ℂ) * I) *
          L ((-1 : ℂ) + (y : ℂ) * I)) =
        -∫ t in (-R)..R,
          W.phi ((-1 : ℂ) - (t : ℂ) * I) *
            L ((2 : ℂ) + (t : ℂ) * I) := by
    simp_rw [hleft]
    rw [intervalIntegral.integral_neg]
    have h := intervalIntegral.integral_comp_neg (a := -R) (b := R)
      (fun t : ℝ ↦ W.phi ((-1 : ℂ) - (t : ℂ) * I) *
        L ((2 : ℂ) + (t : ℂ) * I))
    simp only [neg_neg] at h
    rw [← h]
  dsimp only [VIntegral, completedIntegrand]
  norm_num
  change
    (I • ∫ y in (-R)..R,
      W.phi ((2 : ℂ) + (y : ℂ) * I) *
        L ((2 : ℂ) + (y : ℂ) * I)) -
      (I • ∫ y in (-R)..R,
        W.phi ((-1 : ℂ) + (y : ℂ) * I) *
          L ((-1 : ℂ) + (y : ℂ) * I)) =
        I • ∫ t in (-R)..R, W.completedVerticalPair K t
  rw [hfold, ← smul_sub, sub_neg_eq_add,
    ← intervalIntegral.integral_add hI1 hI2]
  congr 1
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  change
    W.phi ((2 : ℂ) + (t : ℂ) * I) *
          L ((2 : ℂ) + (t : ℂ) * I) +
        W.phi ((-1 : ℂ) - (t : ℂ) * I) *
          L ((2 : ℂ) + (t : ℂ) * I) =
      (W.phi ((2 : ℂ) + (t : ℂ) * I) +
          W.phi ((-1 : ℂ) - (t : ℂ) * I)) *
        L ((2 : ℂ) + (t : ℂ) * I)
  ring

private lemma inv_two_pi_I_mul_I (X : ℂ) :
    (1 / (2 * Real.pi * I) : ℂ) * (I * X) =
      (1 / (2 * Real.pi) : ℂ) * X := by
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have hPi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
  field_simp

/-- Finite generic-weight contour identities along one expanding sequence. -/
structure ContourSequenceData
    (K : Type*) [Field K] [NumberField K] where
  Cg : ℝ
  Cg_nonneg : 0 ≤ Cg
  R : ℕ → ℝ
  R_tendsto : Tendsto R atTop atTop
  R_lower : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n
  R_upper : ∀ n : ℕ, R n ≤ 2 * ((n : ℝ) + 1)
  horizontal_bound : ∀ (n : ℕ) (s : ℂ),
    (s.im = R n ∨ s.im = -R n) → -1 ≤ s.re → s.re ≤ 2 →
      DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s ≠ 0 ∧
      ‖logDeriv
        (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s‖ ≤
          Cg * ((n : ℝ) + 2) ^ 3
  boundary_nonzero : ∀ n : ℕ, ∀ s ∈
    RectangleBorder (odlyzkoContourLower 2 (R n))
      (odlyzkoContourUpper 2 (R n)),
    DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s ≠ 0
  zeros : ℕ → Finset ℂ
  zero_set : ∀ n : ℕ,
    (zeros n : Set ℂ) =
      Rectangle (odlyzkoContourLower 2 (R n))
          (odlyzkoContourUpper 2 (R n)) ∩
        (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ⁻¹'
          ({0} : Set ℂ)
  rectangle_identity : ∀ n : ℕ,
    RectangleIntegral' (W.completedIntegrand K)
        (odlyzkoContourLower 2 (R n))
        (odlyzkoContourUpper 2 (R n)) =
      ∑ ρ ∈ zeros n,
        (analyticOrderNatAt
          (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ρ : ℂ) *
            W.phi ρ
  zero_sum_re_nonneg : ∀ n : ℕ, 0 ≤
    (∑ ρ ∈ zeros n,
      (analyticOrderNatAt
        (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ρ : ℂ) *
          W.phi ρ).re
  horizontal_top_vanish :
    Tendsto (fun n : ℕ ↦ HIntegral (W.completedIntegrand K)
      (-1) 2 (R n)) atTop (𝓝 0)
  horizontal_bottom_vanish :
    Tendsto (fun n : ℕ ↦ HIntegral (W.completedIntegrand K)
      (-1) 2 (-(R n))) atTop (𝓝 0)

/-- The completed zeta good-height sequence supplies all finite contour data
for every admissible generic weight. -/
theorem exists_contourSequenceData
    (K : Type*) [Field K] [NumberField K] :
    Nonempty (W.ContourSequenceData K) := by
  classical
  obtain ⟨Cg, hCg, R, hRTop, hR⟩ :=
    exists_completedZetaPoleRemoved_good_height_sequence K
  obtain ⟨hTop, hBottom⟩ :=
    W.horizontal_vanish_of_good_heights K hCg hR
  have hBoundary : ∀ n : ℕ, ∀ s ∈
      RectangleBorder (odlyzkoContourLower 2 (R n))
        (odlyzkoContourUpper 2 (R n)),
      DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s ≠ 0 := by
    intro n s hs
    obtain ⟨⟨hbottom | hleft⟩ | htop⟩ | hright := hs
    · obtain ⟨-, -, hgood⟩ := hR n
      have hre : -1 ≤ s.re ∧ s.re ≤ 2 := by
        have hre' := hbottom.1
        simp [odlyzkoContourLower, odlyzkoContourUpper,
          Set.mem_uIcc] at hre'
        rcases hre' with h | h
        · constructor <;> linarith
        · exfalso; linarith
      exact (hgood s (Or.inr (by
        simpa [odlyzkoContourLower] using hbottom.2)) hre.1 hre.2).1
    · apply completedZetaPoleRemoved_ne_zero_of_re_lt_zero
      have hsre' : s.re = 1 - (2 : ℝ) := by
        simpa [odlyzkoContourLower] using hleft.1
      have hsre : s.re = -1 := by linarith
      rw [hsre]
      norm_num
    · obtain ⟨-, -, hgood⟩ := hR n
      have hre : -1 ≤ s.re ∧ s.re ≤ 2 := by
        have hre' := htop.1
        simp [odlyzkoContourLower, odlyzkoContourUpper,
          Set.mem_uIcc] at hre'
        rcases hre' with h | h
        · constructor <;> linarith
        · exfalso; linarith
      exact (hgood s (Or.inl (by
        simpa [odlyzkoContourUpper] using htop.2)) hre.1 hre.2).1
    · apply completedZetaPoleRemoved_ne_zero_of_one_lt_re
      have hsre : s.re = 2 := by
        simpa [odlyzkoContourUpper] using hright.1
      rw [hsre]
      norm_num
  have hFinite : ∀ n : ℕ, ∃ Z : Finset ℂ,
      (Z : Set ℂ) =
        Rectangle (odlyzkoContourLower 2 (R n))
            (odlyzkoContourUpper 2 (R n)) ∩
          (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ⁻¹'
            ({0} : Set ℂ) ∧
      RectangleIntegral' (W.completedIntegrand K)
          (odlyzkoContourLower 2 (R n))
          (odlyzkoContourUpper 2 (R n)) =
        ∑ ρ ∈ Z,
          (analyticOrderNatAt
            (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ρ : ℂ) *
              W.phi ρ := by
    intro n
    have hRn : 0 ≤ R n := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith [(hR n).1]
    apply W.exists_weighted_rectangle
    · simp [odlyzkoContourLower, odlyzkoContourUpper]
      norm_num
    · simp [odlyzkoContourLower, odlyzkoContourUpper]
      linarith
    · exact hBoundary n
  choose Z hZset hIdentity using hFinite
  have hNonneg : ∀ n : ℕ, 0 ≤
      (∑ ρ ∈ Z n,
        (analyticOrderNatAt
          (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ρ : ℂ) *
            W.phi ρ).re := by
    intro n
    apply W.zero_finset_re_nonneg
    intro ρ hρ
    have hρSet : ρ ∈ (Z n : Set ℂ) := hρ
    rw [hZset n] at hρSet
    exact hρSet.2
  refine ⟨{
    Cg := Cg
    Cg_nonneg := hCg
    R := R
    R_tendsto := hRTop
    R_lower := fun n ↦ (hR n).1
    R_upper := fun n ↦ (hR n).2.1
    horizontal_bound := fun n ↦ (hR n).2.2
    boundary_nonzero := hBoundary
    zeros := Z
    zero_set := hZset
    rectangle_identity := hIdentity
    zero_sum_re_nonneg := hNonneg
    horizontal_top_vanish := hTop
    horizontal_bottom_vanish := hBottom
  }⟩

/-- The finite rectangle splits into its horizontal error and folded vertical
integral for a generic weight. -/
theorem contourSequence_rectangle_decomposition
    (K : Type*) [Field K] [NumberField K]
    (data : W.ContourSequenceData K) (n : ℕ) :
    RectangleIntegral' (W.completedIntegrand K)
        (odlyzkoContourLower 2 (data.R n))
        (odlyzkoContourUpper 2 (data.R n)) =
      (1 / (2 * Real.pi * I) : ℂ) *
        (HIntegral (W.completedIntegrand K) (-1) 2 (-(data.R n)) -
          HIntegral (W.completedIntegrand K) (-1) 2 (data.R n)) +
      (1 / (2 * Real.pi) : ℂ) *
        ∫ t in (-(data.R n))..data.R n,
          W.completedVerticalPair K t := by
  have e₁ : (odlyzkoContourLower 2 (data.R n)).re = -1 := by
    norm_num [odlyzkoContourLower]
  have e₂ : (odlyzkoContourLower 2 (data.R n)).im = -(data.R n) := by
    simp [odlyzkoContourLower]
  have e₃ : (odlyzkoContourUpper 2 (data.R n)).re = 2 := by
    simp [odlyzkoContourUpper]
  have e₄ : (odlyzkoContourUpper 2 (data.R n)).im = data.R n := by
    simp [odlyzkoContourUpper]
  rw [RectangleIntegral', RectangleIntegral, smul_eq_mul, e₁, e₂, e₃, e₄]
  have hVertical := W.completedIntegrand_verticals_eq K (data.R n)
  rw [show ∀ A B V₁ V₂ : ℂ,
      A - B + V₁ - V₂ = (A - B) + (V₁ - V₂) from
        fun _ _ _ _ ↦ by ring,
    hVertical, smul_eq_mul, mul_add, inv_two_pi_I_mul_I]

/-- The normalized finite rectangle integrals converge to the folded
full-line integral. -/
theorem contourSequence_rectangle_tendsto
    (K : Type*) [Field K] [NumberField K]
    (data : W.ContourSequenceData K) :
    Tendsto (fun n : ℕ ↦
      RectangleIntegral' (W.completedIntegrand K)
        (odlyzkoContourLower 2 (data.R n))
        (odlyzkoContourUpper 2 (data.R n))) atTop
      (𝓝 ((1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ, W.completedVerticalPair K t)) := by
  have hHorizontal :=
    ((data.horizontal_bottom_vanish.sub data.horizontal_top_vanish).const_mul
      (1 / (2 * Real.pi * I) : ℂ))
  have hVertical :=
    (W.completedVerticalPair_tendsto K data.R_tendsto).const_mul
      (1 / (2 * Real.pi) : ℂ)
  have hLimit := hHorizontal.add hVertical
  simp only [sub_zero, mul_zero, zero_add] at hLimit
  exact hLimit.congr fun n ↦
    (W.contourSequence_rectangle_decomposition K data n).symm

/-- Generic completed-zeta contour inequality.  It is obtained as a limit of
finite nonnegative weighted zero sums and does not assume an enumeration of
the zeros. -/
theorem completedVerticalPair_integral_re_nonneg
    (K : Type*) [Field K] [NumberField K] :
    0 ≤ ((1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, W.completedVerticalPair K t).re := by
  classical
  let data : W.ContourSequenceData K :=
    Classical.choice (W.exists_contourSequenceData K)
  have hLimit := W.contourSequence_rectangle_tendsto K data
  have hLimitRe :
      Tendsto (fun n : ℕ ↦
        (RectangleIntegral' (W.completedIntegrand K)
          (odlyzkoContourLower 2 (data.R n))
          (odlyzkoContourUpper 2 (data.R n))).re) atTop
        (𝓝 (((1 / (2 * Real.pi) : ℂ) *
          ∫ t : ℝ, W.completedVerticalPair K t).re)) :=
    (Complex.continuous_re.tendsto _).comp hLimit
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hLimitRe
  filter_upwards with n
  rw [data.rectangle_identity n]
  exact data.zero_sum_re_nonneg n

end CompletedExplicitFormulaWeight

end
end TraceEuclidean
