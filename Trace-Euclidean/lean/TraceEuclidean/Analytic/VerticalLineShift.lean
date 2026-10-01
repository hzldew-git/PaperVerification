/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Vertical-line shifts under an integrable strip majorant

Adapted from `Zeta23/WeilEF/VerticalLine.lean` in
<https://github.com/anthropics/zeta-23-lean> at commit
`fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`.

The proof applies Cauchy's theorem on finite rectangles, bounds the two
horizontal sides by a common majorant, and then passes to the improper
integrals on the two vertical sides.
-/

noncomputable section

namespace TraceEuclidean.Analytic

open Complex Filter MeasureTheory Set Topology

/-- Continuity gives integrability on a vertical line when the function is
bounded there by an integrable real majorant. -/
lemma integrable_line {f : ℂ → ℂ} {σ : ℝ}
    (hf : ∀ t : ℝ, DifferentiableAt ℂ f (σ + t * I))
    {φ : ℝ → ℝ} (hφ : Integrable φ)
    (hb : ∀ t : ℝ, ‖f (σ + t * I)‖ ≤ φ t) :
    Integrable (fun t : ℝ ↦ f (σ + t * I)) := by
  have hc : Continuous (fun t : ℝ ↦ f (σ + t * I)) := by
    refine continuous_iff_continuousAt.mpr fun t ↦ ?_
    have hg : Continuous (fun t : ℝ ↦ (σ : ℂ) + t * I) := by fun_prop
    show ContinuousAt (f ∘ fun t : ℝ ↦ (σ : ℂ) + t * I) t
    exact ContinuousAt.comp_of_eq (hf t).continuousAt hg.continuousAt rfl
  exact hφ.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hb)

/-- General vertical-line shift for an analytic function with an integrable,
uniformly decaying majorant on a closed strip. -/
theorem vertical_line_shift {f : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → DifferentiableAt ℂ f s)
    {φ : ℝ → ℝ} (hφ : Integrable φ)
    (hbound : ∀ (σ t : ℝ), a ≤ σ → σ ≤ b → ‖f (σ + t * I)‖ ≤ φ t)
    (hφtop : Tendsto φ atTop (nhds 0))
    (hφbot : Tendsto φ atBot (nhds 0)) :
    ∫ t : ℝ, f (b + t * I) = ∫ t : ℝ, f (a + t * I) := by
  have hint : ∀ σ : ℝ, a ≤ σ → σ ≤ b →
      Integrable (fun t : ℝ ↦ f (σ + t * I)) :=
    fun σ h1 h2 ↦ integrable_line
      (fun t ↦ hf _ (by simp [h1]) (by simp [h2])) hφ
      (fun t ↦ hbound σ t h1 h2)
  have hφnn : ∀ t, 0 ≤ φ t := fun t ↦
    (norm_nonneg _).trans (hbound a t le_rfl hab)
  have hrect : ∀ R : ℝ,
      (∫ y in (-R)..R, f (b + y * I)) - (∫ y in (-R)..R, f (a + y * I)) =
        -I * ((∫ x in a..b, f (x + R * I)) -
          (∫ x in a..b, f (x + (-R) * I))) := by
    intro R
    have hdiff : DifferentiableOn ℂ f (Set.uIcc a b ×ℂ Set.uIcc (-R) R) := by
      intro z hz
      rw [Set.uIcc_of_le hab] at hz
      exact (hf z hz.1.1 hz.1.2).differentiableWithinAt
    have H := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((a : ℂ) + (-R : ℝ) * I) ((b : ℂ) + (R : ℝ) * I) (by simpa using hdiff)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero, add_im, mul_im, zero_add, smul_eq_mul] at H
    have key :
        I * ((∫ y in (-R)..R, f (b + y * I)) -
          (∫ y in (-R)..R, f (a + y * I))) =
            (∫ x in a..b, f (x + R * I)) -
              (∫ x in a..b, f (x + (-R) * I)) := by
      push_cast at H ⊢
      linear_combination H
    calc
      (∫ y in (-R)..R, f (b + y * I)) -
          (∫ y in (-R)..R, f (a + y * I)) =
          -(I * I) * ((∫ y in (-R)..R, f (b + y * I)) -
            (∫ y in (-R)..R, f (a + y * I))) := by
            rw [I_mul_I]
            ring
      _ = -I * (I * ((∫ y in (-R)..R, f (b + y * I)) -
            (∫ y in (-R)..R, f (a + y * I)))) := by ring
      _ = _ := by rw [key]
  have hsmall : ∀ R : ℝ,
      ‖(∫ y in (-R)..R, f (b + y * I)) -
        (∫ y in (-R)..R, f (a + y * I))‖ ≤
          (b - a) * (φ R + φ (-R)) := by
    intro R
    rw [hrect R, norm_mul, norm_neg, Complex.norm_I, one_mul]
    have h1 : ‖∫ x in a..b, f (x + R * I)‖ ≤ φ R * |b - a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun x hx ↦ by
        rw [Set.uIoc_of_le hab] at hx
        exact hbound x R hx.1.le hx.2
    have h2 : ‖∫ x in a..b, f (x + (-R) * I)‖ ≤ φ (-R) * |b - a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun x hx ↦ by
        rw [Set.uIoc_of_le hab] at hx
        simpa using hbound x (-R) hx.1.le hx.2
    rw [abs_of_nonneg (by linarith)] at h1 h2
    calc
      ‖(∫ x in a..b, f (x + R * I)) -
          (∫ x in a..b, f (x + (-R) * I))‖ ≤
          ‖∫ x in a..b, f (x + R * I)‖ +
            ‖∫ x in a..b, f (x + (-R) * I)‖ := norm_sub_le _ _
      _ ≤ φ R * (b - a) + φ (-R) * (b - a) := add_le_add h1 h2
      _ = (b - a) * (φ R + φ (-R)) := by ring
  set g : ℝ → ℂ := fun R ↦
    (∫ y in (-R)..R, f (b + y * I)) -
      (∫ y in (-R)..R, f (a + y * I)) with hg
  have hlim1 : Tendsto g atTop
      (nhds ((∫ t : ℝ, f (b + t * I)) - (∫ t : ℝ, f (a + t * I)))) := by
    apply Tendsto.sub
    · exact intervalIntegral_tendsto_integral (hint b hab le_rfl)
        tendsto_neg_atTop_atBot tendsto_id
    · exact intervalIntegral_tendsto_integral (hint a le_rfl hab)
        tendsto_neg_atTop_atBot tendsto_id
  have hlim0 : Tendsto g atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun R ↦ norm_nonneg _) (fun R ↦ hsmall R) ?_
    have hlim : Tendsto (fun R ↦ (b - a) * (φ R + φ (-R))) atTop
        (nhds ((b - a) * (0 + 0))) :=
      (hφtop.add (hφbot.comp tendsto_neg_atTop_atBot)).const_mul _
    simpa using hlim
  exact sub_eq_zero.mp (tendsto_nhds_unique hlim1 hlim0)

end TraceEuclidean.Analytic
