import TraceEuclidean.V15DedekindZetaGoodHeights
import TraceEuclidean.V15OdlyzkoFourthDecayCriterion
import TraceEuclidean.Analytic.ResidueCalcOnRectangles

/-!
# Vanishing of the horizontal Odlyzko contour integrals

The good-height theorem gives cubic growth for the logarithmic derivative,
while the exact Odlyzko transform has fourth-power decay uniformly on the
closed strip used by the contour.  Their product is bounded by a constant
times `1 / (n + 2)`, so both horizontal integrals tend to zero.
-/

namespace TraceEuclidean

noncomputable section

open Complex Set MeasureTheory Filter Topology

/-- Along any sequence satisfying the proved good-height bounds, the top and
bottom horizontal sides of the Odlyzko contour vanish. -/
theorem v15_completedZetaPoleRemoved_horizontal_vanish_of_good_heights
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
    Tendsto (fun n : ℕ ↦ HIntegral
      (fun s ↦ v15OdlyzkoPhi s * logDeriv
        (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s)
      (-1) 2 (R n)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ ↦ HIntegral
      (fun s ↦ v15OdlyzkoPhi s * logDeriv
        (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s)
      (-1) 2 (-(R n))) atTop (𝓝 0) := by
  obtain ⟨D, hD, hDecay⟩ := v15OdlyzkoPhi_exists_wideFourthPowerBound
  have hint : ∀ (n : ℕ) (y : ℝ), (y = R n ∨ y = -R n) →
      ‖HIntegral
        (fun s ↦ v15OdlyzkoPhi s * logDeriv
          (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s)
        (-1) 2 y‖ ≤ 3 * D * Cg / ((n : ℝ) + 2) := by
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
          v15OdlyzkoPhi ((x : ℂ) + (y : ℂ) * I) *
            logDeriv
              (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K)
              ((x : ℂ) + (y : ℂ) * I)‖ ≤
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
      have hPhi : ‖v15OdlyzkoPhi s‖ ≤ D / (1 + R n) ^ 4 := by
        have h := hDecay s (by rw [hsre]; linarith [hx.1])
          (by rw [hsre]; linarith [hx.2])
        have hsimy : s.im = y := by simp [s]
        simpa only [hsimy, hyAbs] using h
      obtain ⟨-, hLog⟩ := hgood s hsim
        (by rw [hsre]; linarith [hx.1])
        (by rw [hsre]; linarith [hx.2])
      have hLogNonneg : 0 ≤ Cg * u ^ 3 :=
        mul_nonneg hCg (pow_nonneg hu.le 3)
      calc
        ‖v15OdlyzkoPhi s * logDeriv
            (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s‖ =
            ‖v15OdlyzkoPhi s‖ *
              ‖logDeriv
                (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s‖ :=
          norm_mul _ _
        _ ≤ (D / (1 + R n) ^ 4) * (Cg * u ^ 3) :=
          mul_le_mul hPhi (by simpa only [u] using hLog)
            (norm_nonneg _) (div_nonneg hD (pow_nonneg hRplus.le 4))
        _ ≤ (D / u ^ 4) * (Cg * u ^ 3) :=
          mul_le_mul_of_nonneg_right hDiv hLogNonneg
        _ = D * Cg / u := by field_simp
    calc
      ‖∫ x in (-1 : ℝ)..2,
          v15OdlyzkoPhi ((x : ℂ) + (y : ℂ) * I) *
            logDeriv
              (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K)
              ((x : ℂ) + (y : ℂ) * I)‖
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

/-- There exists a sequence of zero-free good heights tending to infinity
along which both horizontal contour integrals vanish. -/
theorem exists_v15_completedZetaPoleRemoved_horizontal_vanishing_sequence
    (K : Type*) [Field K] [NumberField K] :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∃ R : ℕ → ℝ,
      Tendsto R atTop atTop ∧
      (∀ n : ℕ,
        (n : ℝ) + 1 ≤ R n ∧ R n ≤ 2 * ((n : ℝ) + 1) ∧
        ∀ s : ℂ, (s.im = R n ∨ s.im = -R n) →
          -1 ≤ s.re → s.re ≤ 2 →
          DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s ≠ 0 ∧
          ‖logDeriv
            (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s‖ ≤
              Cg * ((n : ℝ) + 2) ^ 3) ∧
      Tendsto (fun n : ℕ ↦ HIntegral
        (fun s ↦ v15OdlyzkoPhi s * logDeriv
          (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s)
        (-1) 2 (R n)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ ↦ HIntegral
        (fun s ↦ v15OdlyzkoPhi s * logDeriv
          (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s)
        (-1) 2 (-(R n))) atTop (𝓝 0) := by
  obtain ⟨Cg, hCg, R, hRTop, hR⟩ :=
    exists_v15_completedZetaPoleRemoved_good_height_sequence K
  obtain ⟨hTop, hBottom⟩ :=
    v15_completedZetaPoleRemoved_horizontal_vanish_of_good_heights
      K hCg hR
  exact ⟨Cg, hCg, R, hRTop, hR, hTop, hBottom⟩

end

end TraceEuclidean
