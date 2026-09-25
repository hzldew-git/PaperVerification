import TraceEuclidean.Analytic.LandauPartialFraction
import TraceEuclidean.V15MellinGrowth

/-!
# Landau partial fractions for the completed Dedekind zeta

This module specializes the generic disk form of Landau's lemma to the
entire pole-removed completed Dedekind zeta.  Its already proved global
quadratic exponential bound supplies the disk majorant.  The output is a
finite local zero set, a multiplicity bound, and a quantitative approximation
to the logarithmic derivative away from those zeros.
-/

namespace TraceEuclidean

noncomputable section

open Complex Set Metric

/-- A disk radius large enough for the later horizontal contour at height
comparable with `|t|`. -/
def v15DedekindZetaLandauRadius (c : ℂ) (t : ℝ) : ℝ :=
  8 * (‖c‖ + |t| + 4)

/-- The normalized disk majorant used in Landau's lemma. -/
def v15DedekindZetaLandauMajorant
    (F : ℂ → ℂ) (c : ℂ) (A D t : ℝ) : ℝ :=
  2 + D * Real.exp
      (A * (1 + ‖c‖ + v15DedekindZetaLandauRadius c t) ^ 2) *
        ‖F c‖⁻¹

/-- The constructed completed Dedekind zeta satisfies Landau's local partial
fraction estimate on disks whose radius grows linearly with the height.
All constants are independent of `t`. -/
theorem exists_v15_completedZetaPoleRemoved_landau_data
    (K : Type*) [Field K] [NumberField K] :
    ∃ c : ℂ, ∃ A D : ℝ,
      DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K c ≠ 0 ∧
      0 ≤ A ∧ 0 ≤ D ∧
      ∀ t : ℝ,
        ∃ Z : Finset ℂ,
          (Z : Set ℂ) =
              {ρ ∈ closedBall c
                  (22 / 25 * v15DedekindZetaLandauRadius c t) |
                DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K ρ = 0} ∧
          (∑ ρ ∈ Z,
              (analyticOrderNatAt
                (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ρ : ℝ)) ≤
            1 / Real.log ((24 / 25 : ℝ) / (22 / 25 : ℝ)) *
              Real.log (v15DedekindZetaLandauMajorant
                (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K)
                c A D t) ∧
          ∀ s ∈ closedBall c
              (83 / 100 * v15DedekindZetaLandauRadius c t),
            DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s ≠ 0 →
            ‖logDeriv
                (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s -
              ∑ ρ ∈ Z,
                (analyticOrderNatAt
                  (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ρ : ℂ) /
                    (s - ρ)‖ ≤
              44795000 / v15DedekindZetaLandauRadius c t *
                Real.log (v15DedekindZetaLandauMajorant
                  (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K)
                  c A D t) := by
  let F := DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K
  obtain ⟨c, hc⟩ := v15_completedZetaPoleRemoved_exists_nonzero (K := K)
  obtain ⟨A, D, hA, hD, hglobal⟩ :=
    V15MellinGrowth.completedZetaPoleRemoved_hasQuadraticExponentialBound K
  refine ⟨c, A, D, hc, hA, hD, ?_⟩
  intro t
  let R : ℝ := v15DedekindZetaLandauRadius c t
  let B : ℝ := v15DedekindZetaLandauMajorant F c A D t
  have hR : 0 < R := by
    dsimp [R, v15DedekindZetaLandauRadius]
    positivity
  have hFc : 0 < ‖F c‖ := norm_pos_iff.mpr hc
  have hB : 2 ≤ B := by
    dsimp [B, v15DedekindZetaLandauMajorant]
    exact le_add_of_nonneg_right
      (mul_nonneg
        (mul_nonneg hD (Real.exp_nonneg _))
        (inv_nonneg.mpr (norm_nonneg _)))
  have hAnalytic : AnalyticOnNhd ℂ F (closedBall c R) :=
    (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved_analyticOn K).mono
      (subset_univ _)
  have hBound : ∀ w ∈ closedBall c (24 / 25 * R),
      ‖F w‖ ≤ B * ‖F c‖ := by
    intro w hw
    have hdist : ‖w - c‖ ≤ 24 / 25 * R := by
      simpa only [mem_closedBall, dist_eq_norm] using hw
    have hfactor : (24 / 25 : ℝ) * R ≤ R := by
      nlinarith [hR]
    have hnorm : ‖w‖ ≤ ‖c‖ + R := by
      calc
        ‖w‖ = ‖(w - c) + c‖ := by simp
        _ ≤ ‖w - c‖ + ‖c‖ := norm_add_le _ _
        _ ≤ ‖c‖ + R := by linarith
    have hbase : 1 + ‖w‖ ≤ 1 + ‖c‖ + R := by linarith
    have hsq : (1 + ‖w‖) ^ 2 ≤ (1 + ‖c‖ + R) ^ 2 := by
      nlinarith [norm_nonneg w, norm_nonneg c]
    have hexp :
        Real.exp (A * (1 + ‖w‖) ^ 2) ≤
          Real.exp (A * (1 + ‖c‖ + R) ^ 2) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsq hA)
    have hupper :
        ‖F w‖ ≤ D * Real.exp (A * (1 + ‖c‖ + R) ^ 2) :=
      (hglobal w).trans (mul_le_mul_of_nonneg_left hexp hD)
    have hmajorant :
        D * Real.exp (A * (1 + ‖c‖ + R) ^ 2) ≤ B * ‖F c‖ := by
      have hcancel : ‖F c‖⁻¹ * ‖F c‖ = 1 := inv_mul_cancel₀ hFc.ne'
      dsimp [B, v15DedekindZetaLandauMajorant]
      change D * Real.exp (A * (1 + ‖c‖ + R) ^ 2) ≤
        (2 + D * Real.exp (A * (1 + ‖c‖ + R) ^ 2) * ‖F c‖⁻¹) * ‖F c‖
      rw [add_mul, mul_assoc, hcancel, mul_one]
      linarith [norm_nonneg (F c)]
    exact hupper.trans hmajorant
  simpa only [R, B, F] using
    (Analytic.logDeriv_partial_fraction_disk
      (f := F) (s₀ := c) (R := R) (B := B)
      hR hAnalytic hc hB hBound)

/-- The logarithm of the Landau disk majorant grows at most quadratically in
the height. -/
theorem v15DedekindZetaLandauMajorant_log_quadratic
    {F : ℂ → ℂ} {c : ℂ} {A D : ℝ}
    (hFc : F c ≠ 0) (hA : 0 ≤ A) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      Real.log (v15DedekindZetaLandauMajorant F c A D t) ≤
        C * (1 + |t|) ^ 2 := by
  let Q : ℝ := D * ‖F c‖⁻¹
  let L : ℝ := 9 * ‖c‖ + 41
  let C : ℝ := Real.log (2 + Q) + A * L ^ 2
  have hnorm : 0 < ‖F c‖ := norm_pos_iff.mpr hFc
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact mul_nonneg hD (inv_nonneg.mpr (norm_nonneg _))
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  have hlogQ : 0 ≤ Real.log (2 + Q) :=
    Real.log_nonneg (by linarith)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro t
  let x : ℝ := |t|
  let X : ℝ := 1 + ‖c‖ + v15DedekindZetaLandauRadius c t
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hX : X = 9 * ‖c‖ + 8 * x + 33 := by
    dsimp [X, x, v15DedekindZetaLandauRadius]
    ring
  have hXL : X ≤ L * (1 + x) := by
    rw [hX]
    dsimp [L]
    nlinarith [norm_nonneg c]
  have hXnonneg : 0 ≤ X := by
    dsimp [X, v15DedekindZetaLandauRadius]
    positivity
  have hsq : X ^ 2 ≤ L ^ 2 * (1 + x) ^ 2 := by
    nlinarith
  have hE : 0 ≤ A * X ^ 2 := mul_nonneg hA (sq_nonneg X)
  have hexpOne : 1 ≤ Real.exp (A * X ^ 2) := Real.one_le_exp hE
  have hmajorantPos :
      0 < v15DedekindZetaLandauMajorant F c A D t := by
    dsimp [v15DedekindZetaLandauMajorant]
    positivity
  have hmajorantUpper :
      v15DedekindZetaLandauMajorant F c A D t ≤
        (2 + Q) * Real.exp (A * X ^ 2) := by
    dsimp [v15DedekindZetaLandauMajorant, Q, X]
    nlinarith
  have hlogUpper := Real.log_le_log hmajorantPos hmajorantUpper
  have hQpos : 0 < 2 + Q := by linarith
  rw [Real.log_mul hQpos.ne' (Real.exp_ne_zero _), Real.log_exp] at hlogUpper
  have hone : 1 ≤ (1 + x) ^ 2 := by nlinarith
  have hAterm : A * X ^ 2 ≤ A * L ^ 2 * (1 + x) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsq hA]
  calc
    Real.log (v15DedekindZetaLandauMajorant F c A D t) ≤
        Real.log (2 + Q) + A * X ^ 2 := hlogUpper
    _ ≤ (Real.log (2 + Q) + A * L ^ 2) * (1 + x) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hone hlogQ]
    _ = C * (1 + |t|) ^ 2 := by rfl

/-- Polynomial form of the Landau data.  A single constant controls both the
local zero multiplicity and the regular part of the logarithmic derivative. -/
theorem exists_v15_completedZetaPoleRemoved_polynomial_landau_data
    (K : Type*) [Field K] [NumberField K] :
    ∃ c : ℂ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ,
        ∃ Z : Finset ℂ,
          (Z : Set ℂ) =
              {ρ ∈ closedBall c
                  (22 / 25 * v15DedekindZetaLandauRadius c t) |
                DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K ρ = 0} ∧
          (∑ ρ ∈ Z,
              (analyticOrderNatAt
                (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ρ : ℝ)) ≤
            C * (1 + |t|) ^ 2 ∧
          ∀ s ∈ closedBall c
              (83 / 100 * v15DedekindZetaLandauRadius c t),
            DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s ≠ 0 →
            ‖logDeriv
                (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s -
              ∑ ρ ∈ Z,
                (analyticOrderNatAt
                  (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ρ : ℂ) /
                    (s - ρ)‖ ≤
              C * (1 + |t|) ^ 2 := by
  obtain ⟨c, A, D, hc, hA, hD, hLandau⟩ :=
    exists_v15_completedZetaPoleRemoved_landau_data K
  obtain ⟨C₀, hC₀, hLog⟩ :=
    v15DedekindZetaLandauMajorant_log_quadratic
      (F := DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K)
      hc hA hD
  let κ : ℝ := 1 / Real.log ((24 / 25 : ℝ) / (22 / 25 : ℝ))
  let C : ℝ := max (κ * C₀) (44795000 * C₀)
  have hκ : 0 ≤ κ := by
    dsimp [κ]
    exact le_of_lt (one_div_pos.mpr (Real.log_pos (by norm_num)))
  have hC : 0 ≤ C := by
    dsimp [C]
    exact le_trans (mul_nonneg hκ hC₀) (le_max_left _ _)
  refine ⟨c, C, hC, ?_⟩
  intro t
  obtain ⟨Z, hZ, hCount, hError⟩ := hLandau t
  have hLogT := hLog t
  have hCount' :
      (∑ ρ ∈ Z,
          (analyticOrderNatAt
            (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ρ : ℝ)) ≤
        C * (1 + |t|) ^ 2 := by
    calc
      _ ≤ κ * Real.log (v15DedekindZetaLandauMajorant
          (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K)
          c A D t) := by simpa only [κ] using hCount
      _ ≤ κ * (C₀ * (1 + |t|) ^ 2) :=
        mul_le_mul_of_nonneg_left hLogT hκ
      _ = (κ * C₀) * (1 + |t|) ^ 2 := by ring
      _ ≤ C * (1 + |t|) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  refine ⟨Z, hZ, hCount', ?_⟩
  intro s hs hFs
  have hRaw := hError s hs hFs
  let R : ℝ := v15DedekindZetaLandauRadius c t
  have hR : 1 ≤ R := by
    dsimp [R, v15DedekindZetaLandauRadius]
    nlinarith [norm_nonneg c, abs_nonneg t]
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hCoeff : 0 ≤ 44795000 / R := div_nonneg (by norm_num) hRpos.le
  have hCoeffLe : 44795000 / R ≤ (44795000 : ℝ) := by
    apply (div_le_iff₀ hRpos).2
    nlinarith
  calc
    ‖logDeriv
          (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s -
        ∑ ρ ∈ Z,
          (analyticOrderNatAt
            (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ρ : ℂ) /
              (s - ρ)‖ ≤
        44795000 / R *
          Real.log (v15DedekindZetaLandauMajorant
            (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K)
            c A D t) := by simpa only [R] using hRaw
    _ ≤ (44795000 / R) * (C₀ * (1 + |t|) ^ 2) :=
      mul_le_mul_of_nonneg_left hLogT hCoeff
    _ ≤ 44795000 * (C₀ * (1 + |t|) ^ 2) :=
      mul_le_mul_of_nonneg_right hCoeffLe
        (mul_nonneg hC₀ (sq_nonneg _))
    _ = (44795000 * C₀) * (1 + |t|) ^ 2 := by ring
    _ ≤ C * (1 + |t|) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)

end

end TraceEuclidean
