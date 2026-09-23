import TraceEuclidean.V15OdlyzkoZeroSummability
import Mathlib.Data.Finset.Preimage

/-!
# Explicit Dedekind-zeta zero counts and the summability interface

Hasanalizade--Shen--Wong, *Counting zeros of Dedekind zeta functions*,
Corollary 1.2 (2021), bounds the number of critical-strip zeros counted with
multiplicity for `T ≥ 1`. This file checks the elementary reduction of that
published numerical bound to the `T log (2 + T)` interface. The analytic
zero-count theorem and the identification of an enumerated zero family with
the paper's multiplicity count are still inputs.
-/

namespace TraceEuclidean

noncomputable section

/-- Corollary 1.2 of Hasanalizade--Shen--Wong in its expanded-log form,
applied to an indexed family whose number up to height `T` is no greater than
the paper's total zero count `N_K(T)`. Here `d` is the absolute discriminant
and `n` is the field degree. The finite index set makes multiplicity explicit.
The theorem of the cited paper is not proved by this definition. -/
def V15HasanalizadeShenWongPairCountInput
    (d : ℝ) (n : ℕ) (zeros : ℕ → ℂ) : Prop :=
  ∀ T : ℝ, 1 ≤ T → ∃ s : Finset ℕ,
    (∀ i, i ∈ s ↔ |(zeros i).im| ≤ T) ∧
      (s.card : ℝ) ≤
        T / Real.pi * (Real.log d + (n : ℝ) *
          (Real.log T - Real.log (2 * Real.pi * Real.exp 1))) +
        (228 / 1000 : ℝ) * (Real.log d + (n : ℝ) * Real.log T) +
        (23108 / 1000 : ℝ) * n + 4520 / 1000

/-- The same published inequality for all zero *occurrences*, so repeated
zeros remain distinct elements of `ι`. This models the paper's phrase
"counted with multiplicity" without equating a set of complex values with a
multiset of zero occurrences. -/
def V15HasanalizadeShenWongAllZeroCountInput
    (d : ℝ) (n : ℕ) {ι : Type*} (zeroValue : ι → ℂ) : Prop :=
  ∀ T : ℝ, 1 ≤ T → ∃ s : Finset ι,
    (∀ i, i ∈ s ↔ |(zeroValue i).im| ≤ T) ∧
      (s.card : ℝ) ≤
        T / Real.pi * (Real.log d + (n : ℝ) *
          (Real.log T - Real.log (2 * Real.pi * Real.exp 1))) +
        (228 / 1000 : ℝ) * (Real.log d + (n : ℝ) * Real.log T) +
        (23108 / 1000 : ℝ) * n + 4520 / 1000

/-- The upper half of Corollary 1.2, retaining its literal logarithm, for a
type of critical-strip zero occurrences. -/
def V15HasanalizadeShenWongPublishedCountInput
    (d : ℝ) (n : ℕ) {ι : Type*} (zeroValue : ι → ℂ) : Prop :=
  ∀ T : ℝ, 1 ≤ T → ∃ s : Finset ι,
    (∀ i, i ∈ s ↔ |(zeroValue i).im| ≤ T) ∧
      (s.card : ℝ) ≤
        T / Real.pi *
          Real.log (d * (T / (2 * Real.pi * Real.exp 1)) ^ n) +
        (228 / 1000 : ℝ) * (Real.log d + (n : ℝ) * Real.log T) +
        (23108 / 1000 : ℝ) * n + 4520 / 1000

/-- Corollary 1.2 in its actual absolute-error form. This is an external
analytic premise, not a theorem about a constructed Dedekind-zeta function. -/
def V15HasanalizadeShenWongCorollary12Input
    (d : ℝ) (n : ℕ) {ι : Type*} (zeroValue : ι → ℂ) : Prop :=
  ∀ T : ℝ, 1 ≤ T → ∃ s : Finset ι,
    (∀ i, i ∈ s ↔ |(zeroValue i).im| ≤ T) ∧
      |(s.card : ℝ) - T / Real.pi *
        Real.log (d * (T / (2 * Real.pi * Real.exp 1)) ^ n)| ≤
        (228 / 1000 : ℝ) * (Real.log d + (n : ℝ) * Real.log T) +
        (23108 / 1000 : ℝ) * n + 4520 / 1000

/-- Only the upper half of the published two-sided estimate is needed. -/
theorem v15HasanalizadeShenWong_publishedUpper_of_corollary12
    (d : ℝ) (n : ℕ) {ι : Type*} (zeroValue : ι → ℂ)
    (hCorollary : V15HasanalizadeShenWongCorollary12Input d n zeroValue) :
    V15HasanalizadeShenWongPublishedCountInput d n zeroValue := by
  intro T hT
  obtain ⟨s, hs, hBound⟩ := hCorollary T hT
  refine ⟨s, hs, ?_⟩
  have hUpper := (abs_le.mp hBound).2
  linarith

/-- An injective enumeration of conjugate-pair representatives inherits the
all-zero count, with multiplicities respected by the occurrence type. -/
theorem v15HasanalizadeShenWong_pairCount_of_allZeroCount
    (d : ℝ) (n : ℕ) {ι : Type*} (zeroValue : ι → ℂ)
    (representative : ℕ → ι) (hInjective : Function.Injective representative)
    (hAll : V15HasanalizadeShenWongAllZeroCountInput d n zeroValue) :
    V15HasanalizadeShenWongPairCountInput d n (zeroValue ∘ representative) := by
  classical
  intro T hT
  obtain ⟨s, hs, hCard⟩ := hAll T hT
  let pre := s.preimage representative hInjective.injOn
  refine ⟨pre, ?_, ?_⟩
  · intro i
    exact (Finset.mem_preimage).trans (hs (representative i))
  · have hMap : pre.map ⟨representative, hInjective⟩ ⊆ s := by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
      exact Finset.mem_preimage.mp hj
    have hCardLe : pre.card ≤ s.card := by
      simpa using Finset.card_le_card hMap
    exact (by exact_mod_cast hCardLe : (pre.card : ℝ) ≤ (s.card : ℝ)).trans hCard

/-- The exact logarithm in the published main term expands as used above. -/
theorem v15HasanalizadeShenWong_log_main_term
    (d T : ℝ) (n : ℕ) (hd : 0 < d) (hT : 0 < T) :
    Real.log (d * (T / (2 * Real.pi * Real.exp 1)) ^ n) =
      Real.log d + (n : ℝ) *
        (Real.log T - Real.log (2 * Real.pi * Real.exp 1)) := by
  have hden : (2 * Real.pi * Real.exp 1 : ℝ) ≠ 0 := by positivity
  rw [Real.log_mul (ne_of_gt hd) (pow_ne_zero _ (div_ne_zero (ne_of_gt hT) hden)),
    Real.log_pow, Real.log_div (ne_of_gt hT) hden]

/-- The source's literal main term is exactly the expanded form used for the
elementary bounds below. -/
theorem v15HasanalizadeShenWong_allZeroCount_of_published
    (d : ℝ) (n : ℕ) {ι : Type*} (zeroValue : ι → ℂ) (hd : 0 < d)
    (hPublished : V15HasanalizadeShenWongPublishedCountInput d n zeroValue) :
    V15HasanalizadeShenWongAllZeroCountInput d n zeroValue := by
  intro T hT
  obtain ⟨s, hs, hCard⟩ := hPublished T hT
  refine ⟨s, hs, ?_⟩
  rw [v15HasanalizadeShenWong_log_main_term d T n hd (by linarith)] at hCard
  exact hCard

/-- A source-range `T ≥ 1` zero count implies a deliberately coarse
`T log (2 + T)` count with elementary, explicit constants. -/
theorem v15OdlyzkoZeroCountLargeHeightLogBound_of_HSW
    (d : ℝ) (n : ℕ) (zeros : ℕ → ℂ) (hd : 1 ≤ d)
    (hCount : V15HasanalizadeShenWongPairCountInput d n zeros) :
    V15OdlyzkoZeroCountLargeHeightLogBound
      (24 * (n : ℝ) + 5) (3 * (Real.log d + n)) zeros := by
  intro T hT
  obtain ⟨s, hs, hCard⟩ := hCount T hT
  refine ⟨s, hs, ?_⟩
  have hdpos : 0 < d := by linarith
  have hL : 0 ≤ Real.log d := Real.log_nonneg hd
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hPi : 1 ≤ Real.pi := by linarith [Real.one_le_pi_div_two]
  have hPiPos : 0 < Real.pi := Real.pi_pos
  have hExp : 1 ≤ Real.exp 1 := by
    simpa only [Real.exp_zero] using
      Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 1 by norm_num)
  have hDen : 1 ≤ 2 * Real.pi * Real.exp 1 := by
    have hTwoPi : 1 ≤ 2 * Real.pi := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hTwoPi) (sub_nonneg.mpr hExp)]
  have hc : 0 ≤ Real.log (2 * Real.pi * Real.exp 1) := Real.log_nonneg hDen
  have hl : 0 ≤ Real.log T := Real.log_nonneg hT
  have hu : Real.log T ≤ Real.log (2 + T) :=
    Real.log_le_log (by linarith) (by linarith)
  have huLower : (2 / 3 : ℝ) ≤ Real.log (2 + T) := by
    have hThree : Real.log 3 ≤ Real.log (2 + T) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hThreeLower : (2 / 3 : ℝ) ≤ Real.log 3 := by
      have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 by norm_num)
      norm_num at h ⊢
      exact h
    exact hThreeLower.trans hThree
  let q : ℝ := Real.log d + (n : ℝ) * Real.log T
  let r : ℝ := Real.log d + (n : ℝ) * Real.log (2 + T)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hqr : q ≤ r := by
    dsimp [q, r]
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hu)]
  have hr : 0 ≤ r := hq.trans hqr
  have hMain :
      T / Real.pi * (q - (n : ℝ) * Real.log (2 * Real.pi * Real.exp 1)) ≤
        T * q := by
    have hDiv : T / Real.pi ≤ T := by
      apply (div_le_iff₀ hPiPos).2
      nlinarith [mul_nonneg (sub_nonneg.mpr hPi) (by linarith : 0 ≤ T)]
    calc
      _ ≤ T / Real.pi * q :=
        mul_le_mul_of_nonneg_left (sub_le_self _ (mul_nonneg hn hc))
          (div_nonneg (by linarith) hPiPos.le)
      _ ≤ T * q := mul_le_mul_of_nonneg_right hDiv hq
  have hNumerical :
      (228 / 1000 : ℝ) * q + (23108 / 1000 : ℝ) * n + 4520 / 1000 ≤
        q + 24 * n + 5 := by
    nlinarith
  have hFirst : (s.card : ℝ) ≤ (T + 1) * q + 24 * n + 5 := by
    dsimp [q] at hCard ⊢
    nlinarith [hMain, hNumerical]
  have hSecond : (T + 1) * q ≤ 2 * T * r := by
    have hOne : T + 1 ≤ 2 * T := by linarith
    calc
      _ ≤ (T + 1) * r := mul_le_mul_of_nonneg_left hqr (by linarith)
      _ ≤ (2 * T) * r := mul_le_mul_of_nonneg_right hOne hr
      _ = 2 * T * r := by ring
  have hThird : 2 * T * r ≤ 3 * (Real.log d + n) * T * Real.log (2 + T) := by
    dsimp [r]
    have hTL : 0 ≤ T * Real.log d := mul_nonneg (by linarith) hL
    have hNU : 0 ≤ (n : ℝ) * T * Real.log (2 + T) := by positivity
    have hKey : 0 ≤ (T * Real.log d) * (3 * Real.log (2 + T) - 2) :=
      mul_nonneg hTL (by linarith)
    nlinarith
  nlinarith [hFirst, hSecond, hThird]

/-- The cited `T ≥ 1` estimate also supplies the all-height quadratic count
used by the paired-zero summability criterion. No analytic number-theory
claim is silently introduced: the cited count remains the premise. -/
theorem v15OdlyzkoZeroCountBound_of_HSW
    (d : ℝ) (n : ℕ) (zeros : ℕ → ℂ) (hd : 1 ≤ d)
    (hCount : V15HasanalizadeShenWongPairCountInput d n zeros) :
    V15OdlyzkoZeroCountBound
      ((24 * (n : ℝ) + 5) + 3 * (Real.log d + n) * Real.log 3 +
        3 * (Real.log d + n)) zeros := by
  have hB : 0 ≤ 3 * (Real.log d + (n : ℝ)) := by
    have := Real.log_nonneg hd
    positivity
  exact v15OdlyzkoZeroCountBound_of_logBound zeros _ _
    (by
      have := Real.log_nonneg hd
      have := Real.log_nonneg (show (1 : ℝ) ≤ 3 by norm_num)
      positivity)
    hB
    (v15OdlyzkoZeroCountLogBound_of_largeHeight zeros _ _ hB
      (v15OdlyzkoZeroCountLargeHeightLogBound_of_HSW d n zeros hd hCount))

/-- Direct source-to-criterion bridge, conditional only on the published
zero-count inequality for actual zero occurrences and an injective choice of
pair representatives. -/
theorem v15OdlyzkoZeroCountBound_of_HSW_published
    (d : ℝ) (n : ℕ) {ι : Type*} (zeroValue : ι → ℂ)
    (representative : ℕ → ι) (hd : 1 ≤ d)
    (hInjective : Function.Injective representative)
    (hCorollary : V15HasanalizadeShenWongCorollary12Input d n zeroValue) :
    V15OdlyzkoZeroCountBound
      ((24 * (n : ℝ) + 5) + 3 * (Real.log d + n) * Real.log 3 +
        3 * (Real.log d + n)) (zeroValue ∘ representative) := by
  apply v15OdlyzkoZeroCountBound_of_HSW d n _ hd
  exact v15HasanalizadeShenWong_pairCount_of_allZeroCount d n zeroValue
    representative hInjective
    (v15HasanalizadeShenWong_allZeroCount_of_published d n zeroValue
      (by linarith)
      (v15HasanalizadeShenWong_publishedUpper_of_corollary12 d n zeroValue
        hCorollary))

end
end TraceEuclidean
