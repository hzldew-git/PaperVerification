import TraceEuclidean.V15DedekindZetaUnorderedZeros
import Mathlib.Analysis.Complex.JensenFormula

/-!
# Jensen's inequality for actual Dedekind-zeta zero occurrences

The first bridge identifies the analytic zero order of a hypothetical entire
regularization with the value of its divisor inside a closed ball. No growth
estimate or analytic continuation is asserted here.
-/

namespace TraceEuclidean

noncomputable section

open Filter Set Metric MeromorphicOn
open scoped Topology

variable {K : Type*} [Field K] [NumberField K]

private theorem divisor_eq_zero_order_nat
    (Z : V15DedekindZetaRegularization K) {B : Set ℂ} {z : ℂ}
    (hz : z ∈ B) :
    (divisor Z.value B z : ℝ) = (analyticOrderNatAt Z.value z : ℝ) := by
  have hAnalytic : AnalyticOnNhd ℂ Z.value B := Z.analytic.mono (subset_univ _)
  rw [hAnalytic.divisor_apply hz]
  have hOrder := Z.order_ne_top z
  rw [← Nat.cast_analyticOrderNatAt hOrder]
  simp

/-- A ball containing all strip-zero occurrences through height `T` also
contains at least that many zeros in its divisor, counted with analytic
multiplicity. This is the exact bridge needed for Jensen's inequality. -/
theorem V15DedekindZetaZeroOccurrence.boundedSet_ncard_le_divisor
    (Z : V15DedekindZetaRegularization K) (T : ℝ) {B : Set ℂ}
    (hB : IsCompact B)
    (hContain : ∀ o : V15DedekindZetaZeroOccurrence Z,
      o ∈ V15DedekindZetaZeroOccurrence.boundedSet Z T → o.value ∈ B) :
    ((V15DedekindZetaZeroOccurrence.boundedSet Z T).ncard : ℝ) ≤
      ∑ᶠ z : ℂ, (divisor Z.value B z : ℝ) := by
  classical
  let E := V15DedekindZetaZeroOccurrence.boundedSet Z T
  let S := B ∩ Z.zeroSet
  have hE : E.Finite := V15DedekindZetaZeroOccurrence.boundedSet_finite Z T
  have hS : S.Finite := Z.finite_zeros_in_compact hB
  letI : Fintype E := hE.fintype
  letI : Fintype S := hS.fintype
  let f : E → Σ s : S, Fin (analyticOrderNatAt Z.value s.1) := fun o ↦
    ⟨⟨o.1.value, ⟨hContain o.1 o.2, o.1.is_zero⟩⟩, o.1.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hpoint : a.1.1 = b.1.1 := Subtype.ext
      (congrArg (fun x : Σ s : S, Fin (analyticOrderNatAt Z.value s.1) ↦ x.1.1) hab)
    have hslot : HEq a.1.2 b.1.2 := (Sigma.mk.inj_iff.mp hab).2
    exact Subtype.ext (Sigma.ext hpoint hslot)
  have hCard : E.ncard ≤ Fintype.card (Σ s : S, Fin (analyticOrderNatAt Z.value s.1)) := by
    simpa [Set.ncard_eq_toFinset_card] using Fintype.card_le_of_injective f hf
  have hSupport : Function.support (fun z : ℂ ↦ (divisor Z.value B z : ℝ)) ⊆ S := by
    intro z hz
    have hDivisor : divisor Z.value B z ≠ 0 := by
      exact_mod_cast (Function.mem_support.mp hz)
    have hzB : z ∈ B := (divisor Z.value B).supportWithinDomain
      (Function.mem_support.mpr hDivisor)
    have hOrder : analyticOrderNatAt Z.value z ≠ 0 := by
      intro hzero
      have hCast := divisor_eq_zero_order_nat Z (B := B) hzB
      have hCastZero : (divisor Z.value B z : ℝ) = 0 := by
        simpa only [hzero, Nat.cast_zero] using hCast
      exact hDivisor (by exact_mod_cast hCastZero)
    exact ⟨hzB, apply_eq_zero_of_analyticOrderNatAt_ne_zero hOrder⟩
  have hSum :
      (∑ᶠ z : ℂ, (divisor Z.value B z : ℝ)) =
        ∑ z : S, (analyticOrderNatAt Z.value z.1 : ℝ) := by
    rw [finsum_eq_sum_of_support_subset _
      (show Function.support (fun z : ℂ ↦ (divisor Z.value B z : ℝ)) ⊆
        hS.toFinset from by simpa using hSupport)]
    calc
      _ = ∑ z ∈ hS.toFinset, (analyticOrderNatAt Z.value z : ℝ) := by
        apply Finset.sum_congr rfl
        intro z hz
        exact divisor_eq_zero_order_nat Z (hS.mem_toFinset.mp hz).1
      _ = ∑ z : S, (analyticOrderNatAt Z.value z.1 : ℝ) := by
        simp only [Set.Finite.toFinset, Set.toFinset, Finset.sum_map]
        rfl
  have hSigma :
      Fintype.card (Σ s : S, Fin (analyticOrderNatAt Z.value s.1)) =
        ∑ s : S, analyticOrderNatAt Z.value s.1 := by
    simp [Fintype.card_sigma]
  rw [hSum]
  have hReal : (E.ncard : ℝ) ≤
      (Fintype.card (Σ s : S, Fin (analyticOrderNatAt Z.value s.1)) : ℝ) := by
    exact_mod_cast hCard
  rw [hSigma] at hReal
  simpa only [Nat.cast_sum] using hReal

/-- Jensen's inequality converts a circle bound on an entire Dedekind-zeta
regularization into a bound for actual strip zeros, counted with multiplicity. -/
theorem V15DedekindZetaZeroOccurrence.boundedSet_ncard_le_jensen
    (Z : V15DedekindZetaRegularization K) (T : ℝ)
    {c : ℂ} {r R M : ℝ}
    (hr : 0 < |r|) (hrR : |r| < |R|) (hM : 1 ≤ M)
    (hc : Z.value c ≠ 0)
    (hContain : ∀ o : V15DedekindZetaZeroOccurrence Z,
      o ∈ V15DedekindZetaZeroOccurrence.boundedSet Z T →
        o.value ∈ closedBall c |r|)
    (hBound : ∀ z ∈ sphere c |R|, ‖Z.value z‖ ≤ M) :
    ((V15DedekindZetaZeroOccurrence.boundedSet Z T).ncard : ℝ) ≤
      Real.log (M / ‖Z.value c‖) / Real.log (R / r) := by
  have hAnalytic : AnalyticOnNhd ℂ Z.value (closedBall c |R|) :=
    Z.analytic.mono (subset_univ _)
  have hDivisor := V15DedekindZetaZeroOccurrence.boundedSet_ncard_le_divisor
    Z T (isCompact_closedBall c |r|) hContain
  have hCast :
      (∑ᶠ z : ℂ, (divisor Z.value (closedBall c |r|) z : ℝ)) =
        ((∑ᶠ z : ℂ, divisor Z.value (closedBall c |r|) z : ℤ) : ℝ) := by
    exact (map_finsum (Int.castRingHom ℝ)
      ((divisor Z.value (closedBall c |r|)).finiteSupport
        (isCompact_closedBall c |r|))).symm
  calc
    _ ≤ ∑ᶠ z : ℂ, (divisor Z.value (closedBall c |r|) z : ℝ) := hDivisor
    _ = ((∑ᶠ z : ℂ, divisor Z.value (closedBall c |r|) z : ℤ) : ℝ) := hCast
    _ ≤ _ := hAnalytic.sum_divisor_le hr hrR hM hc hBound

/-- Every strip zero up to height `T` lies in an explicit ball about `c`. -/
private theorem boundedSet_mem_explicit_ball
    (Z : V15DedekindZetaRegularization K) {T : ℝ}
    (c : ℂ) (o : V15DedekindZetaZeroOccurrence Z)
    (ho : o ∈ V15DedekindZetaZeroOccurrence.boundedSet Z T) :
    o.value ∈ closedBall c (‖c‖ + T + 2) := by
  have hstrip := o.in_strip
  have hRe : |o.value.re| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hIm : |o.value.im| ≤ T := ho
  have hNorm : ‖o.value‖ ≤ 1 + T := by
    calc
      ‖o.value‖ ≤ |o.value.re| + |o.value.im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 1 + T := by linarith
  have hDist : dist o.value c ≤ ‖c‖ + T + 2 := by
    calc
      dist o.value c = ‖o.value - c‖ := dist_eq_norm _ _
      _ ≤ ‖o.value‖ + ‖c‖ := norm_sub_le _ _
      _ ≤ ‖c‖ + T + 2 := by linarith
  exact hDist

/-- The radius `‖c‖+T+2` absorbs all strip zeros of height at most `T`.
Consequently a bound on the circle of twice this radius yields a Jensen
bound without an additional geometric hypothesis. -/
theorem V15DedekindZetaZeroOccurrence.boundedSet_ncard_le_circle_growth
    (Z : V15DedekindZetaRegularization K) {T : ℝ} (hT : 0 ≤ T)
    {c : ℂ} {M : ℝ} (hM : 1 ≤ M) (hc : Z.value c ≠ 0)
    (hGrowth : ∀ z ∈ sphere c (2 * (‖c‖ + T + 2)), ‖Z.value z‖ ≤ M) :
    ((V15DedekindZetaZeroOccurrence.boundedSet Z T).ncard : ℝ) ≤
      Real.log (M / ‖Z.value c‖) / Real.log 2 := by
  let r : ℝ := ‖c‖ + T + 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hR : 0 < 2 * r := by positivity
  have hrR : |r| < |2 * r| := by rw [abs_of_pos hr, abs_of_pos hR]; linarith
  have hContain : ∀ o : V15DedekindZetaZeroOccurrence Z,
      o ∈ V15DedekindZetaZeroOccurrence.boundedSet Z T →
        o.value ∈ closedBall c |r| := by
    intro o ho
    rw [abs_of_pos hr]
    exact boundedSet_mem_explicit_ball Z c o ho
  have hBound : ∀ z ∈ sphere c |2 * r|, ‖Z.value z‖ ≤ M := by
    simpa only [abs_of_pos hR] using hGrowth
  have hJensen := V15DedekindZetaZeroOccurrence.boundedSet_ncard_le_jensen
    Z T (r := r) (R := 2 * r) (M := M)
      (by simpa only [abs_of_pos hr] using hr) hrR hM hc hContain hBound
  have hRatio : 2 * r / r = 2 := by field_simp
  simpa only [hRatio] using hJensen

/-- A uniform quadratic exponential bound on the indicated circles gives
the quadratic zero-count input used by the unordered zero sum. The entire
continuation and the growth estimate remain explicit hypotheses. -/
theorem V15DedekindZetaZeroOccurrence.quadraticCount_of_circle_growth
    (Z : V15DedekindZetaRegularization K) (c : ℂ)
    (hc : Z.value c ≠ 0) (A : ℝ) (hA : 0 ≤ A)
    (hGrowth : ∀ T : ℝ, 0 ≤ T →
      ∀ z ∈ sphere c (2 * (‖c‖ + T + 2)),
        ‖Z.value z‖ ≤ Real.exp (A * (1 + T) ^ 2)) :
    V15DedekindZetaZeroOccurrence.QuadraticCountInput Z
      ((A + |Real.log ‖Z.value c‖|) / Real.log 2) := by
  intro T hT
  have hExp : 1 ≤ Real.exp (A * (1 + T) ^ 2) :=
    Real.one_le_exp (mul_nonneg hA (sq_nonneg _))
  have hJensen :=
    V15DedekindZetaZeroOccurrence.boundedSet_ncard_le_circle_growth
      Z hT hExp hc (hGrowth T hT)
  have hNorm : ‖Z.value c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  rw [Real.log_div (Real.exp_ne_zero _) hNorm, Real.log_exp] at hJensen
  have hSq : 1 ≤ (1 + T) ^ 2 := by nlinarith
  have hAbs : -Real.log ‖Z.value c‖ ≤ |Real.log ‖Z.value c‖| :=
    neg_le_abs _
  have hAbsMul : |Real.log ‖Z.value c‖| ≤
      |Real.log ‖Z.value c‖| * (1 + T) ^ 2 :=
    le_mul_of_one_le_right (abs_nonneg _) hSq
  have hNumerator : A * (1 + T) ^ 2 - Real.log ‖Z.value c‖ ≤
      (A + |Real.log ‖Z.value c‖|) * (1 + T) ^ 2 := by
    nlinarith
  have hLog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    _ ≤ (A * (1 + T) ^ 2 - Real.log ‖Z.value c‖) / Real.log 2 :=
      hJensen
    _ ≤ ((A + |Real.log ‖Z.value c‖|) * (1 + T) ^ 2) / Real.log 2 :=
      (div_le_div_iff_of_pos_right hLog2).mpr hNumerator
    _ = ((A + |Real.log ‖Z.value c‖|) / Real.log 2) * (1 + T) ^ 2 := by
      ring

/-- The circle growth route supplies the absolute convergence required by
the Odlyzko zero term, without HSW's sharp numerical zero-count theorem. -/
theorem V15DedekindZetaZeroOccurrence.phi_summable_of_circle_growth
    (Z : V15DedekindZetaRegularization K) (c : ℂ)
    (hc : Z.value c ≠ 0) (A : ℝ) (hA : 0 ≤ A)
    (hGrowth : ∀ T : ℝ, 0 ≤ T →
      ∀ z ∈ sphere c (2 * (‖c‖ + T + 2)),
        ‖Z.value z‖ ≤ Real.exp (A * (1 + T) ^ 2)) :
    Summable (fun o : V15DedekindZetaZeroOccurrence Z ↦ v15OdlyzkoPhi o.value) := by
  let C := (A + |Real.log ‖Z.value c‖|) / Real.log 2
  have hC : 0 ≤ C := div_nonneg (add_nonneg hA (abs_nonneg _))
    (le_of_lt (Real.log_pos (by norm_num)))
  exact V15DedekindZetaZeroOccurrence.phi_summable_of_quadratic_count
    Z C hC (V15DedekindZetaZeroOccurrence.quadraticCount_of_circle_growth
      Z c hc A hA hGrowth)

/-- Jensen's count also provides the sign of the convergent zero
contribution required by the Table 4 bridge. -/
theorem V15DedekindZetaZeroOccurrence.phi_tsum_re_nonneg_of_circle_growth
    (Z : V15DedekindZetaRegularization K) (c : ℂ)
    (hc : Z.value c ≠ 0) (A : ℝ) (hA : 0 ≤ A)
    (hGrowth : ∀ T : ℝ, 0 ≤ T →
      ∀ z ∈ sphere c (2 * (‖c‖ + T + 2)),
        ‖Z.value z‖ ≤ Real.exp (A * (1 + T) ^ 2)) :
    0 ≤ (∑' o : V15DedekindZetaZeroOccurrence Z,
      v15OdlyzkoPhi o.value).re := by
  let C := (A + |Real.log ‖Z.value c‖|) / Real.log 2
  have hC : 0 ≤ C := div_nonneg (add_nonneg hA (abs_nonneg _))
    (le_of_lt (Real.log_pos (by norm_num)))
  exact V15DedekindZetaZeroOccurrence.phi_tsum_re_nonneg_of_quadratic_count
    Z C hC (V15DedekindZetaZeroOccurrence.quadraticCount_of_circle_growth
      Z c hc A hA hGrowth)

/-- The Table 4 bridge can use a coarse circle-growth estimate instead of
the HSW numerical zero count. The global continuation, this growth estimate,
and the source explicit formula are still named analytic inputs. -/
theorem v15_odlyzkoTable4ExplicitCorrectionInput_of_circle_growth
    (regularization : ∀ K : CodedNumberField,
      V15DedekindZetaRegularization K.1)
    (center : CodedNumberField → ℂ)
    (hCenter : ∀ K, (regularization K).value (center K) ≠ 0)
    (A : CodedNumberField → ℝ) (hA : ∀ K, 0 ≤ A K)
    (hGrowth : ∀ K : CodedNumberField, ∀ T : ℝ, 0 ≤ T →
      ∀ z ∈ sphere (center K) (2 * (‖center K‖ + T + 2)),
        ‖(regularization K).value z‖ ≤ Real.exp (A K * (1 + T) ^ 2))
    (hFormula : V15OdlyzkoExplicitFormulaInput
      (fun K ↦ (∑' o : V15DedekindZetaZeroOccurrence (regularization K),
        v15OdlyzkoPhi o.value).re))
    (hAB : V15OdlyzkoABIntegralCertificate) :
    V15OdlyzkoTable4ExplicitCorrectionInput := by
  apply v15_odlyzkoTable4ExplicitCorrectionInput_of_unorderedZeros regularization
    (fun K ↦ (A K + |Real.log ‖(regularization K).value (center K)‖|) / Real.log 2)
  · intro K
    exact div_nonneg (add_nonneg (hA K) (abs_nonneg _))
      (le_of_lt (Real.log_pos (by norm_num)))
  · intro K
    exact V15DedekindZetaZeroOccurrence.quadraticCount_of_circle_growth
      (regularization K) (center K) (hCenter K) (A K) (hA K) (hGrowth K)
  · exact hFormula
  · exact hAB

end
end TraceEuclidean
