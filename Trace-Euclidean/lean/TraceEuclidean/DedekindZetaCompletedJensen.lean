import TraceEuclidean.DedekindZetaConstructed
import TraceEuclidean.DedekindZetaCompletion
import Mathlib.Analysis.Complex.JensenFormula

/-!
# Jensen counting through the completed Dedekind zeta

The theta--Mellin construction gives an entire pole-removed completed zeta.
On the positive half-plane it is the HSW completion of the already constructed
ordinary regularization.  Consequently the two functions have the same zeros,
with the same analytic multiplicities, in the open critical strip.

This file lets Jensen's inequality act directly on the completed entire
function.  A growth estimate for the Mellin-tail formula can therefore be used
without first proving a global bound for the reciprocal Gamma factors in the
ordinary regularization.
-/

namespace TraceEuclidean

noncomputable section

open Filter Set Metric MeromorphicOn
open scoped Topology

variable {K : Type*} [Field K] [NumberField K]

/-- The multiplier used in the HSW completion is exactly `s * ZInfty(s)`. -/
theorem completedMultiplier_eq_s_mul_ZInfty (K : Type*) [Field K]
    [NumberField K] (s : ℂ) :
    completedMultiplier K s = s * DedekindZeta.ZInfty K s := by
  have hdisc :
      (((|(NumberField.discr K : ℝ)| : ℝ) : ℂ)) =
        (((|NumberField.discr K| : ℤ) : ℂ)) := by
    norm_cast
  unfold completedMultiplier completedArchimedeanFactor
  unfold DedekindZeta.ZInfty DedekindZeta.LReal DedekindZeta.LComplex
  unfold Complex.Gammaℝ Complex.Gammaℂ
  rw [hdisc]
  ring_nf

/-- On `Re(s) > 0`, completing the constructed ordinary regularization
recovers the pole-removed entire completed zeta exactly. -/
theorem completedFromConstructed_eq_poleRemoved_of_re_pos
    {s : ℂ} (hs : 0 < s.re) :
    completedFromRegularization K
        (constructedDedekindZetaRegularization K) s =
      DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s := by
  unfold completedFromRegularization
  change completedMultiplier K s *
      (DedekindZeta.ZetaRegularization.inverseCompletedMultiplier K s *
        DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s) = _
  rw [completedMultiplier_eq_s_mul_ZInfty]
  have hcancel :=
    DedekindZeta.ZetaRegularization.inverseCompletedMultiplier_mul_of_re_pos K hs
  calc
    _ = (DedekindZeta.ZetaRegularization.inverseCompletedMultiplier K s *
          (s * DedekindZeta.ZInfty K s)) *
        DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s := by ring
    _ = _ := by rw [hcancel, one_mul]

/-- The entire completed function and the constructed ordinary
regularization have the same analytic zero order throughout the open
critical strip (in fact, throughout the positive half-plane). -/
theorem completedPoleRemoved_zero_order_eq_constructed
    {s : ℂ} (hs : 0 < s.re) :
    analyticOrderNatAt
        (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s =
      analyticOrderNatAt
        (constructedDedekindZetaRegularization K).value s := by
  have hOpen : {z : ℂ | 0 < z.re} ∈ 𝓝 s :=
    (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hs
  have hEq :
      DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K =ᶠ[𝓝 s]
        completedFromRegularization K
          (constructedDedekindZetaRegularization K) := by
    filter_upwards [hOpen] with z hz
    exact (completedFromConstructed_eq_poleRemoved_of_re_pos
      (K := K) hz).symm
  calc
    analyticOrderNatAt
        (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s =
      analyticOrderNatAt
        (completedFromRegularization K
          (constructedDedekindZetaRegularization K)) s := by
        unfold analyticOrderNatAt
        rw [analyticOrderAt_congr hEq]
    _ = analyticOrderNatAt
        (constructedDedekindZetaRegularization K).value s :=
      completed_zero_order_eq_regularized_zero_order K
        (constructedDedekindZetaRegularization K) hs

/-- The completed pole-removed function is not identically zero. -/
theorem completedZetaPoleRemoved_exists_nonzero :
    ∃ s : ℂ,
      DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s ≠ 0 := by
  let Z := constructedDedekindZetaRegularization K
  have hlimit := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  have hres : (NumberField.dedekindZeta_residue K : ℂ) ≠ 0 := by
    exact_mod_cast NumberField.dedekindZeta_residue_ne_zero K
  have hne : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ),
      ((t : ℂ) - 1) * NumberField.dedekindZeta K t ≠ 0 :=
    hlimit.eventually_ne hres
  obtain ⟨t, htne, ht⟩ := (hne.and self_mem_nhdsWithin).exists
  have htpos : 0 < (t : ℂ).re := by simpa using (lt_trans (by norm_num) ht)
  refine ⟨(t : ℂ), ?_⟩
  rw [← completedFromConstructed_eq_poleRemoved_of_re_pos
    (K := K) htpos]
  unfold completedFromRegularization
  apply mul_ne_zero (completedMultiplier_ne_zero K htpos)
  change Z.value (t : ℂ) ≠ 0
  rw [Z.agrees_right (t : ℂ) (by simpa using ht)]
  exact htne

/-- The analytic order of the completed pole-removed function is finite at
every point. -/
theorem completedZetaPoleRemoved_order_ne_top (s : ℂ) :
    analyticOrderAt
      (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s ≠ ⊤ := by
  intro htop
  have hzero :=
    (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s
      (fun z ↦
        DedekindZeta.GlobalContinuation.completedZetaPoleRemoved_analyticOn K
          z (mem_univ z))).mp htop
  obtain ⟨z, hz⟩ := completedZetaPoleRemoved_exists_nonzero (K := K)
  exact hz (congrFun hzero z)

private theorem completed_divisor_eq_zero_order_nat
    {B : Set ℂ} {z : ℂ} (hz : z ∈ B) :
    (divisor
        (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) B z : ℝ) =
      (analyticOrderNatAt
        (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) z : ℝ) := by
  have hAnalytic : AnalyticOnNhd ℂ
      (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) B :=
    (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved_analyticOn K).mono
      (subset_univ _)
  rw [hAnalytic.divisor_apply hz]
  rw [← Nat.cast_analyticOrderNatAt
    (completedZetaPoleRemoved_order_ne_top (K := K) z)]
  simp

/-- A compact set containing all ordinary strip-zero occurrences through
height `T` contains at least that many zeros of the entire completed function,
counted with analytic multiplicity. -/
theorem DedekindZetaZeroOccurrence.boundedSet_ncard_le_completed_divisor
    (T : ℝ) {B : Set ℂ} (hB : IsCompact B)
    (hContain : ∀ o : DedekindZetaZeroOccurrence
        (constructedDedekindZetaRegularization K),
      o ∈ DedekindZetaZeroOccurrence.boundedSet
          (constructedDedekindZetaRegularization K) T → o.value ∈ B) :
    ((DedekindZetaZeroOccurrence.boundedSet
        (constructedDedekindZetaRegularization K) T).ncard : ℝ) ≤
      ∑ᶠ z : ℂ, (divisor
        (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) B z : ℝ) := by
  classical
  let Z := constructedDedekindZetaRegularization K
  let F := DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K
  let E := DedekindZetaZeroOccurrence.boundedSet Z T
  let S := Function.support (divisor F B)
  have hE : E.Finite := DedekindZetaZeroOccurrence.boundedSet_finite Z T
  have hS : S.Finite := (divisor F B).finiteSupport hB
  letI : Fintype E := hE.fintype
  letI : Fintype S := hS.fintype
  let f : E → Σ s : S, Fin (analyticOrderNatAt F s.1) := fun o ↦
    ⟨⟨o.1.value, by
      apply Function.mem_support.mpr
      have hzB : o.1.value ∈ B := hContain o.1 o.2
      have hpos : 0 < analyticOrderNatAt F o.1.value := by
        rw [completedPoleRemoved_zero_order_eq_constructed
          (K := K) o.1.in_strip.1]
        change 0 < analyticOrderNatAt Z.value o.1.value
        exact lt_of_le_of_lt (Nat.zero_le o.1.2.val) o.1.2.isLt
      have hcast : (analyticOrderNatAt F o.1.value : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hpos)
      intro hdiv
      apply hcast
      have heq := completed_divisor_eq_zero_order_nat (K := K) hzB
      rw [hdiv] at heq
      simpa using heq.symm⟩,
      ⟨o.1.2.val, by
        rw [completedPoleRemoved_zero_order_eq_constructed
          (K := K) o.1.in_strip.1]
        change o.1.2.val < analyticOrderNatAt Z.value o.1.value
        exact o.1.2.isLt⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hpoint : a.1.1 = b.1.1 := Subtype.ext
      (congrArg (fun x : Σ s : S, Fin (analyticOrderNatAt F s.1) ↦ x.1.1) hab)
    have hslot : a.1.2.val = b.1.2.val :=
      congrArg (fun x : Σ s : S, Fin (analyticOrderNatAt F s.1) ↦ x.2.val) hab
    apply Subtype.ext
    apply Sigma.ext hpoint
    have htype :
        analyticOrderNatAt Z.value a.1.1 =
          analyticOrderNatAt Z.value b.1.1 :=
      congrArg (fun s : {z : ℂ // 0 < z.re ∧ z.re < 1} ↦
        analyticOrderNatAt Z.value s.1) hpoint
    exact (Fin.heq_ext_iff htype).2 hslot
  have hCard : E.ncard ≤
      Fintype.card (Σ s : S, Fin (analyticOrderNatAt F s.1)) := by
    simpa [Set.ncard_eq_toFinset_card] using Fintype.card_le_of_injective f hf
  have hSupport :
      Function.support (fun z : ℂ ↦ (divisor F B z : ℝ)) ⊆ S := by
    intro z hz
    apply Function.mem_support.mpr
    exact_mod_cast Function.mem_support.mp hz
  have hSum :
      (∑ᶠ z : ℂ, (divisor F B z : ℝ)) =
        ∑ z : S, (analyticOrderNatAt F z.1 : ℝ) := by
    rw [finsum_eq_sum_of_support_subset _
      (show Function.support (fun z : ℂ ↦ (divisor F B z : ℝ)) ⊆
        hS.toFinset from by simpa using hSupport)]
    calc
      _ = ∑ z ∈ hS.toFinset, (analyticOrderNatAt F z : ℝ) := by
        apply Finset.sum_congr rfl
        intro z hz
        have hdiv : divisor F B z ≠ 0 :=
          Function.mem_support.mp (hS.mem_toFinset.mp hz)
        exact completed_divisor_eq_zero_order_nat (K := K)
          ((divisor F B).supportWithinDomain hdiv)
      _ = ∑ z : S, (analyticOrderNatAt F z.1 : ℝ) := by
        simp only [Set.Finite.toFinset, Set.toFinset, Finset.sum_map]
        rfl
  have hSigma :
      Fintype.card (Σ s : S, Fin (analyticOrderNatAt F s.1)) =
        ∑ s : S, analyticOrderNatAt F s.1 := by
    simp [Fintype.card_sigma]
  rw [hSum]
  have hReal : (E.ncard : ℝ) ≤
      (Fintype.card (Σ s : S, Fin (analyticOrderNatAt F s.1)) : ℝ) := by
    exact_mod_cast hCard
  rw [hSigma] at hReal
  simpa only [Nat.cast_sum] using hReal

/-- Jensen's inequality applied to the entire completed function bounds the
ordinary strip-zero occurrences, because their multiplicities agree in the
critical strip. -/
theorem DedekindZetaZeroOccurrence.boundedSet_ncard_le_completed_jensen
    (T : ℝ) {c : ℂ} {r R M : ℝ}
    (hr : 0 < |r|) (hrR : |r| < |R|) (hM : 1 ≤ M)
    (hc : DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K c ≠ 0)
    (hContain : ∀ o : DedekindZetaZeroOccurrence
        (constructedDedekindZetaRegularization K),
      o ∈ DedekindZetaZeroOccurrence.boundedSet
          (constructedDedekindZetaRegularization K) T →
        o.value ∈ closedBall c |r|)
    (hBound : ∀ z ∈ sphere c |R|,
      ‖DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K z‖ ≤ M) :
    ((DedekindZetaZeroOccurrence.boundedSet
        (constructedDedekindZetaRegularization K) T).ncard : ℝ) ≤
      Real.log (M /
        ‖DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K c‖) /
          Real.log (R / r) := by
  let F := DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K
  have hAnalytic : AnalyticOnNhd ℂ F (closedBall c |R|) :=
    (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved_analyticOn K).mono
      (subset_univ _)
  have hDivisor :=
    DedekindZetaZeroOccurrence.boundedSet_ncard_le_completed_divisor
      (K := K) T (isCompact_closedBall c |r|) hContain
  have hCast :
      (∑ᶠ z : ℂ, (divisor F (closedBall c |r|) z : ℝ)) =
        ((∑ᶠ z : ℂ, divisor F (closedBall c |r|) z : ℤ) : ℝ) := by
    exact (map_finsum (Int.castRingHom ℝ)
      ((divisor F (closedBall c |r|)).finiteSupport
        (isCompact_closedBall c |r|))).symm
  calc
    _ ≤ ∑ᶠ z : ℂ, (divisor F (closedBall c |r|) z : ℝ) := hDivisor
    _ = ((∑ᶠ z : ℂ, divisor F (closedBall c |r|) z : ℤ) : ℝ) := hCast
    _ ≤ _ := hAnalytic.sum_divisor_le hr hrR hM hc hBound

private theorem completed_boundedSet_mem_explicit_ball
    {T : ℝ} (c : ℂ)
    (o : DedekindZetaZeroOccurrence
      (constructedDedekindZetaRegularization K))
    (ho : o ∈ DedekindZetaZeroOccurrence.boundedSet
      (constructedDedekindZetaRegularization K) T) :
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

/-- A completed-zeta bound on the circle of twice the elementary containing
radius gives the corresponding Jensen bound. -/
theorem DedekindZetaZeroOccurrence.boundedSet_ncard_le_completed_circle_growth
    {T : ℝ} (hT : 0 ≤ T) {c : ℂ} {M : ℝ} (hM : 1 ≤ M)
    (hc : DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K c ≠ 0)
    (hGrowth : ∀ z ∈ sphere c (2 * (‖c‖ + T + 2)),
      ‖DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K z‖ ≤ M) :
    ((DedekindZetaZeroOccurrence.boundedSet
        (constructedDedekindZetaRegularization K) T).ncard : ℝ) ≤
      Real.log (M /
        ‖DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K c‖) /
          Real.log 2 := by
  let r : ℝ := ‖c‖ + T + 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hR : 0 < 2 * r := by positivity
  have hrR : |r| < |2 * r| := by rw [abs_of_pos hr, abs_of_pos hR]; linarith
  have hContain : ∀ o : DedekindZetaZeroOccurrence
      (constructedDedekindZetaRegularization K),
      o ∈ DedekindZetaZeroOccurrence.boundedSet
          (constructedDedekindZetaRegularization K) T →
        o.value ∈ closedBall c |r| := by
    intro o ho
    rw [abs_of_pos hr]
    exact completed_boundedSet_mem_explicit_ball (K := K) c o ho
  have hBound : ∀ z ∈ sphere c |2 * r|,
      ‖DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K z‖ ≤ M := by
    simpa only [abs_of_pos hR] using hGrowth
  have hJensen :=
    DedekindZetaZeroOccurrence.boundedSet_ncard_le_completed_jensen
      (K := K) T (r := r) (R := 2 * r) (M := M)
        (by simpa only [abs_of_pos hr] using hr) hrR hM hc hContain hBound
  have hRatio : 2 * r / r = 2 := by field_simp
  simpa only [hRatio] using hJensen

/-- Quadratic exponential growth of the entire completed function on the
explicit circles gives the quadratic zero-count input for the constructed
ordinary regularization. -/
theorem DedekindZetaZeroOccurrence.quadraticCount_of_completed_circle_growth
    (c : ℂ)
    (hc : DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K c ≠ 0)
    (A : ℝ) (hA : 0 ≤ A)
    (hGrowth : ∀ T : ℝ, 0 ≤ T →
      ∀ z ∈ sphere c (2 * (‖c‖ + T + 2)),
        ‖DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K z‖ ≤
          Real.exp (A * (1 + T) ^ 2)) :
    DedekindZetaZeroOccurrence.QuadraticCountInput
      (constructedDedekindZetaRegularization K)
      ((A + |Real.log
        ‖DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K c‖|) /
          Real.log 2) := by
  intro T hT
  have hExp : 1 ≤ Real.exp (A * (1 + T) ^ 2) :=
    Real.one_le_exp (mul_nonneg hA (sq_nonneg _))
  have hJensen :=
    DedekindZetaZeroOccurrence.boundedSet_ncard_le_completed_circle_growth
      (K := K) hT hExp hc (hGrowth T hT)
  have hNorm :
      ‖DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K c‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hc
  rw [Real.log_div (Real.exp_ne_zero _) hNorm, Real.log_exp] at hJensen
  have hSq : 1 ≤ (1 + T) ^ 2 := by nlinarith
  have hAbs :
      -Real.log ‖DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K c‖ ≤
        |Real.log
          ‖DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K c‖| :=
    neg_le_abs _
  have hAbsMul :
      |Real.log
          ‖DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K c‖| ≤
        |Real.log
          ‖DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K c‖| *
            (1 + T) ^ 2 :=
    le_mul_of_one_le_right (abs_nonneg _) hSq
  have hNumerator :
      A * (1 + T) ^ 2 -
          Real.log
            ‖DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K c‖ ≤
        (A + |Real.log
          ‖DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K c‖|) *
            (1 + T) ^ 2 := by
    nlinarith
  have hLog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    _ ≤ (A * (1 + T) ^ 2 -
        Real.log
          ‖DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K c‖) /
            Real.log 2 := hJensen
    _ ≤ ((A + |Real.log
        ‖DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K c‖|) *
          (1 + T) ^ 2) / Real.log 2 :=
      (div_le_div_iff_of_pos_right hLog2).mpr hNumerator
    _ = ((A + |Real.log
        ‖DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K c‖|) /
          Real.log 2) * (1 + T) ^ 2 := by ring

/-- The completed-function growth route supplies absolute convergence of the
Odlyzko zero transform for the actual constructed regularization. -/
theorem DedekindZetaZeroOccurrence.phi_summable_of_completed_circle_growth
    (c : ℂ)
    (hc : DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K c ≠ 0)
    (A : ℝ) (hA : 0 ≤ A)
    (hGrowth : ∀ T : ℝ, 0 ≤ T →
      ∀ z ∈ sphere c (2 * (‖c‖ + T + 2)),
        ‖DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K z‖ ≤
          Real.exp (A * (1 + T) ^ 2)) :
    Summable (fun o : DedekindZetaZeroOccurrence
      (constructedDedekindZetaRegularization K) ↦
        odlyzkoPhi o.value) := by
  let C := (A + |Real.log
    ‖DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K c‖|) /
      Real.log 2
  have hC : 0 ≤ C := div_nonneg (add_nonneg hA (abs_nonneg _))
    (le_of_lt (Real.log_pos (by norm_num)))
  exact DedekindZetaZeroOccurrence.phi_summable_of_quadratic_count
    (constructedDedekindZetaRegularization K) C hC
    (DedekindZetaZeroOccurrence.quadraticCount_of_completed_circle_growth
      (K := K) c hc A hA hGrowth)

/-- The remaining growth premise for Table 4 can be stated entirely for the
theta--Mellin completed function; no reciprocal-Gamma growth premise is
needed. -/
theorem odlyzkoTable4_of_constructed_completed_circle_growth
    (center : CodedNumberField → ℂ)
    (hCenter : ∀ K,
      DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K.1
        (center K) ≠ 0)
    (A : CodedNumberField → ℝ) (hA : ∀ K, 0 ≤ A K)
    (hGrowth : ∀ K : CodedNumberField, ∀ T : ℝ, 0 ≤ T →
      ∀ z ∈ sphere (center K) (2 * (‖center K‖ + T + 2)),
        ‖DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K.1 z‖ ≤
          Real.exp (A K * (1 + T) ^ 2))
    (hFormula : OdlyzkoExplicitFormulaInput
      (fun K ↦ (∑' o : DedekindZetaZeroOccurrence
        (constructedRegularizationFamily K),
          odlyzkoPhi o.value).re))
    (hAB : OdlyzkoABIntegralCertificate) :
    OdlyzkoTable4ExplicitCorrectionInput := by
  let C : CodedNumberField → ℝ := fun K ↦
    (A K + |Real.log
      ‖DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K.1
        (center K)‖|) / Real.log 2
  apply odlyzkoTable4ExplicitCorrectionInput_of_unorderedZeros
    constructedRegularizationFamily C
  · intro K
    exact div_nonneg (add_nonneg (hA K) (abs_nonneg _))
      (le_of_lt (Real.log_pos (by norm_num)))
  · intro K
    exact DedekindZetaZeroOccurrence.quadraticCount_of_completed_circle_growth
        (K := K.1) (center K) (hCenter K) (A K) (hA K) (hGrowth K)
  · exact hFormula
  · exact hAB

end
end TraceEuclidean
