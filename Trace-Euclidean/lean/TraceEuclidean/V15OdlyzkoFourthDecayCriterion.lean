import TraceEuclidean.V15OdlyzkoZeroSummability
import TraceEuclidean.V15OdlyzkoFourthRegularity
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# A fourth-derivative route to the Odlyzko transform bound

This module applies mathlib's iterated Fourier derivative theorem to the
source-normalized transform `v15OdlyzkoPhi`. The remaining analytic work is
reduced to a concrete, uniform regularity and integral certificate for the
exact compactly supported kernel, including the boundary weights.
-/

namespace TraceEuclidean

noncomputable section
open MeasureTheory FourierTransform Complex
open scoped RealInnerProductSpace
open scoped Topology
open scoped ComplexConjugate

/-- The source-exact tilted function is `C⁴` for every real exponential
weight, including the critical-strip endpoints. -/
theorem v15OdlyzkoTiltedF4_contDiff_four (a : ℝ) :
    ContDiff ℝ 4 (v15OdlyzkoTiltedF4 a) := by
  have hReal : ContDiff ℝ 4 (fun x : ℝ ↦ Real.exp (a * x) * v15OdlyzkoF4 x) :=
    ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul
      v15OdlyzkoF4_contDiff_four)
  change ContDiff ℝ 4 (fun x : ℝ ↦
    ((Real.exp (a * x) * v15OdlyzkoF4 x : ℝ) : ℂ))
  simpa only [Function.comp_def, Complex.ofRealCLM_apply]
    using Complex.ofRealCLM.contDiff.comp hReal

private theorem v15Fourth_iteratedDeriv_ofReal (f : ℝ → ℝ)
    (hf : ContDiff ℝ 4 f) (k : ℕ) (hk : k ≤ 4) :
    iteratedDeriv k (fun x : ℝ ↦ (f x : ℂ)) =
      fun x : ℝ ↦ ((iteratedDeriv k f x : ℝ) : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk' : k < 4 := Nat.lt_of_succ_le hk
      have hk'' : (k : WithTop ℕ∞) < 4 := by exact_mod_cast hk'
      rw [iteratedDeriv_succ, ih hk'.le]
      funext x
      have hd := (hf.differentiable_iteratedDeriv k hk'' x).hasDerivAt
      simpa only [iteratedDeriv_succ] using
        (HasDerivAt.ofReal_comp hd).deriv

private theorem v15OdlyzkoTiltedF4_fourth_deriv_formula (a x : ℝ) :
    iteratedDeriv 4 (v15OdlyzkoTiltedF4 a) x =
      ((∑ i ∈ Finset.range 5, (Nat.choose 4 i : ℝ) * a ^ i * Real.exp (a * x) *
        iteratedDeriv (4 - i) v15OdlyzkoF4 x : ℝ) : ℂ) := by
  let f : ℝ → ℝ := fun y ↦ Real.exp (a * y) * v15OdlyzkoF4 y
  have hf : ContDiff ℝ 4 f :=
    ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul
      v15OdlyzkoF4_contDiff_four)
  have hCast := congrFun (v15Fourth_iteratedDeriv_ofReal f hf 4 (by norm_num)) x
  have hMul : iteratedDeriv 4 f x =
      ∑ i ∈ Finset.range 5, (Nat.choose 4 i : ℝ) * a ^ i * Real.exp (a * x) *
        iteratedDeriv (4 - i) v15OdlyzkoF4 x := by
    dsimp [f]
    change iteratedDeriv 4 ((fun y : ℝ ↦ Real.exp (a * y)) * v15OdlyzkoF4) x = _
    rw [iteratedDeriv_mul (f := fun y : ℝ ↦ Real.exp (a * y))
      (g := v15OdlyzkoF4) (n := 4)
      (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).contDiffAt
      v15OdlyzkoF4_contDiff_four.contDiffAt]
    simp only [iteratedDeriv_exp_const_mul]
    congr 1
    ext i
    ring
  change iteratedDeriv 4 (fun y : ℝ ↦ ((f y : ℝ) : ℂ)) x = _
  rw [hCast, hMul]

private theorem v15OdlyzkoTiltedF4_continuous_joint :
    Continuous (fun p : ℝ × ℝ ↦ v15OdlyzkoTiltedF4 p.1 p.2) := by
  unfold v15OdlyzkoTiltedF4
  exact Complex.continuous_ofReal.comp
    ((Real.continuous_exp.comp (continuous_fst.mul continuous_snd)).mul
      (v15OdlyzkoF4_continuous.comp continuous_snd))

private theorem v15OdlyzkoTiltedF4_fourth_deriv_continuous_joint :
    Continuous (fun p : ℝ × ℝ ↦
      iteratedDeriv 4 (v15OdlyzkoTiltedF4 p.1) p.2) := by
  have hReal : Continuous (fun p : ℝ × ℝ ↦
      ∑ i ∈ Finset.range 5, (Nat.choose 4 i : ℝ) * p.1 ^ i *
        Real.exp (p.1 * p.2) *
          iteratedDeriv (4 - i) v15OdlyzkoF4 p.2) := by
    apply continuous_finsetSum _
    intro i _
    have hfi : Continuous (fun p : ℝ × ℝ ↦
        iteratedDeriv (4 - i) v15OdlyzkoF4 p.2) :=
      (v15OdlyzkoF4_contDiff_four.continuous_iteratedDeriv (4 - i)
        (by exact_mod_cast Nat.sub_le 4 i)).comp continuous_snd
    exact (((continuous_const.mul (continuous_fst.pow i)).mul
      (Real.continuous_exp.comp (continuous_fst.mul continuous_snd))).mul hfi)
  have hComplex := Complex.continuous_ofReal.comp hReal
  convert hComplex using 1
  funext p
  simpa only [Function.comp_apply] using
    v15OdlyzkoTiltedF4_fourth_deriv_formula p.1 p.2

private theorem v15OdlyzkoTiltedF4_iteratedDeriv_zero_outside (a : ℝ) (k : ℕ)
    {x : ℝ} (hx : 8 < |x|) :
    iteratedDeriv k (v15OdlyzkoTiltedF4 a) x = 0 := by
  have hOpen : IsOpen {y : ℝ | 8 < |y|} :=
    isOpen_lt continuous_const continuous_abs
  have hLocal : v15OdlyzkoTiltedF4 a =ᶠ[𝓝 x] (fun _ ↦ (0 : ℂ)) := by
    filter_upwards [hOpen.mem_nhds hx] with y hy
    simp [v15OdlyzkoTiltedF4,
      v15OdlyzkoF4_eq_zero_of_eight_lt_abs hy]
  rw [Filter.EventuallyEq.iteratedDeriv_eq k hLocal]
  simp

private theorem v15OdlyzkoTiltedF4_iteratedDeriv_norm_integral_eq_set
    (a : ℝ) (k : ℕ) :
    (∫ x : ℝ, ‖iteratedDeriv k (v15OdlyzkoTiltedF4 a) x‖) =
      ∫ x in Set.Icc (-8 : ℝ) 8,
        ‖iteratedDeriv k (v15OdlyzkoTiltedF4 a) x‖ := by
  rw [← setIntegral_univ]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    MeasurableSet.univ (Set.subset_univ _)
  intro x hx
  have hbound : 8 < |x| := by
    by_contra h
    apply hx.2
    change -8 ≤ x ∧ x ≤ 8
    rw [← abs_le]
    exact le_of_not_gt h
  rw [v15OdlyzkoTiltedF4_iteratedDeriv_zero_outside a k hbound, norm_zero]

/-- The two uniform integral bounds required after global smoothness. -/
def V15OdlyzkoTiltedFourthDerivativeMassBound (M₀ M₄ : ℝ) : Prop :=
  ∀ a : ℝ, -(1 / 2 : ℝ) ≤ a → a ≤ 1 / 2 →
    (∫ x : ℝ, ‖v15OdlyzkoTiltedF4 a x‖) ≤ M₀ ∧
      (∫ x : ℝ, ‖iteratedDeriv 4 (v15OdlyzkoTiltedF4 a) x‖) ≤ M₄

/-- Compactness of the closed tilt interval and of the common support gives
finite uniform `L¹` bounds for the exact kernel and its fourth derivative.
No numerical evaluation of these bounds is required for zero summability. -/
theorem v15OdlyzkoTiltedF4_exists_uniform_fourth_mass :
    ∃ M₀ M₄ : ℝ, V15OdlyzkoTiltedFourthDerivativeMassBound M₀ M₄ := by
  let S : Set (ℝ × ℝ) :=
    Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Set.Icc (-8 : ℝ) 8
  have hCompact : IsCompact S := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C₀, hC₀⟩ := hCompact.exists_bound_of_continuousOn
    v15OdlyzkoTiltedF4_continuous_joint.continuousOn
  obtain ⟨C₄, hC₄⟩ := hCompact.exists_bound_of_continuousOn
    v15OdlyzkoTiltedF4_fourth_deriv_continuous_joint.continuousOn
  let V : ℝ := (volume (Set.Icc (-8 : ℝ) 8)).toReal
  refine ⟨C₀ * V, C₄ * V, ?_⟩
  intro a ha₀ ha₁
  have ha : a ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := ⟨ha₀, ha₁⟩
  have hfinite : volume (Set.Icc (-8 : ℝ) 8) < ⊤ := isCompact_Icc.measure_lt_top
  constructor
  · have hb := norm_setIntegral_le_of_norm_le_const
      (μ := volume) (s := Set.Icc (-8 : ℝ) 8)
      (f := fun x : ℝ ↦ ‖v15OdlyzkoTiltedF4 a x‖)
      hfinite (by
        intro x hx
        simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
          hC₀ (a, x) (show (a, x) ∈ S from ⟨ha, hx⟩))
    have hEq := v15OdlyzkoTiltedF4_iteratedDeriv_norm_integral_eq_set a 0
    simp only [iteratedDeriv_zero] at hEq
    rw [hEq]
    have hle :
        (∫ x in Set.Icc (-8 : ℝ) 8, ‖v15OdlyzkoTiltedF4 a x‖) ≤
          ‖∫ x in Set.Icc (-8 : ℝ) 8, ‖v15OdlyzkoTiltedF4 a x‖‖ := by
      simpa only [Real.norm_eq_abs] using
        (le_abs_self (∫ x in Set.Icc (-8 : ℝ) 8, ‖v15OdlyzkoTiltedF4 a x‖))
    exact hle.trans hb
  · have hb := norm_setIntegral_le_of_norm_le_const
      (μ := volume) (s := Set.Icc (-8 : ℝ) 8)
      (f := fun x : ℝ ↦ ‖iteratedDeriv 4 (v15OdlyzkoTiltedF4 a) x‖)
      hfinite (by
        intro x hx
        simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
          hC₄ (a, x) (show (a, x) ∈ S from ⟨ha, hx⟩))
    rw [v15OdlyzkoTiltedF4_iteratedDeriv_norm_integral_eq_set a 4]
    have hle :
        (∫ x in Set.Icc (-8 : ℝ) 8,
          ‖iteratedDeriv 4 (v15OdlyzkoTiltedF4 a) x‖) ≤
          ‖∫ x in Set.Icc (-8 : ℝ) 8,
            ‖iteratedDeriv 4 (v15OdlyzkoTiltedF4 a) x‖‖ := by
      simpa only [Real.norm_eq_abs] using
        (le_abs_self (∫ x in Set.Icc (-8 : ℝ) 8,
          ‖iteratedDeriv 4 (v15OdlyzkoTiltedF4 a) x‖))
    exact hle.trans hb

/-- On every fixed compact interval of exponential tilts, the exact source
kernel and its fourth derivative have uniform finite `L¹` bounds. -/
def V15OdlyzkoTiltedFourthDerivativeMassBoundOn
    (a₀ a₁ M₀ M₄ : ℝ) : Prop :=
  ∀ a : ℝ, a₀ ≤ a → a ≤ a₁ →
    (∫ x : ℝ, ‖v15OdlyzkoTiltedF4 a x‖) ≤ M₀ ∧
      (∫ x : ℝ, ‖iteratedDeriv 4 (v15OdlyzkoTiltedF4 a) x‖) ≤ M₄

/-- Compactness supplies uniform fourth-derivative masses on an arbitrary
closed tilt interval. -/
theorem v15OdlyzkoTiltedF4_exists_uniform_fourth_mass_on (a₀ a₁ : ℝ) :
    ∃ M₀ M₄ : ℝ,
      V15OdlyzkoTiltedFourthDerivativeMassBoundOn a₀ a₁ M₀ M₄ := by
  let S : Set (ℝ × ℝ) :=
    Set.Icc a₀ a₁ ×ˢ Set.Icc (-8 : ℝ) 8
  have hCompact : IsCompact S := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C₀, hC₀⟩ := hCompact.exists_bound_of_continuousOn
    v15OdlyzkoTiltedF4_continuous_joint.continuousOn
  obtain ⟨C₄, hC₄⟩ := hCompact.exists_bound_of_continuousOn
    v15OdlyzkoTiltedF4_fourth_deriv_continuous_joint.continuousOn
  let V : ℝ := (volume (Set.Icc (-8 : ℝ) 8)).toReal
  refine ⟨C₀ * V, C₄ * V, ?_⟩
  intro a ha₀ ha₁
  have ha : a ∈ Set.Icc a₀ a₁ := ⟨ha₀, ha₁⟩
  have hfinite : volume (Set.Icc (-8 : ℝ) 8) < ⊤ := isCompact_Icc.measure_lt_top
  constructor
  · have hb := norm_setIntegral_le_of_norm_le_const
      (μ := volume) (s := Set.Icc (-8 : ℝ) 8)
      (f := fun x : ℝ ↦ ‖v15OdlyzkoTiltedF4 a x‖)
      hfinite (by
        intro x hx
        simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
          hC₀ (a, x) (show (a, x) ∈ S from ⟨ha, hx⟩))
    have hEq := v15OdlyzkoTiltedF4_iteratedDeriv_norm_integral_eq_set a 0
    simp only [iteratedDeriv_zero] at hEq
    rw [hEq]
    have hle :
        (∫ x in Set.Icc (-8 : ℝ) 8, ‖v15OdlyzkoTiltedF4 a x‖) ≤
          ‖∫ x in Set.Icc (-8 : ℝ) 8, ‖v15OdlyzkoTiltedF4 a x‖‖ := by
      simpa only [Real.norm_eq_abs] using
        (le_abs_self (∫ x in Set.Icc (-8 : ℝ) 8,
          ‖v15OdlyzkoTiltedF4 a x‖))
    exact hle.trans hb
  · have hb := norm_setIntegral_le_of_norm_le_const
      (μ := volume) (s := Set.Icc (-8 : ℝ) 8)
      (f := fun x : ℝ ↦ ‖iteratedDeriv 4 (v15OdlyzkoTiltedF4 a) x‖)
      hfinite (by
        intro x hx
        simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
          hC₄ (a, x) (show (a, x) ∈ S from ⟨ha, hx⟩))
    rw [v15OdlyzkoTiltedF4_iteratedDeriv_norm_integral_eq_set a 4]
    have hle :
        (∫ x in Set.Icc (-8 : ℝ) 8,
          ‖iteratedDeriv 4 (v15OdlyzkoTiltedF4 a) x‖) ≤
          ‖∫ x in Set.Icc (-8 : ℝ) 8,
            ‖iteratedDeriv 4 (v15OdlyzkoTiltedF4 a) x‖‖ := by
      simpa only [Real.norm_eq_abs] using
        (le_abs_self (∫ x in Set.Icc (-8 : ℝ) 8,
          ‖iteratedDeriv 4 (v15OdlyzkoTiltedF4 a) x‖))
    exact hle.trans hb

/-- Uniform fourth-derivative data for the exponentially tilted exact kernel
on the entire closed critical strip. The `C⁴` assertion and both integral
bounds are established above for the exact source kernel. -/
def V15OdlyzkoTiltedFourthDerivativeCertificate (M₀ M₄ : ℝ) : Prop :=
  ∀ a : ℝ, -(1 / 2 : ℝ) ≤ a → a ≤ 1 / 2 →
    ContDiff ℝ 4 (v15OdlyzkoTiltedF4 a) ∧
      (∀ k : ℕ, (k : ℕ∞) ≤ 4 →
        Integrable (iteratedDeriv k (v15OdlyzkoTiltedF4 a)) volume) ∧
      (∫ x : ℝ, ‖v15OdlyzkoTiltedF4 a x‖) ≤ M₀ ∧
      (∫ x : ℝ, ‖iteratedDeriv 4 (v15OdlyzkoTiltedF4 a) x‖) ≤ M₄

/-- Compact support persists under every one-dimensional iterated derivative. -/
private theorem v15_hasCompactSupport_iteratedDeriv (f : ℝ → ℂ)
    (hf : HasCompactSupport f) (k : ℕ) :
    HasCompactSupport (iteratedDeriv k f) := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ k ih => simpa only [iteratedDeriv_succ] using ih.deriv

/-- For the actual tilted source kernel, compact support turns `C⁴` into
integrability of all four derivatives. -/
theorem v15OdlyzkoTiltedF4_iteratedDeriv_integrable_of_contDiff
    (a : ℝ) (hSmooth : ContDiff ℝ 4 (v15OdlyzkoTiltedF4 a))
    (k : ℕ) (hk : (k : ℕ∞) ≤ 4) :
    Integrable (iteratedDeriv k (v15OdlyzkoTiltedF4 a)) volume := by
  have hk' : (k : WithTop ℕ∞) ≤ 4 := by exact_mod_cast hk
  exact (hSmooth.continuous_iteratedDeriv k hk').integrable_of_hasCompactSupport
    (v15_hasCompactSupport_iteratedDeriv _
      (v15OdlyzkoTiltedF4_hasCompactSupport a) k)

theorem v15OdlyzkoTiltedFourthDerivativeCertificate_of_massBound
    (M₀ M₄ : ℝ) (hMass : V15OdlyzkoTiltedFourthDerivativeMassBound M₀ M₄) :
    V15OdlyzkoTiltedFourthDerivativeCertificate M₀ M₄ := by
  intro a ha₀ ha₁
  obtain ⟨h₀, h₄⟩ := hMass a ha₀ ha₁
  exact ⟨v15OdlyzkoTiltedF4_contDiff_four a,
    v15OdlyzkoTiltedF4_iteratedDeriv_integrable_of_contDiff a
      (v15OdlyzkoTiltedF4_contDiff_four a),
    h₀, h₄⟩

/-- Four integrations by parts, in mathlib's Fourier normalization, yield
a bound on the transform multiplied by the fourth power of the frequency. -/
theorem v15Fourier_fourth_frequency_bound (f : ℝ → ℂ)
    (hf : ContDiff ℝ 4 f)
    (hInt : ∀ k : ℕ, (k : ℕ∞) ≤ 4 → Integrable (iteratedDeriv k f) volume)
    (w : ℝ) :
    ‖((2 * (Real.pi : ℂ) * Complex.I * (w : ℂ)) ^ 4)‖ * ‖𝓕 f w‖ ≤
      ∫ x : ℝ, ‖iteratedDeriv 4 f x‖ := by
  have hEq := congrFun (Real.fourier_iteratedDeriv (n := 4) hf hInt
    (by norm_num : (4 : ℕ∞) ≤ 4)) w
  have hBound := VectorFourier.norm_fourierIntegral_le_integral_norm
    𝐞 volume (innerₗ ℝ) (iteratedDeriv 4 f) w
  change ‖𝓕 (iteratedDeriv 4 f) w‖ ≤
    ∫ x : ℝ, ‖iteratedDeriv 4 f x‖ at hBound
  rw [hEq] at hBound
  simpa only [norm_smul] using hBound

/-- The complex Fourier multiplier becomes exactly `|Im s|⁴` after the
source-to-mathlib frequency conversion; the factors of `2π` cancel. -/
theorem v15Odlyzko_fourth_frequency_normalization (t : ℝ) :
    ‖((2 * (Real.pi : ℂ) * Complex.I *
      ((-t / (2 * Real.pi) : ℝ) : ℂ)) ^ 4)‖ = |t| ^ 4 := by
  have hScalar :
      2 * (Real.pi : ℂ) * Complex.I *
        ((-t / (2 * Real.pi) : ℝ) : ℂ) = -(t : ℂ) * Complex.I := by
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [hScalar, norm_pow, norm_mul, Complex.norm_I, mul_one]
  simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs]

/-- The concrete fourth-derivative certificate removes the previously
abstract `Phi` decay premise from the paired-zero convergence criterion. -/
theorem v15OdlyzkoPhiFourthPowerBound_of_derivativeCertificate
    (M₀ M₄ : ℝ) (hCert : V15OdlyzkoTiltedFourthDerivativeCertificate M₀ M₄) :
    V15OdlyzkoPhiFourthPowerBound (8 * (M₀ + M₄)) := by
  intro s hs₀ hs₁
  let a : ℝ := s.re - 1 / 2
  let w : ℝ := -s.im / (2 * Real.pi)
  let f : ℝ → ℂ := v15OdlyzkoTiltedF4 a
  obtain ⟨hSmooth, hInt, hMass, hDerivMass⟩ := hCert a (by dsimp [a]; linarith)
    (by dsimp [a]; linarith)
  have hPhi : v15OdlyzkoPhi s = 𝓕 f w := by
    simpa only [a, w, f] using v15OdlyzkoPhi_eq_fourier s
  have hZero : ‖v15OdlyzkoPhi s‖ ≤ M₀ := by
    rw [hPhi]
    exact (VectorFourier.norm_fourierIntegral_le_integral_norm
      𝐞 volume (innerₗ ℝ) f w).trans hMass
  have hFourth : |s.im| ^ 4 * ‖v15OdlyzkoPhi s‖ ≤ M₄ := by
    have h := v15Fourier_fourth_frequency_bound f hSmooth hInt w
    rw [v15Odlyzko_fourth_frequency_normalization s.im, ← hPhi] at h
    exact h.trans hDerivMass
  have hAbs : 0 ≤ |s.im| := abs_nonneg _
  have hPow : (1 + |s.im|) ^ 4 ≤ 8 * (1 + |s.im| ^ 4) := by
    have hFactor : 0 ≤ (|s.im| - 1) ^ 2 *
        (7 * |s.im| ^ 2 + 10 * |s.im| + 7) := by positivity
    nlinarith
  have hProduct :
      (1 + |s.im|) ^ 4 * ‖v15OdlyzkoPhi s‖ ≤ 8 * (M₀ + M₄) := by
    calc
      _ ≤ (8 * (1 + |s.im| ^ 4)) * ‖v15OdlyzkoPhi s‖ :=
        mul_le_mul_of_nonneg_right hPow (norm_nonneg _)
      _ = 8 * (‖v15OdlyzkoPhi s‖ + |s.im| ^ 4 * ‖v15OdlyzkoPhi s‖) := by ring
      _ ≤ 8 * (M₀ + M₄) := by nlinarith
  apply (le_div_iff₀ (by positivity : 0 < (1 + |s.im|) ^ 4)).2
  nlinarith

theorem v15OdlyzkoPhiFourthPowerBound_of_derivativeMassBound
    (M₀ M₄ : ℝ) (hMass : V15OdlyzkoTiltedFourthDerivativeMassBound M₀ M₄) :
    V15OdlyzkoPhiFourthPowerBound (8 * (M₀ + M₄)) :=
  v15OdlyzkoPhiFourthPowerBound_of_derivativeCertificate M₀ M₄
    (v15OdlyzkoTiltedFourthDerivativeCertificate_of_massBound M₀ M₄ hMass)

/-- The actual Odlyzko transform satisfies a uniform fourth-power decay
estimate throughout the closed critical strip. The finite constant exists
by compactness and is independent of the strip point. -/
theorem v15OdlyzkoPhi_exists_fourthPowerBound :
    ∃ D : ℝ, 0 ≤ D ∧ V15OdlyzkoPhiFourthPowerBound D := by
  obtain ⟨M₀, M₄, hMass⟩ :=
    v15OdlyzkoTiltedF4_exists_uniform_fourth_mass
  obtain ⟨h₀, h₄⟩ := hMass 0 (by norm_num) (by norm_num)
  have hM₀ : 0 ≤ M₀ :=
    (integral_nonneg (fun x ↦ norm_nonneg (v15OdlyzkoTiltedF4 0 x))).trans h₀
  have hM₄ : 0 ≤ M₄ :=
    (integral_nonneg (fun x ↦ norm_nonneg
      (iteratedDeriv 4 (v15OdlyzkoTiltedF4 0) x))).trans h₄
  exact ⟨8 * (M₀ + M₄), by positivity,
    v15OdlyzkoPhiFourthPowerBound_of_derivativeMassBound M₀ M₄ hMass⟩

/-- A uniform fourth-power transform bound on an arbitrary closed vertical
strip. -/
def V15OdlyzkoPhiFourthPowerBoundOn (σ₀ σ₁ D : ℝ) : Prop :=
  ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ →
    ‖v15OdlyzkoPhi s‖ ≤ D / (1 + |s.im|) ^ 4

/-- Uniform fourth-derivative masses on the corresponding compact interval
of exponential tilts imply fourth-power decay on a closed vertical strip. -/
theorem v15OdlyzkoPhiFourthPowerBoundOn_of_massBound
    (σ₀ σ₁ M₀ M₄ : ℝ)
    (hMass : V15OdlyzkoTiltedFourthDerivativeMassBoundOn
      (σ₀ - 1 / 2) (σ₁ - 1 / 2) M₀ M₄) :
    V15OdlyzkoPhiFourthPowerBoundOn σ₀ σ₁ (8 * (M₀ + M₄)) := by
  intro s hs₀ hs₁
  let a : ℝ := s.re - 1 / 2
  let w : ℝ := -s.im / (2 * Real.pi)
  let f : ℝ → ℂ := v15OdlyzkoTiltedF4 a
  obtain ⟨hMass₀, hMass₄⟩ := hMass a (by dsimp [a]; linarith)
    (by dsimp [a]; linarith)
  have hSmooth : ContDiff ℝ 4 f := by
    simpa only [f] using v15OdlyzkoTiltedF4_contDiff_four a
  have hInt : ∀ k : ℕ, (k : ℕ∞) ≤ 4 →
      Integrable (iteratedDeriv k f) volume := by
    intro k hk
    simpa only [f] using
      v15OdlyzkoTiltedF4_iteratedDeriv_integrable_of_contDiff a
        (v15OdlyzkoTiltedF4_contDiff_four a) k hk
  have hPhi : v15OdlyzkoPhi s = 𝓕 f w := by
    simpa only [a, w, f] using v15OdlyzkoPhi_eq_fourier s
  have hZero : ‖v15OdlyzkoPhi s‖ ≤ M₀ := by
    rw [hPhi]
    exact (VectorFourier.norm_fourierIntegral_le_integral_norm
      𝐞 volume (innerₗ ℝ) f w).trans hMass₀
  have hFourth : |s.im| ^ 4 * ‖v15OdlyzkoPhi s‖ ≤ M₄ := by
    have h := v15Fourier_fourth_frequency_bound f hSmooth hInt w
    rw [v15Odlyzko_fourth_frequency_normalization s.im, ← hPhi] at h
    exact h.trans hMass₄
  have hPow : (1 + |s.im|) ^ 4 ≤ 8 * (1 + |s.im| ^ 4) := by
    have hFactor : 0 ≤ (|s.im| - 1) ^ 2 *
        (7 * |s.im| ^ 2 + 10 * |s.im| + 7) := by positivity
    nlinarith
  have hProduct :
      (1 + |s.im|) ^ 4 * ‖v15OdlyzkoPhi s‖ ≤ 8 * (M₀ + M₄) := by
    calc
      _ ≤ (8 * (1 + |s.im| ^ 4)) * ‖v15OdlyzkoPhi s‖ :=
        mul_le_mul_of_nonneg_right hPow (norm_nonneg _)
      _ = 8 * (‖v15OdlyzkoPhi s‖ +
          |s.im| ^ 4 * ‖v15OdlyzkoPhi s‖) := by ring
      _ ≤ 8 * (M₀ + M₄) := by nlinarith
  apply (le_div_iff₀ (by positivity : 0 < (1 + |s.im|) ^ 4)).2
  nlinarith

/-- The exact Odlyzko transform has uniform fourth-power decay on the wider
strip used by the finite symmetric contour. -/
theorem v15OdlyzkoPhi_exists_wideFourthPowerBound :
    ∃ D : ℝ, 0 ≤ D ∧ V15OdlyzkoPhiFourthPowerBoundOn (-1) 2 D := by
  obtain ⟨M₀, M₄, hMass⟩ :=
    v15OdlyzkoTiltedF4_exists_uniform_fourth_mass_on
      (-(3 / 2 : ℝ)) (3 / 2 : ℝ)
  obtain ⟨h₀, h₄⟩ := hMass 0 (by norm_num) (by norm_num)
  have hM₀ : 0 ≤ M₀ :=
    (integral_nonneg (fun x ↦ norm_nonneg (v15OdlyzkoTiltedF4 0 x))).trans h₀
  have hM₄ : 0 ≤ M₄ :=
    (integral_nonneg (fun x ↦ norm_nonneg
      (iteratedDeriv 4 (v15OdlyzkoTiltedF4 0) x))).trans h₄
  have hMass' : V15OdlyzkoTiltedFourthDerivativeMassBoundOn
      ((-1 : ℝ) - 1 / 2) (2 - 1 / 2) M₀ M₄ := by
    intro a ha₀ ha₁
    apply hMass a <;> norm_num at ha₀ ha₁ ⊢ <;> linarith
  exact ⟨8 * (M₀ + M₄), by positivity,
    v15OdlyzkoPhiFourthPowerBoundOn_of_massBound (-1) 2 M₀ M₄ hMass'⟩

/-- For any height-ordered zero enumeration satisfying the quadratic ordinal
bound, the actual conjugate-paired transform series is absolutely summable.
The decay of the exact transform is now a proved theorem. -/
theorem v15OdlyzkoPhi_conj_pair_summable_of_ordinalBound
    (zeros : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hStrip : ∀ n, 0 ≤ (zeros n).re ∧ (zeros n).re ≤ 1)
    (hGrowth : V15OdlyzkoZeroOrdinalBound C zeros) :
    Summable (fun n ↦ v15OdlyzkoPhi (zeros n) +
      v15OdlyzkoPhi (conj (zeros n))) := by
  obtain ⟨D, hD, hDecay⟩ := v15OdlyzkoPhi_exists_fourthPowerBound
  exact v15OdlyzkoPhi_conj_pair_summable_of_bounds zeros C D hC hD
    hStrip hGrowth hDecay

/-- In the Table 4 reduction, a quadratic count for height-ordered zero
representatives now suffices for paired summability. The transform decay
assumption has been discharged for Odlyzko's exact source kernel. -/
theorem v15_odlyzkoTable4ExplicitCorrectionInput_of_count
    (realIndices : CodedNumberField → Finset ℕ)
    (realZeros pairReps : CodedNumberField → ℕ → ℂ)
    (hReal : ∀ K i, i ∈ realIndices K → (realZeros K i).im = 0)
    (hNonreal : ∀ K i, (pairReps K i).im ≠ 0)
    (hRealStrip : ∀ K i, i ∈ realIndices K →
      0 ≤ (realZeros K i).re ∧ (realZeros K i).re ≤ 1)
    (hPairStrip : ∀ K i, 0 ≤ (pairReps K i).re ∧ (pairReps K i).re ≤ 1)
    (C : CodedNumberField → ℝ)
    (hC : ∀ K, 0 ≤ C K)
    (hOrdered : ∀ K i j, i ≤ j →
      |(pairReps K i).im| ≤ |(pairReps K j).im|)
    (hCount : ∀ K, V15OdlyzkoZeroCountBound (C K) (pairReps K))
    (hFormula : V15OdlyzkoExplicitFormulaInput
      (fun K ↦ (∑ i ∈ realIndices K, (v15OdlyzkoPhi (realZeros K i)).re) +
        (∑' i, (v15OdlyzkoPhi (pairReps K i) +
          v15OdlyzkoPhi (conj (pairReps K i)))).re))
    (hAB : V15OdlyzkoABIntegralCertificate) :
    V15OdlyzkoTable4ExplicitCorrectionInput := by
  obtain ⟨D, hD, hDecay⟩ := v15OdlyzkoPhi_exists_fourthPowerBound
  exact v15_odlyzkoTable4ExplicitCorrectionInput_of_countAndDecay
    realIndices realZeros pairReps hReal hNonreal hRealStrip hPairStrip
    C D hC hD hOrdered hCount hDecay hFormula hAB

end
end TraceEuclidean
