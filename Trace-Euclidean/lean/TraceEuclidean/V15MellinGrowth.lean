import TraceEuclidean.V15DedekindZetaCompletedJensen
import TraceEuclidean.V15OdlyzkoNumerical
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Quantitative growth estimates for Mellin tails

This file begins the quantitative estimate required by the completed-zeta
Jensen bridge.  It turns the asymptotic exponential-decay hypothesis of an
`IsMellinPair` into a single pointwise envelope valid on the whole integration
ray `[1, ∞)`, and records the elementary logarithmic/Young inequality that
absorbs arbitrary Mellin powers into a quadratic exponential in the parameter.
-/

namespace TraceEuclidean.V15MellinGrowth

noncomputable section

open Filter Set Asymptotics NumberField

/-- A fixed nonzero complex base raised to a complex power has at most
quadratic exponential growth. -/
theorem norm_cpow_le_exp_quadratic {z : ℂ} (hz : z ≠ 0) (s : ℂ) :
    ‖z ^ s‖ ≤ Real.exp
      ((|Real.log ‖z‖| + |Complex.arg z|) * (1 + ‖s‖) ^ 2) := by
  have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let L : ℝ := |Real.log ‖z‖| + |Complex.arg z|
  have hL : 0 ≤ L := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hre : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
  have him : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hnormSq : ‖s‖ ≤ (1 + ‖s‖) ^ 2 := by
    nlinarith [norm_nonneg s]
  have hexponent :
      Real.log ‖z‖ * s.re - Complex.arg z * s.im ≤
        L * (1 + ‖s‖) ^ 2 := by
    calc
      Real.log ‖z‖ * s.re - Complex.arg z * s.im ≤
          |Real.log ‖z‖ * s.re| + |Complex.arg z * s.im| := by
        nlinarith [le_abs_self (Real.log ‖z‖ * s.re),
          neg_le_abs (Complex.arg z * s.im)]
      _ = |Real.log ‖z‖| * |s.re| + |Complex.arg z| * |s.im| := by
        rw [abs_mul, abs_mul]
      _ ≤ |Real.log ‖z‖| * ‖s‖ + |Complex.arg z| * ‖s‖ :=
        add_le_add
          (mul_le_mul_of_nonneg_left hre (abs_nonneg _))
          (mul_le_mul_of_nonneg_left him (abs_nonneg _))
      _ = L * ‖s‖ := by dsimp [L]; ring
      _ ≤ L * (1 + ‖s‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hnormSq hL
  rw [Complex.norm_cpow_of_ne_zero hz,
    Real.rpow_def_of_pos hznorm, div_eq_mul_inv, ← Real.exp_neg,
    ← Real.exp_add]
  exact Real.exp_le_exp.mpr hexponent

/-- For `y ≥ 1` and `α > 0`, the logarithm is bounded by the half-`α` power.
This form is chosen so that squaring the power gives `y ^ α`. -/
theorem log_le_two_div_mul_rpow_half {α y : ℝ} (hα : 0 < α) (hy : 1 ≤ y) :
    Real.log y ≤ (2 / α) * y ^ (α / 2) := by
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have ha : 0 < α / 2 := div_pos hα (by norm_num)
  have hlog := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hypos (α / 2))
  rw [Real.log_rpow hypos] at hlog
  have hmain : Real.log y ≤ y ^ (α / 2) / (α / 2) := by
    apply (le_div_iff₀ ha).2
    nlinarith [Real.rpow_pos_of_pos hypos (α / 2)]
  calc
    Real.log y ≤ y ^ (α / 2) / (α / 2) := hmain
    _ = (2 / α) * y ^ (α / 2) := by field_simp

/-- A Mellin power times an exponential tail is bounded by a fixed integrable
tail and a quadratic exponential in the Mellin exponent. -/
theorem rpow_mul_exp_neg_le_exp_sq_mul_exp_half
    {p c α y : ℝ} (hp : 0 ≤ p) (hc : 0 < c) (hα : 0 < α) (hy : 1 ≤ y) :
    y ^ p * Real.exp (-c * y ^ α) ≤
      Real.exp ((((2 / α) * p) ^ 2) / (2 * c)) *
        Real.exp (-(c / 2) * y ^ α) := by
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  let L : ℝ := 2 / α
  let t : ℝ := y ^ (α / 2)
  let q : ℝ := L * p
  have hL : 0 < L := by dsimp [L]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hlog : Real.log y ≤ L * t := by
    simpa [L, t] using log_le_two_div_mul_rpow_half hα hy
  have hplog : p * Real.log y ≤ q * t := by
    dsimp [q]
    nlinarith
  have ht_sq : t ^ 2 = y ^ α := by
    dsimp [t]
    rw [← Real.rpow_natCast (y ^ (α / 2)) 2, ← Real.rpow_mul hypos.le]
    congr 1
    ring
  have hyoung : q * t ≤ q ^ 2 / (2 * c) + c * t ^ 2 / 2 := by
    rw [show q ^ 2 / (2 * c) + c * t ^ 2 / 2 =
        (q ^ 2 + c ^ 2 * t ^ 2) / (2 * c) by field_simp]
    apply (le_div_iff₀ (mul_pos (by norm_num) hc)).2
    nlinarith [sq_nonneg (q - c * t)]
  have hexponent :
      p * Real.log y - c * y ^ α ≤
        q ^ 2 / (2 * c) - (c / 2) * y ^ α := by
    rw [← ht_sq]
    nlinarith
  rw [Real.rpow_def_of_pos hypos, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [hexponent]

/-- Asymptotic exponential decay plus continuity gives a uniform exponential
envelope on the entire ray `[1, ∞)`. -/
theorem exists_uniform_exp_bound
    {φ : ℝ → ℂ} {c α : ℝ}
    (hcont : ContinuousOn φ (Ioi (0 : ℝ))) (hc : 0 < c) (hα : 0 < α)
    (hdecay : φ =O[atTop] (fun y : ℝ ↦ Real.exp (-c * y ^ α))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, 1 ≤ y →
      ‖φ y‖ ≤ B * Real.exp (-c * y ^ α) := by
  obtain ⟨B₀, hB₀⟩ := hdecay.bound
  obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.mp hB₀
  let R : ℝ := max 1 R₀
  have hRone : 1 ≤ R := le_max_left _ _
  have hR₀R : R₀ ≤ R := le_max_right _ _
  have hcompact : IsCompact (Icc (1 : ℝ) R) := isCompact_Icc
  have hcont' : ContinuousOn φ (Icc (1 : ℝ) R) :=
    hcont.mono (fun y hy ↦ lt_of_lt_of_le zero_lt_one hy.1)
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hcont'
  have hMnonneg : 0 ≤ M := by
    have hone : (1 : ℝ) ∈ Icc (1 : ℝ) R := ⟨le_rfl, hRone⟩
    exact (norm_nonneg (φ 1)).trans (hM 1 hone)
  let B : ℝ := max |B₀| (M * Real.exp (c * R ^ α))
  refine ⟨B, ?_, ?_⟩
  · exact le_trans (abs_nonneg B₀) (le_max_left _ _)
  · intro y hy
    by_cases hyR : y ≤ R
    · have hyIcc : y ∈ Icc (1 : ℝ) R := ⟨hy, hyR⟩
      have hyrpow : y ^ α ≤ R ^ α :=
        Real.rpow_le_rpow (le_trans zero_le_one hy) hyR (le_of_lt hα)
      have honeexp : 1 ≤ Real.exp (c * R ^ α) * Real.exp (-c * y ^ α) := by
        rw [← Real.exp_add, ← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hyrpow)]
      calc
        ‖φ y‖ ≤ M := hM y hyIcc
        _ ≤ (M * Real.exp (c * R ^ α)) * Real.exp (-c * y ^ α) := by
          nlinarith [mul_nonneg hMnonneg (sub_nonneg.mpr honeexp)]
        _ ≤ B * Real.exp (-c * y ^ α) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _)
            (Real.exp_nonneg _)
    · have hRy : R ≤ y := le_of_not_ge hyR
      have htail := hR₀ y (hR₀R.trans hRy)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at htail
      calc
        ‖φ y‖ ≤ B₀ * Real.exp (-c * y ^ α) := htail
        _ ≤ |B₀| * Real.exp (-c * y ^ α) :=
          mul_le_mul_of_nonneg_right (le_abs_self B₀) (Real.exp_nonneg _)
        _ ≤ B * Real.exp (-c * y ^ α) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)

/-- Both reduced functions in an `IsMellinPair` admit uniform envelopes with
the same decay rate. -/
theorem IsMellinPair.exists_uniform_exp_bounds
    {f g : ℝ → ℂ} {a₀ b₀ C : ℂ} {k c α : ℝ}
    (h : DedekindZeta.MellinPrinciple.IsMellinPair
      f g a₀ b₀ C k c α) :
    ∃ Bf Bg : ℝ, 0 ≤ Bf ∧ 0 ≤ Bg ∧
      (∀ y : ℝ, 1 ≤ y → ‖f y - a₀‖ ≤ Bf * Real.exp (-c * y ^ α)) ∧
      (∀ y : ℝ, 1 ≤ y → ‖g y - b₀‖ ≤ Bg * Real.exp (-c * y ^ α)) := by
  obtain ⟨Bf, hBf, hf⟩ := exists_uniform_exp_bound
    (h.hf_cont.sub continuousOn_const) h.hc h.hα h.hf_decay
  obtain ⟨Bg, hBg, hg⟩ := exists_uniform_exp_bound
    (h.hg_cont.sub continuousOn_const) h.hc h.hα h.hg_decay
  exact ⟨Bf, Bg, hBf, hBg, hf, hg⟩

/-- The fixed half-rate exponential tail is integrable on `[1, ∞)` for every
positive power `α`. -/
theorem integrableOn_exp_neg_mul_rpow
    {c α : ℝ} (hc : 0 < c) (hα : 0 < α) :
    MeasureTheory.IntegrableOn
      (fun y : ℝ ↦ Real.exp (-(c / 2) * y ^ α)) (Ioi (1 : ℝ)) := by
  have hrate : 0 < c / 2 := div_pos hc (by norm_num)
  have hlo :
      (fun y : ℝ ↦ Real.exp (-(c / 2) * y ^ α)) =o[atTop]
        (fun y : ℝ ↦ y ^ (-2 : ℝ)) := by
    have h0 :=
      (isLittleO_exp_neg_mul_rpow_atTop hrate ((-2 : ℝ) / α)).comp_tendsto
        (tendsto_rpow_atTop hα)
    refine h0.congr' (Filter.EventuallyEq.rfl) ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    simp only [Function.comp_apply]
    rw [← Real.rpow_mul hy]
    congr 1
    field_simp
  have hcont : ContinuousOn
      (fun y : ℝ ↦ Real.exp (-(c / 2) * y ^ α)) (Ici (1 : ℝ)) := by
    exact (Real.continuous_exp.comp
      (continuous_const.mul (Real.continuous_rpow_const hα.le))).continuousOn
  have hpow : MeasureTheory.IntegrableAtFilter
      (fun y : ℝ ↦ y ^ (-2 : ℝ)) atTop :=
    ⟨Ioi (1 : ℝ), Ioi_mem_atTop 1,
      integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one⟩
  have hIci : MeasureTheory.IntegrableOn
      (fun y : ℝ ↦ Real.exp (-(c / 2) * y ^ α)) (Ici (1 : ℝ)) :=
    (hcont.locallyIntegrableOn measurableSet_Ici).integrableOn_of_isBigO_atTop
      hlo.isBigO hpow
  exact (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mp hIci

/-- Norm bound for one Mellin-tail summand.  The exponent `p` may be any
nonnegative upper bound for the real part of the complex Mellin power. -/
theorem norm_setIntegral_mul_cpow_le
    {φ : ℝ → ℂ} {B c α p : ℝ} (hB : 0 ≤ B) (hc : 0 < c) (hα : 0 < α)
    (hφ : ∀ y : ℝ, 1 ≤ y → ‖φ y‖ ≤ B * Real.exp (-c * y ^ α))
    (u : ℂ) (hp : 0 ≤ p) (hu : u.re ≤ p) :
    ‖∫ y in Ioi (1 : ℝ), φ y * (y : ℂ) ^ u‖ ≤
      B * Real.exp ((((2 / α) * p) ^ 2) / (2 * c)) *
        ∫ y in Ioi (1 : ℝ), Real.exp (-(c / 2) * y ^ α) := by
  let Q : ℝ := (((2 / α) * p) ^ 2) / (2 * c)
  have hfixed := integrableOn_exp_neg_mul_rpow hc hα
  have hmajor : MeasureTheory.IntegrableOn
      (fun y : ℝ ↦ (B * Real.exp Q) * Real.exp (-(c / 2) * y ^ α))
      (Ioi (1 : ℝ)) :=
    hfixed.const_mul (B * Real.exp Q)
  have hpoint : ∀ y ∈ Ioi (1 : ℝ),
      ‖φ y * (y : ℂ) ^ u‖ ≤
        (B * Real.exp Q) * Real.exp (-(c / 2) * y ^ α) := by
    intro y hy
    have hyone : 1 ≤ y := le_of_lt hy
    have hypos : 0 < y := lt_trans zero_lt_one hy
    have hpow : y ^ u.re ≤ y ^ p :=
      Real.rpow_le_rpow_of_exponent_le hyone hu
    have htail := rpow_mul_exp_neg_le_exp_sq_mul_exp_half hp hc hα hyone
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hypos]
    calc
      ‖φ y‖ * y ^ u.re ≤
          (B * Real.exp (-c * y ^ α)) * y ^ p :=
        mul_le_mul (hφ y hyone) hpow (Real.rpow_nonneg hypos.le _)
          (mul_nonneg hB (Real.exp_nonneg _))
      _ = B * (y ^ p * Real.exp (-c * y ^ α)) := by ring
      _ ≤ B * (Real.exp Q * Real.exp (-(c / 2) * y ^ α)) :=
        mul_le_mul_of_nonneg_left (by simpa [Q] using htail) hB
      _ = (B * Real.exp Q) * Real.exp (-(c / 2) * y ^ α) := by ring
  have hae : ∀ᵐ y ∂(MeasureTheory.volume.restrict (Ioi (1 : ℝ))),
      ‖φ y * (y : ℂ) ^ u‖ ≤
        (B * Real.exp Q) * Real.exp (-(c / 2) * y ^ α) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall (fun y hy ↦ hpoint y hy))
  have hnorm := MeasureTheory.norm_integral_le_of_norm_le hmajor hae
  rw [MeasureTheory.integral_const_mul] at hnorm
  simpa [Q, mul_assoc] using hnorm

/-- The entire Mellin tail of an `IsMellinPair` has a quadratic exponential
bound in the complex parameter.  All constants depend only on the fixed pair,
not on `s`. -/
theorem IsMellinPair.exists_mellinTail_quadratic_bound
    {f g : ℝ → ℂ} {a₀ b₀ C : ℂ} {k c α : ℝ}
    (h : DedekindZeta.MellinPrinciple.IsMellinPair
      f g a₀ b₀ C k c α) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧ ∀ s : ℂ,
      ‖DedekindZeta.MellinPrinciple.mellinTail f g a₀ b₀ C k s‖ ≤
        D * Real.exp (A * (1 + ‖s‖) ^ 2) := by
  obtain ⟨Bf, Bg, hBf, hBg, hf, hg⟩ :=
    IsMellinPair.exists_uniform_exp_bounds h
  let J : ℝ :=
    ∫ y in Ioi (1 : ℝ), Real.exp (-(c / 2) * y ^ α)
  have hJ : 0 ≤ J := by
    dsimp [J]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioi
      (fun _ _ ↦ (Real.exp_pos _).le)
  let a : ℝ := (2 / α) ^ 2 / (2 * c)
  have ha : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) h.hc.le)
  let A : ℝ := a * (k + 2) ^ 2
  have hA : 0 ≤ A := mul_nonneg ha (sq_nonneg _)
  let D : ℝ := (Bf + ‖C‖ * Bg) * J
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  refine ⟨A, D, hA, hD, ?_⟩
  intro s
  let p : ℝ := |s.re| + k + 1
  have hp : 0 ≤ p := by dsimp [p]; nlinarith [abs_nonneg s.re, h.hk]
  have hleftExp : (s - 1).re ≤ p := by
    dsimp [p]
    nlinarith [le_abs_self s.re, h.hk]
  have hrightExp : ((k : ℂ) - s - 1).re ≤ p := by
    dsimp [p]
    nlinarith [neg_le_abs s.re]
  have hleft := norm_setIntegral_mul_cpow_le hBf h.hc h.hα hf
    (s - 1) hp hleftExp
  have hCg : ∀ y : ℝ, 1 ≤ y →
      ‖C * (g y - b₀)‖ ≤ (‖C‖ * Bg) * Real.exp (-c * y ^ α) := by
    intro y hy
    rw [norm_mul]
    calc
      ‖C‖ * ‖g y - b₀‖ ≤ ‖C‖ * (Bg * Real.exp (-c * y ^ α)) :=
        mul_le_mul_of_nonneg_left (hg y hy) (norm_nonneg C)
      _ = (‖C‖ * Bg) * Real.exp (-c * y ^ α) := by ring
  have hright := norm_setIntegral_mul_cpow_le
    (mul_nonneg (norm_nonneg C) hBg) h.hc h.hα hCg
      ((k : ℂ) - s - 1) hp hrightExp
  have htail :
      ‖DedekindZeta.MellinPrinciple.mellinTail f g a₀ b₀ C k s‖ ≤
        D * Real.exp (a * p ^ 2) := by
    unfold DedekindZeta.MellinPrinciple.mellinTail
    rw [MeasureTheory.integral_add
      (DedekindZeta.MellinPrinciple.mellinTail_integrable_left h)
      (DedekindZeta.MellinPrinciple.mellinTail_integrable_right h)]
    calc
      ‖(∫ y in Ioi (1 : ℝ), (f y - a₀) * (y : ℂ) ^ (s - 1)) +
          ∫ y in Ioi (1 : ℝ),
            C * (g y - b₀) * (y : ℂ) ^ ((k : ℂ) - s - 1)‖ ≤
          ‖∫ y in Ioi (1 : ℝ), (f y - a₀) * (y : ℂ) ^ (s - 1)‖ +
            ‖∫ y in Ioi (1 : ℝ),
              C * (g y - b₀) * (y : ℂ) ^ ((k : ℂ) - s - 1)‖ :=
        norm_add_le _ _
      _ ≤ Bf * Real.exp ((((2 / α) * p) ^ 2) / (2 * c)) * J +
          (‖C‖ * Bg) * Real.exp ((((2 / α) * p) ^ 2) / (2 * c)) * J :=
        add_le_add hleft hright
      _ = D * Real.exp (a * p ^ 2) := by
        dsimp [D, a]
        ring_nf
  have hre : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
  have hk2 : 0 ≤ k + 2 := by linarith [h.hk]
  have hpUpper : p ≤ (k + 2) * (1 + ‖s‖) := by
    dsimp [p]
    have hknorm : 0 ≤ (k + 1) * ‖s‖ :=
      mul_nonneg (by linarith [h.hk]) (norm_nonneg s)
    nlinarith
  have hUpperNonneg : 0 ≤ (k + 2) * (1 + ‖s‖) :=
    mul_nonneg hk2 (by positivity)
  have hpSq : p ^ 2 ≤ ((k + 2) * (1 + ‖s‖)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hpUpper)
      (add_nonneg hp hUpperNonneg)]
  have hExponent : a * p ^ 2 ≤ A * (1 + ‖s‖) ^ 2 := by
    dsimp [A]
    have hmul := mul_le_mul_of_nonneg_left hpSq ha
    nlinarith
  exact htail.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr hExponent) hD)

/-- The pole-removed radial continuation for one ideal has quadratic
exponential growth. -/
theorem exists_poleRemovedRadial_quadratic_bound
    (K : Type*) [Field K] [NumberField K]
    (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧ ∀ s : ℂ,
      ‖DedekindZeta.GlobalContinuation.poleRemovedRadial K 𝔞 s‖ ≤
        D * Real.exp (A * (1 + ‖s‖) ^ 2) := by
  open DedekindZeta.ConeRadialReduction DedekindZeta.MellinPrinciple in
    obtain ⟨c, α, hpair⟩ :=
      exists_isMellinPair_radialTheta (K := K) 𝔞 hne
    obtain ⟨A₀, D₀, hA₀, hD₀, htail⟩ :=
      IsMellinPair.exists_mellinTail_quadratic_bound hpair
    let C : ℂ := ((DedekindZeta.Theta.covolume K 𝔞 : ℂ)⁻¹)
    let V : ℂ := DedekindZeta.ConeRadialReduction.surfaceVolume K
    let P : ℝ := ‖V‖ + ‖C * V‖
    have hP : 0 ≤ P := add_nonneg (norm_nonneg _) (norm_nonneg _)
    let A : ℝ := A₀ + 1
    let D : ℝ := P + D₀
    have hA : 0 ≤ A := by dsimp [A]; linarith
    have hD : 0 ≤ D := by dsimp [D]; positivity
    refine ⟨A, D, hA, hD, ?_⟩
    intro s
    let R : ℝ := 1 + ‖s‖
    let X : ℝ := R ^ 2
    have hR : 1 ≤ R := by
      dsimp [R]
      linarith [norm_nonneg s]
    have hR0 : 0 ≤ R := le_trans zero_le_one hR
    have hX : 0 ≤ X := by dsimp [X]; positivity
    have hRX : R ≤ X := by dsimp [X]; nlinarith
    have hs : ‖s‖ ≤ R := by dsimp [R]; linarith
    have hs1 : ‖s - 1‖ ≤ R := by
      dsimp [R]
      simpa only [norm_one, add_comm] using norm_sub_le s 1
    have htail' :
        ‖mellinTail (radialTheta K 𝔞) (radialThetaDual K 𝔞)
          (surfaceVolume K) (surfaceVolume K) C 1 s‖ ≤
            D₀ * Real.exp (A₀ * X) := by
      simpa [C, X, R] using htail s
    have hpoly :
        ‖s * (s - 1) *
          mellinTail (radialTheta K 𝔞) (radialThetaDual K 𝔞)
            (surfaceVolume K) (surfaceVolume K) C 1 s‖ ≤
          D₀ * Real.exp (A * X) := by
      rw [norm_mul, norm_mul]
      calc
        ‖s‖ * ‖s - 1‖ *
            ‖mellinTail (radialTheta K 𝔞) (radialThetaDual K 𝔞)
              (surfaceVolume K) (surfaceVolume K) C 1 s‖ ≤
            R * R * (D₀ * Real.exp (A₀ * X)) := by
          gcongr
        _ = D₀ * (X * Real.exp (A₀ * X)) := by
          dsimp [X]
          ring
        _ ≤ D₀ * (Real.exp X * Real.exp (A₀ * X)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp X))
              (Real.exp_nonneg _)) hD₀
        _ = D₀ * Real.exp (A * X) := by
          rw [← Real.exp_add]
          dsimp [A]
          congr 2
          ring
    have hpolar : ‖-V * (s - 1) + C * V * s‖ ≤
        P * Real.exp (A * X) := by
      calc
        ‖-V * (s - 1) + C * V * s‖ ≤
            ‖-V * (s - 1)‖ + ‖C * V * s‖ := norm_add_le _ _
        _ = ‖V‖ * ‖s - 1‖ + ‖C * V‖ * ‖s‖ := by
          simp only [norm_mul, norm_neg]
        _ ≤ ‖V‖ * R + ‖C * V‖ * R :=
          add_le_add
            (mul_le_mul_of_nonneg_left hs1 (norm_nonneg _))
            (mul_le_mul_of_nonneg_left hs (norm_nonneg _))
        _ = P * R := by dsimp [P]; ring
        _ ≤ P * X := mul_le_mul_of_nonneg_left hRX hP
        _ ≤ P * Real.exp X :=
          mul_le_mul_of_nonneg_left
            ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp X)) hP
        _ ≤ P * Real.exp (A * X) := by
          apply mul_le_mul_of_nonneg_left _ hP
          apply Real.exp_le_exp.mpr
          dsimp [A]
          nlinarith [mul_nonneg hA₀ hX]
    unfold DedekindZeta.GlobalContinuation.poleRemovedRadial
    change ‖(-V * (s - 1) + C * V * s) +
      s * (s - 1) *
        mellinTail (radialTheta K 𝔞) (radialThetaDual K 𝔞)
          (surfaceVolume K) (surfaceVolume K) C 1 s‖ ≤ _
    calc
      _ ≤ ‖-V * (s - 1) + C * V * s‖ +
          ‖s * (s - 1) *
            mellinTail (radialTheta K 𝔞) (radialThetaDual K 𝔞)
              (surfaceVolume K) (surfaceVolume K) C 1 s‖ := norm_add_le _ _
      _ ≤ P * Real.exp (A * X) + D₀ * Real.exp (A * X) :=
        add_le_add hpolar hpoly
      _ = D * Real.exp (A * (1 + ‖s‖) ^ 2) := by
        dsimp [D, X, R]
        ring

/-- The elementary ideal-norm and discriminant factor in one completed
partial zeta has quadratic exponential growth. -/
theorem exists_partialFactor_quadratic_bound
    (K : Type*) [Field K] [NumberField K]
    (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧ ∀ s : ℂ,
      ‖DedekindZeta.GlobalContinuation.partialFactor K 𝔞 s‖ ≤
        D * Real.exp (A * (1 + ‖s‖) ^ 2) := by
  let N : ℂ := Ideal.absNorm 𝔞
  let Δ : ℂ := ((|NumberField.discr K| : ℤ) : ℂ)
  let LN : ℝ := |Real.log ‖N‖| + |Complex.arg N|
  let LΔ : ℝ := |Real.log ‖Δ‖| + |Complex.arg Δ|
  let A : ℝ := LN + LΔ
  let D : ℝ := ‖(1 / (NumberField.Units.torsionOrder K : ℂ))‖
  have hN : N ≠ 0 := by
    dsimp [N]
    exact_mod_cast (Ideal.absNorm_eq_zero_iff (I := 𝔞)).not.mpr hne
  have hΔ : Δ ≠ 0 := by
    dsimp [Δ]
    exact_mod_cast (abs_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hLN : 0 ≤ LN := by dsimp [LN]; positivity
  have hLΔ : 0 ≤ LΔ := by dsimp [LΔ]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := norm_nonneg _
  refine ⟨A, D, hA, hD, ?_⟩
  intro s
  let X : ℝ := (1 + ‖s‖) ^ 2
  have hhalf : ‖s / 2‖ ≤ ‖s‖ := by
    rw [norm_div]
    norm_num
  have hhalfSq : (1 + ‖s / 2‖) ^ 2 ≤ X := by
    dsimp [X]
    nlinarith [norm_nonneg s, norm_nonneg (s / 2)]
  have hNpow : ‖N ^ s‖ ≤ Real.exp (LN * X) := by
    simpa [LN, X] using norm_cpow_le_exp_quadratic hN s
  have hΔpow : ‖Δ ^ (s / 2)‖ ≤ Real.exp (LΔ * X) := by
    calc
      ‖Δ ^ (s / 2)‖ ≤
          Real.exp (LΔ * (1 + ‖s / 2‖) ^ 2) := by
        simpa [LΔ] using norm_cpow_le_exp_quadratic hΔ (s / 2)
      _ ≤ Real.exp (LΔ * X) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left hhalfSq hLΔ
  unfold DedekindZeta.GlobalContinuation.partialFactor
  change ‖(1 / (NumberField.Units.torsionOrder K : ℂ)) * N ^ s *
      Δ ^ (s / 2)‖ ≤ _
  rw [norm_mul, norm_mul]
  calc
    D * ‖N ^ s‖ * ‖Δ ^ (s / 2)‖ ≤
        D * Real.exp (LN * X) * Real.exp (LΔ * X) := by
      gcongr
    _ = D * Real.exp (A * (1 + ‖s‖) ^ 2) := by
      rw [mul_assoc, ← Real.exp_add]
      dsimp [A, X]
      congr 2
      ring

/-- A uniform quadratic exponential bound for a complex-valued function. -/
def HasQuadraticExponentialBound (f : ℂ → ℂ) : Prop :=
  ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧ ∀ s : ℂ,
    ‖f s‖ ≤ D * Real.exp (A * (1 + ‖s‖) ^ 2)

theorem hasQuadraticExponentialBound_zero :
    HasQuadraticExponentialBound (fun _ : ℂ ↦ (0 : ℂ)) := by
  refine ⟨0, 0, le_rfl, le_rfl, ?_⟩
  intro s
  simp

theorem HasQuadraticExponentialBound.add {f g : ℂ → ℂ}
    (hf : HasQuadraticExponentialBound f)
    (hg : HasQuadraticExponentialBound g) :
    HasQuadraticExponentialBound (fun s ↦ f s + g s) := by
  obtain ⟨Af, Df, hAf, hDf, hf⟩ := hf
  obtain ⟨Ag, Dg, hAg, hDg, hg⟩ := hg
  refine ⟨Af + Ag, Df + Dg, add_nonneg hAf hAg,
    add_nonneg hDf hDg, ?_⟩
  intro s
  let X : ℝ := (1 + ‖s‖) ^ 2
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hfExp : Real.exp (Af * X) ≤ Real.exp ((Af + Ag) * X) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hAg hX]
  have hgExp : Real.exp (Ag * X) ≤ Real.exp ((Af + Ag) * X) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hAf hX]
  calc
    ‖f s + g s‖ ≤ ‖f s‖ + ‖g s‖ := norm_add_le _ _
    _ ≤ Df * Real.exp (Af * X) + Dg * Real.exp (Ag * X) := by
      exact add_le_add (by simpa [X] using hf s) (by simpa [X] using hg s)
    _ ≤ Df * Real.exp ((Af + Ag) * X) +
        Dg * Real.exp ((Af + Ag) * X) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hfExp hDf)
        (mul_le_mul_of_nonneg_left hgExp hDg)
    _ = (Df + Dg) * Real.exp ((Af + Ag) * (1 + ‖s‖) ^ 2) := by
      dsimp [X]
      ring

theorem HasQuadraticExponentialBound.mul {f g : ℂ → ℂ}
    (hf : HasQuadraticExponentialBound f)
    (hg : HasQuadraticExponentialBound g) :
    HasQuadraticExponentialBound (fun s ↦ f s * g s) := by
  obtain ⟨Af, Df, hAf, hDf, hf⟩ := hf
  obtain ⟨Ag, Dg, hAg, hDg, hg⟩ := hg
  refine ⟨Af + Ag, Df * Dg, add_nonneg hAf hAg,
    mul_nonneg hDf hDg, ?_⟩
  intro s
  let X : ℝ := (1 + ‖s‖) ^ 2
  calc
    ‖f s * g s‖ = ‖f s‖ * ‖g s‖ := norm_mul _ _
    _ ≤ (Df * Real.exp (Af * X)) * (Dg * Real.exp (Ag * X)) := by
      gcongr
      · simpa [X] using hf s
      · simpa [X] using hg s
    _ = (Df * Dg) * Real.exp ((Af + Ag) * (1 + ‖s‖) ^ 2) := by
      rw [show (Df * Real.exp (Af * X)) * (Dg * Real.exp (Ag * X)) =
        (Df * Dg) * (Real.exp (Af * X) * Real.exp (Ag * X)) by ring]
      rw [← Real.exp_add]
      dsimp [X]
      congr 2
      ring

theorem hasQuadraticExponentialBound_finset_sum {ι : Type*}
    (S : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ S, HasQuadraticExponentialBound (f i)) :
    HasQuadraticExponentialBound (fun s ↦ ∑ i ∈ S, f i s) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa using hasQuadraticExponentialBound_zero
  | @insert a S ha ih =>
      have haBound : HasQuadraticExponentialBound (f a) := hf a (by simp)
      have hSBound : HasQuadraticExponentialBound (fun s ↦ ∑ i ∈ S, f i s) :=
        ih (fun i hi ↦ hf i (by simp [hi]))
      simpa [Finset.sum_insert, ha] using haBound.add hSBound

/-- The entire pole-removed completed Dedekind zeta has a global quadratic
exponential bound. -/
theorem completedZetaPoleRemoved_hasQuadraticExponentialBound
    (K : Type*) [Field K] [NumberField K] :
    HasQuadraticExponentialBound
      (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) := by
  classical
  unfold DedekindZeta.GlobalContinuation.completedZetaPoleRemoved
  apply hasQuadraticExponentialBound_finset_sum
  intro c hc
  apply HasQuadraticExponentialBound.mul
  · exact exists_partialFactor_quadratic_bound K
      (DedekindZeta.idealClassRep K c)
      (DedekindZeta.GlobalContinuation.idealClassRep_ne_zero K c)
  · exact exists_poleRemovedRadial_quadratic_bound K
      (DedekindZeta.idealClassRep K c)
      (DedekindZeta.GlobalContinuation.idealClassRep_ne_zero K c)

/-- The global bound supplies the precise family of circles used by the
completed-function Jensen argument. -/
theorem exists_completedZetaPoleRemoved_circle_growth
    (K : Type*) [Field K] [NumberField K] :
    ∃ c : ℂ, ∃ A : ℝ,
      DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K c ≠ 0 ∧
      0 ≤ A ∧
      ∀ T : ℝ, 0 ≤ T →
        ∀ z ∈ Metric.sphere c (2 * (‖c‖ + T + 2)),
          ‖DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K z‖ ≤
            Real.exp (A * (1 + T) ^ 2) := by
  obtain ⟨c, hc⟩ :=
    TraceEuclidean.v15_completedZetaPoleRemoved_exists_nonzero (K := K)
  obtain ⟨A₀, D, hA₀, hD, hglobal⟩ :=
    completedZetaPoleRemoved_hasQuadraticExponentialBound K
  let B : ℝ := 3 * ‖c‖ + 5
  let A : ℝ := D + A₀ * B ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg hD (mul_nonneg hA₀ (sq_nonneg B))
  refine ⟨c, A, hc, hA, ?_⟩
  intro T hT z hz
  have hdist : dist z c = 2 * (‖c‖ + T + 2) :=
    Metric.mem_sphere.mp hz
  have hnormSub : ‖z - c‖ = 2 * (‖c‖ + T + 2) := by
    rw [← dist_eq_norm]
    exact hdist
  have hnormZ : ‖z‖ ≤ (B - 1) * (1 + T) := by
    calc
      ‖z‖ = ‖(z - c) + c‖ := by simp
      _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
      _ = 3 * ‖c‖ + 2 * T + 4 := by rw [hnormSub]; ring
      _ ≤ (B - 1) * (1 + T) := by
        dsimp [B]
        nlinarith [norm_nonneg c]
  have hOneNorm : 1 + ‖z‖ ≤ B * (1 + T) := by
    calc
      1 + ‖z‖ ≤ 1 + (B - 1) * (1 + T) := by linarith
      _ ≤ B * (1 + T) := by nlinarith
  have hBT : 0 ≤ B * (1 + T) :=
    mul_nonneg hB (by linarith)
  have hsq : (1 + ‖z‖) ^ 2 ≤ B ^ 2 * (1 + T) ^ 2 := by
    nlinarith [norm_nonneg z]
  have hExpArgument :
      A₀ * (1 + ‖z‖) ^ 2 ≤ A₀ * B ^ 2 * (1 + T) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hsq hA₀
    nlinarith
  have hDexp : D ≤ Real.exp D := by
    exact (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp D)
  have hTSq : 1 ≤ (1 + T) ^ 2 := by nlinarith
  have hFinalArgument :
      D + A₀ * B ^ 2 * (1 + T) ^ 2 ≤ A * (1 + T) ^ 2 := by
    dsimp [A]
    nlinarith [mul_nonneg hD (sub_nonneg.mpr hTSq)]
  calc
    ‖DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K z‖ ≤
        D * Real.exp (A₀ * (1 + ‖z‖) ^ 2) := hglobal z
    _ ≤ D * Real.exp (A₀ * B ^ 2 * (1 + T) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hExpArgument) hD
    _ ≤ Real.exp D * Real.exp (A₀ * B ^ 2 * (1 + T) ^ 2) :=
      mul_le_mul_of_nonneg_right hDexp (Real.exp_nonneg _)
    _ = Real.exp (D + A₀ * B ^ 2 * (1 + T) ^ 2) :=
      (Real.exp_add _ _).symm
    _ ≤ Real.exp (A * (1 + T) ^ 2) :=
      Real.exp_le_exp.mpr hFinalArgument

/-- The theta--Mellin construction supplies the coarse quadratic zero count
needed for the Odlyzko zero sum, without an additional analytic input. -/
theorem exists_constructedDedekindZeta_quadraticCountInput
    (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 ≤ C ∧
      TraceEuclidean.V15DedekindZetaZeroOccurrence.QuadraticCountInput
        (TraceEuclidean.v15ConstructedDedekindZetaRegularization K) C := by
  obtain ⟨c, A, hc, hA, hGrowth⟩ :=
    exists_completedZetaPoleRemoved_circle_growth K
  let C : ℝ :=
    (A + |Real.log
      ‖DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K c‖|) /
        Real.log 2
  have hC : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg (add_nonneg hA (abs_nonneg _))
      (le_of_lt (Real.log_pos (by norm_num)))
  refine ⟨C, hC, ?_⟩
  exact
    TraceEuclidean.V15DedekindZetaZeroOccurrence.quadraticCount_of_completed_circle_growth
      (K := K) c hc A hA hGrowth

/-- The Odlyzko test function is absolutely summable over the actual zeros of
the constructed ordinary Dedekind-zeta regularization. -/
theorem constructedDedekindZeta_odlyzkoPhi_summable
    (K : Type*) [Field K] [NumberField K] :
    Summable (fun o : TraceEuclidean.V15DedekindZetaZeroOccurrence
      (TraceEuclidean.v15ConstructedDedekindZetaRegularization K) ↦
        TraceEuclidean.v15OdlyzkoPhi o.value) := by
  obtain ⟨c, A, hc, hA, hGrowth⟩ :=
    exists_completedZetaPoleRemoved_circle_growth K
  exact
    TraceEuclidean.V15DedekindZetaZeroOccurrence.phi_summable_of_completed_circle_growth
      (K := K) c hc A hA hGrowth

/-- After the theta--Mellin growth argument and the certified numerical
integrals, the literature's explicit formula is the sole remaining premise for
the Table 4 correction. -/
theorem v15_odlyzkoTable4_of_constructed_explicitFormula
    (hFormula : TraceEuclidean.V15OdlyzkoExplicitFormulaInput
      (fun K ↦ (∑' o : TraceEuclidean.V15DedekindZetaZeroOccurrence
        (TraceEuclidean.v15ConstructedRegularizationFamily K),
          TraceEuclidean.v15OdlyzkoPhi o.value).re)) :
    TraceEuclidean.V15OdlyzkoTable4ExplicitCorrectionInput := by
  have hExist : ∀ K : TraceEuclidean.CodedNumberField,
      ∃ c : ℂ, ∃ A : ℝ,
        DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K.1 c ≠ 0 ∧
        0 ≤ A ∧
        ∀ T : ℝ, 0 ≤ T →
          ∀ z ∈ Metric.sphere c (2 * (‖c‖ + T + 2)),
            ‖DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K.1 z‖ ≤
              Real.exp (A * (1 + T) ^ 2) := by
    intro K
    exact exists_completedZetaPoleRemoved_circle_growth K.1
  choose center A hCenter hA hGrowth using hExist
  exact TraceEuclidean.v15_odlyzkoTable4_of_constructed_completed_circle_growth
    center hCenter A hA hGrowth hFormula
      TraceEuclidean.V15OdlyzkoNumerical.abIntegralCertificate

end
end TraceEuclidean.V15MellinGrowth
