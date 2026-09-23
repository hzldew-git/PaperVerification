import TraceEuclidean.V15OdlyzkoKernel
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Differentiability of the unconditional Odlyzko test function

The explicit formula in Odlyzko's 1990 survey assumes that its test function
is differentiable, and that the function and its derivative decay faster than
an exponential of exponent `1/2 + ε`. For the compactly supported `b = 4`
kernel the decay follows once global differentiability has been proved.
-/

namespace TraceEuclidean

noncomputable section
open scoped Topology

private theorem hasDerivAt_if_le (f g : ℝ → ℝ) (a d : ℝ)
    (hf : HasDerivAt f d a) (hg : HasDerivAt g d a)
    (hfg : f a = g a) :
    HasDerivAt (fun x ↦ if x ≤ a then f x else g x) d a := by
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · have heq : (slope (fun x ↦ if x ≤ a then f x else g x) a) =ᶠ[𝓝[<] a]
        slope f a := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      change x < a at hx
      simp [slope_def_module, hx.le]
    exact hf.tendsto_slope.mono_left (nhdsLT_le_nhdsNE a) |>.congr' heq.symm
  · have heq : (slope (fun x ↦ if x ≤ a then f x else g x) a) =ᶠ[𝓝[>] a]
        slope g a := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      change a < x at hx
      simp [slope_def_module, not_le_of_gt hx, hfg]
    exact hg.tendsto_slope.mono_left (nhdsGT_le_nhdsNE a) |>.congr' heq.symm

private theorem differentiable_if_le (f g : ℝ → ℝ) (a : ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hfg : f a = g a) (hderiv : deriv f a = deriv g a) :
    Differentiable ℝ (fun x ↦ if x ≤ a then f x else g x) := by
  intro x
  rcases lt_trichotomy x a with hlt | heq | hgt
  · have hlocal : (fun y ↦ if y ≤ a then f y else g y) =ᶠ[𝓝 x] f := by
      filter_upwards [Iio_mem_nhds hlt] with y hy
      change y < a at hy
      simp [hy.le]
    exact (hf x).congr_of_eventuallyEq hlocal
  · subst x
    exact (hasDerivAt_if_le f g a (deriv f a)
      (hf a).hasDerivAt (hderiv ▸ (hg a).hasDerivAt) hfg).differentiableAt
  · have hlocal : (fun y ↦ if y ≤ a then f y else g y) =ᶠ[𝓝 x] g := by
      filter_upwards [Ioi_mem_nhds hgt] with y hy
      change a < y at hy
      simp [not_le_of_gt hy]
    exact (hg x).congr_of_eventuallyEq hlocal

private theorem v15OdlyzkoHCore_hasDerivAt (t : ℝ) :
    HasDerivAt v15OdlyzkoHCore
      (-(1 + Real.cos (Real.pi * t) / 2) / 3 -
        (2 - t) * (Real.sin (Real.pi * t) * Real.pi / 2) / 3 +
        Real.cos (Real.pi * t) * Real.pi / (2 * Real.pi)) t := by
  have harg : HasDerivAt (fun x : ℝ ↦ Real.pi * x) Real.pi t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul Real.pi
  have hcos : HasDerivAt (fun x : ℝ ↦ Real.cos (Real.pi * x))
      (-Real.sin (Real.pi * t) * Real.pi) t := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_cos (Real.pi * t)).comp t harg
  have hsin : HasDerivAt (fun x : ℝ ↦ Real.sin (Real.pi * x))
      (Real.cos (Real.pi * t) * Real.pi) t := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_sin (Real.pi * t)).comp t harg
  have hlin : HasDerivAt (fun x : ℝ ↦ 2 - x) (-1) t := by
    convert (hasDerivAt_const t 2).sub (hasDerivAt_id t) using 1
    all_goals first | rfl | norm_num
  unfold v15OdlyzkoHCore
  convert ((hlin.mul ((hasDerivAt_const t 1).add (hcos.div_const 2))).div_const 3).add
    (hsin.div_const (2 * Real.pi)) using 1
  all_goals first | rfl | (simp only [Pi.add_apply]; ring)

private theorem v15OdlyzkoHCore_hasDerivAt_zero :
    HasDerivAt v15OdlyzkoHCore 0 0 := by
  convert v15OdlyzkoHCore_hasDerivAt 0 using 1
  · simp only [mul_zero, Real.cos_zero, Real.sin_zero, zero_mul, zero_div]
    field_simp [Real.pi_ne_zero]
    ring

private theorem v15OdlyzkoHCore_hasDerivAt_two :
    HasDerivAt v15OdlyzkoHCore 0 2 := by
  convert v15OdlyzkoHCore_hasDerivAt 2 using 1
  · rw [show Real.pi * (2 : ℝ) = 2 * Real.pi by ring,
      Real.cos_two_pi, Real.sin_two_pi]
    field_simp [Real.pi_ne_zero]
    ring

private theorem v15OdlyzkoHCore_differentiable :
    Differentiable ℝ v15OdlyzkoHCore :=
  fun t ↦ (v15OdlyzkoHCore_hasDerivAt t).differentiableAt

def v15OdlyzkoHRight (x : ℝ) : ℝ :=
  if x ≤ 2 then v15OdlyzkoHCore x else 0

def v15OdlyzkoHMiddle (x : ℝ) : ℝ :=
  if x ≤ 0 then v15OdlyzkoHCore (-x) else v15OdlyzkoHRight x

def v15OdlyzkoHPiecewise (x : ℝ) : ℝ :=
  if x ≤ -2 then 0 else v15OdlyzkoHMiddle x

private theorem v15OdlyzkoHRight_differentiable :
    Differentiable ℝ v15OdlyzkoHRight := by
  unfold v15OdlyzkoHRight
  apply differentiable_if_le v15OdlyzkoHCore (fun _ ↦ 0) 2
    v15OdlyzkoHCore_differentiable (differentiable_const 0)
  · exact v15OdlyzkoHCore_two
  · rw [v15OdlyzkoHCore_hasDerivAt_two.deriv]
    simp

private theorem v15OdlyzkoHRight_hasDerivAt_zero :
    HasDerivAt v15OdlyzkoHRight 0 0 := by
  apply v15OdlyzkoHCore_hasDerivAt_zero.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 2)] with x hx
  change x < 2 at hx
  simp [v15OdlyzkoHRight, hx.le]

private theorem v15OdlyzkoHMiddle_differentiable :
    Differentiable ℝ v15OdlyzkoHMiddle := by
  unfold v15OdlyzkoHMiddle
  apply differentiable_if_le (fun x ↦ v15OdlyzkoHCore (-x)) v15OdlyzkoHRight 0
    (v15OdlyzkoHCore_differentiable.comp differentiable_neg)
    v15OdlyzkoHRight_differentiable
  · simp [v15OdlyzkoHRight]
  · have hleft : HasDerivAt (fun x : ℝ ↦ v15OdlyzkoHCore (-x)) 0 0 := by
      have hcore : HasDerivAt v15OdlyzkoHCore 0 ((-id) (0 : ℝ)) := by
        simpa using v15OdlyzkoHCore_hasDerivAt_zero
      simpa only [Function.comp_def, Pi.neg_apply, id_eq, zero_mul] using
        hcore.comp 0 ((hasDerivAt_id (0 : ℝ)).neg)
    rw [hleft.deriv, v15OdlyzkoHRight_hasDerivAt_zero.deriv]

private theorem v15OdlyzkoHMiddle_hasDerivAt_neg_two :
    HasDerivAt v15OdlyzkoHMiddle 0 (-2) := by
  have hleft : HasDerivAt (fun x : ℝ ↦ v15OdlyzkoHCore (-x)) 0 (-2) := by
    have hcore : HasDerivAt v15OdlyzkoHCore 0 ((-id) (-2 : ℝ)) := by
      simpa using v15OdlyzkoHCore_hasDerivAt_two
    simpa only [Function.comp_def, Pi.neg_apply, id_eq, zero_mul] using
      hcore.comp (-2) ((hasDerivAt_id (-2 : ℝ)).neg)
  apply hleft.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds (by norm_num : (-2 : ℝ) < 0)] with x hx
  change x < 0 at hx
  simp [v15OdlyzkoHMiddle, hx.le]

private theorem v15OdlyzkoHPiecewise_differentiable :
    Differentiable ℝ v15OdlyzkoHPiecewise := by
  unfold v15OdlyzkoHPiecewise
  apply differentiable_if_le (fun _ ↦ 0) v15OdlyzkoHMiddle (-2)
    (differentiable_const 0) v15OdlyzkoHMiddle_differentiable
  · simp [v15OdlyzkoHMiddle, v15OdlyzkoHCore_two]
  · rw [v15OdlyzkoHMiddle_hasDerivAt_neg_two.deriv]
    simp

theorem v15OdlyzkoH_eq_piecewise (x : ℝ) :
    v15OdlyzkoH x = v15OdlyzkoHPiecewise x := by
  by_cases hx₁ : x ≤ -2
  · rcases lt_or_eq_of_le hx₁ with hlt | heq
    · have habs : 2 < |x| := by rw [abs_of_neg (by linarith : x < 0)]; linarith
      rw [v15OdlyzkoH_eq_zero_of_two_lt_abs habs]
      simp [v15OdlyzkoHPiecewise, hx₁]
    · subst x
      simp [v15OdlyzkoHPiecewise, v15OdlyzkoH, v15OdlyzkoHCore_two]
  · have hx₁' : -2 < x := lt_of_not_ge hx₁
    by_cases hx₀ : x ≤ 0
    · have habs : |x| = -x := abs_of_nonpos hx₀
      have hx₂ : |x| ≤ 2 := by rw [habs]; linarith
      rw [v15OdlyzkoH, if_pos hx₂, habs]
      simp [v15OdlyzkoHPiecewise, v15OdlyzkoHMiddle, hx₁, hx₀]
    · have hx₀' : 0 < x := lt_of_not_ge hx₀
      by_cases hx₂ : x ≤ 2
      · have habs : |x| = x := abs_of_pos hx₀'
        simp [v15OdlyzkoH, v15OdlyzkoHPiecewise, v15OdlyzkoHMiddle,
          v15OdlyzkoHRight, hx₁, hx₀, hx₂, habs]
      · have habs : 2 < |x| := by rw [abs_of_pos hx₀']; exact lt_of_not_ge hx₂
        rw [v15OdlyzkoH_eq_zero_of_two_lt_abs habs]
        simp [v15OdlyzkoHPiecewise, v15OdlyzkoHMiddle,
          v15OdlyzkoHRight, hx₁, hx₀, hx₂]

/-- The source's unconditional auxiliary function is differentiable at every
real argument, including `0` and both support endpoints. -/
theorem v15OdlyzkoH_differentiable : Differentiable ℝ v15OdlyzkoH := by
  intro x
  rw [show v15OdlyzkoH = v15OdlyzkoHPiecewise from funext v15OdlyzkoH_eq_piecewise]
  exact v15OdlyzkoHPiecewise_differentiable x

/-- The `b = 4` unconditional test function meets the global differentiability
hypothesis of Odlyzko's explicit formula. -/
theorem v15OdlyzkoF4_differentiable : Differentiable ℝ v15OdlyzkoF4 := by
  unfold v15OdlyzkoF4
  exact (v15OdlyzkoH_differentiable.comp (differentiable_id.div_const 4)).div
    (Real.differentiable_cosh.comp (differentiable_id.div_const 2))
    (fun x ↦ (Real.cosh_pos (x / 2)).ne')

/-- Differentiation preserves compact support for the exact test function. -/
theorem v15OdlyzkoF4_deriv_hasCompactSupport :
    HasCompactSupport (deriv v15OdlyzkoF4) :=
  v15OdlyzkoF4_hasCompactSupport.deriv

/-- Outside the explicit support interval, the test function and its derivative
both vanish. -/
theorem v15OdlyzkoF4_and_deriv_eq_zero_of_eight_lt_abs {x : ℝ}
    (hx : 8 < |x|) :
    v15OdlyzkoF4 x = 0 ∧ deriv v15OdlyzkoF4 x = 0 := by
  refine ⟨v15OdlyzkoF4_eq_zero_of_eight_lt_abs hx, ?_⟩
  apply deriv_of_notMem_tsupport
  have hsubset : tsupport v15OdlyzkoF4 ⊆ Set.Icc (-8) 8 := by
    apply closure_minimal _ isClosed_Icc
    intro y hy
    change -8 ≤ y ∧ y ≤ 8
    rw [← abs_le]
    by_contra hnot
    exact hy (v15OdlyzkoF4_eq_zero_of_eight_lt_abs (lt_of_not_ge hnot))
  intro hmem
  have hbounds := hsubset hmem
  have habs : |x| ≤ 8 := (abs_le).2 hbounds
  linarith

/-- The precise `b = 4` kernel satisfies the eventual exponential bound in
Odlyzko's 1990 survey, equation (2.1), with `c = ε = 1`. -/
theorem v15OdlyzkoF4_exp_decay (x : ℝ) (hx : 8 < |x|) :
    |v15OdlyzkoF4 x| ≤ Real.exp (-(1 / 2 + 1) * |x|) ∧
      |deriv v15OdlyzkoF4 x| ≤ Real.exp (-(1 / 2 + 1) * |x|) := by
  obtain ⟨hf, hd⟩ := v15OdlyzkoF4_and_deriv_eq_zero_of_eight_lt_abs hx
  rw [hf, hd]
  simp only [abs_zero]
  exact ⟨(Real.exp_pos _).le, (Real.exp_pos _).le⟩

/-- All elementary source hypotheses on the `b = 4` test function in
Odlyzko's survey, equation (2.1), are packaged in one theorem. The eventual
exponential bound uses the explicit positive constants `c = ε = 1`. -/
theorem v15OdlyzkoF4_source_test_hypotheses :
    (∀ x : ℝ, v15OdlyzkoF4 (-x) = v15OdlyzkoF4 x) ∧
      v15OdlyzkoF4 0 = 1 ∧ Differentiable ℝ v15OdlyzkoF4 ∧
      ∀ x : ℝ, 8 < |x| →
        |v15OdlyzkoF4 x| ≤ Real.exp (-(1 / 2 + 1) * |x|) ∧
          |deriv v15OdlyzkoF4 x| ≤ Real.exp (-(1 / 2 + 1) * |x|) := by
  exact ⟨v15OdlyzkoF4_even, v15OdlyzkoF4_zero,
    v15OdlyzkoF4_differentiable, v15OdlyzkoF4_exp_decay⟩

end
end TraceEuclidean
