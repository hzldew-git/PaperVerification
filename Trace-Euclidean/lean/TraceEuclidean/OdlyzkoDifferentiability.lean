import TraceEuclidean.OdlyzkoKernel
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

private theorem odlyzkoHCore_hasDerivAt (t : ℝ) :
    HasDerivAt odlyzkoHCore
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
  unfold odlyzkoHCore
  convert ((hlin.mul ((hasDerivAt_const t 1).add (hcos.div_const 2))).div_const 3).add
    (hsin.div_const (2 * Real.pi)) using 1
  all_goals first | rfl | (simp only [Pi.add_apply]; ring)

private theorem odlyzkoHCore_hasDerivAt_zero :
    HasDerivAt odlyzkoHCore 0 0 := by
  convert odlyzkoHCore_hasDerivAt 0 using 1
  · simp only [mul_zero, Real.cos_zero, Real.sin_zero, zero_mul, zero_div]
    field_simp [Real.pi_ne_zero]
    ring

private theorem odlyzkoHCore_hasDerivAt_two :
    HasDerivAt odlyzkoHCore 0 2 := by
  convert odlyzkoHCore_hasDerivAt 2 using 1
  · rw [show Real.pi * (2 : ℝ) = 2 * Real.pi by ring,
      Real.cos_two_pi, Real.sin_two_pi]
    field_simp [Real.pi_ne_zero]
    ring

private theorem odlyzkoHCore_differentiable :
    Differentiable ℝ odlyzkoHCore :=
  fun t ↦ (odlyzkoHCore_hasDerivAt t).differentiableAt

def odlyzkoHRight (x : ℝ) : ℝ :=
  if x ≤ 2 then odlyzkoHCore x else 0

def odlyzkoHMiddle (x : ℝ) : ℝ :=
  if x ≤ 0 then odlyzkoHCore (-x) else odlyzkoHRight x

def odlyzkoHPiecewise (x : ℝ) : ℝ :=
  if x ≤ -2 then 0 else odlyzkoHMiddle x

private theorem odlyzkoHRight_differentiable :
    Differentiable ℝ odlyzkoHRight := by
  unfold odlyzkoHRight
  apply differentiable_if_le odlyzkoHCore (fun _ ↦ 0) 2
    odlyzkoHCore_differentiable (differentiable_const 0)
  · exact odlyzkoHCore_two
  · rw [odlyzkoHCore_hasDerivAt_two.deriv]
    simp

private theorem odlyzkoHRight_hasDerivAt_zero :
    HasDerivAt odlyzkoHRight 0 0 := by
  apply odlyzkoHCore_hasDerivAt_zero.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 2)] with x hx
  change x < 2 at hx
  simp [odlyzkoHRight, hx.le]

private theorem odlyzkoHMiddle_differentiable :
    Differentiable ℝ odlyzkoHMiddle := by
  unfold odlyzkoHMiddle
  apply differentiable_if_le (fun x ↦ odlyzkoHCore (-x)) odlyzkoHRight 0
    (odlyzkoHCore_differentiable.comp differentiable_neg)
    odlyzkoHRight_differentiable
  · simp [odlyzkoHRight]
  · have hleft : HasDerivAt (fun x : ℝ ↦ odlyzkoHCore (-x)) 0 0 := by
      have hcore : HasDerivAt odlyzkoHCore 0 ((-id) (0 : ℝ)) := by
        simpa using odlyzkoHCore_hasDerivAt_zero
      simpa only [Function.comp_def, Pi.neg_apply, id_eq, zero_mul] using
        hcore.comp 0 ((hasDerivAt_id (0 : ℝ)).neg)
    rw [hleft.deriv, odlyzkoHRight_hasDerivAt_zero.deriv]

private theorem odlyzkoHMiddle_hasDerivAt_neg_two :
    HasDerivAt odlyzkoHMiddle 0 (-2) := by
  have hleft : HasDerivAt (fun x : ℝ ↦ odlyzkoHCore (-x)) 0 (-2) := by
    have hcore : HasDerivAt odlyzkoHCore 0 ((-id) (-2 : ℝ)) := by
      simpa using odlyzkoHCore_hasDerivAt_two
    simpa only [Function.comp_def, Pi.neg_apply, id_eq, zero_mul] using
      hcore.comp (-2) ((hasDerivAt_id (-2 : ℝ)).neg)
  apply hleft.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds (by norm_num : (-2 : ℝ) < 0)] with x hx
  change x < 0 at hx
  simp [odlyzkoHMiddle, hx.le]

private theorem odlyzkoHPiecewise_differentiable :
    Differentiable ℝ odlyzkoHPiecewise := by
  unfold odlyzkoHPiecewise
  apply differentiable_if_le (fun _ ↦ 0) odlyzkoHMiddle (-2)
    (differentiable_const 0) odlyzkoHMiddle_differentiable
  · simp [odlyzkoHMiddle, odlyzkoHCore_two]
  · rw [odlyzkoHMiddle_hasDerivAt_neg_two.deriv]
    simp

theorem odlyzkoH_eq_piecewise (x : ℝ) :
    odlyzkoH x = odlyzkoHPiecewise x := by
  by_cases hx₁ : x ≤ -2
  · rcases lt_or_eq_of_le hx₁ with hlt | heq
    · have habs : 2 < |x| := by rw [abs_of_neg (by linarith : x < 0)]; linarith
      rw [odlyzkoH_eq_zero_of_two_lt_abs habs]
      simp [odlyzkoHPiecewise, hx₁]
    · subst x
      simp [odlyzkoHPiecewise, odlyzkoH, odlyzkoHCore_two]
  · have hx₁' : -2 < x := lt_of_not_ge hx₁
    by_cases hx₀ : x ≤ 0
    · have habs : |x| = -x := abs_of_nonpos hx₀
      have hx₂ : |x| ≤ 2 := by rw [habs]; linarith
      rw [odlyzkoH, if_pos hx₂, habs]
      simp [odlyzkoHPiecewise, odlyzkoHMiddle, hx₁, hx₀]
    · have hx₀' : 0 < x := lt_of_not_ge hx₀
      by_cases hx₂ : x ≤ 2
      · have habs : |x| = x := abs_of_pos hx₀'
        simp [odlyzkoH, odlyzkoHPiecewise, odlyzkoHMiddle,
          odlyzkoHRight, hx₁, hx₀, hx₂, habs]
      · have habs : 2 < |x| := by rw [abs_of_pos hx₀']; exact lt_of_not_ge hx₂
        rw [odlyzkoH_eq_zero_of_two_lt_abs habs]
        simp [odlyzkoHPiecewise, odlyzkoHMiddle,
          odlyzkoHRight, hx₁, hx₀, hx₂]

/-- The source's unconditional auxiliary function is differentiable at every
real argument, including `0` and both support endpoints. -/
theorem odlyzkoH_differentiable : Differentiable ℝ odlyzkoH := by
  intro x
  rw [show odlyzkoH = odlyzkoHPiecewise from funext odlyzkoH_eq_piecewise]
  exact odlyzkoHPiecewise_differentiable x

/-- The `b = 4` unconditional test function meets the global differentiability
hypothesis of Odlyzko's explicit formula. -/
theorem odlyzkoF4_differentiable : Differentiable ℝ odlyzkoF4 := by
  unfold odlyzkoF4
  exact (odlyzkoH_differentiable.comp (differentiable_id.div_const 4)).div
    (Real.differentiable_cosh.comp (differentiable_id.div_const 2))
    (fun x ↦ (Real.cosh_pos (x / 2)).ne')

/-- Differentiation preserves compact support for the exact test function. -/
theorem odlyzkoF4_deriv_hasCompactSupport :
    HasCompactSupport (deriv odlyzkoF4) :=
  odlyzkoF4_hasCompactSupport.deriv

/-- Outside the explicit support interval, the test function and its derivative
both vanish. -/
theorem odlyzkoF4_and_deriv_eq_zero_of_eight_lt_abs {x : ℝ}
    (hx : 8 < |x|) :
    odlyzkoF4 x = 0 ∧ deriv odlyzkoF4 x = 0 := by
  refine ⟨odlyzkoF4_eq_zero_of_eight_lt_abs hx, ?_⟩
  apply deriv_of_notMem_tsupport
  have hsubset : tsupport odlyzkoF4 ⊆ Set.Icc (-8) 8 := by
    apply closure_minimal _ isClosed_Icc
    intro y hy
    change -8 ≤ y ∧ y ≤ 8
    rw [← abs_le]
    by_contra hnot
    exact hy (odlyzkoF4_eq_zero_of_eight_lt_abs (lt_of_not_ge hnot))
  intro hmem
  have hbounds := hsubset hmem
  have habs : |x| ≤ 8 := (abs_le).2 hbounds
  linarith

/-- The precise `b = 4` kernel satisfies the eventual exponential bound in
Odlyzko's 1990 survey, equation (2.1), with `c = ε = 1`. -/
theorem odlyzkoF4_exp_decay (x : ℝ) (hx : 8 < |x|) :
    |odlyzkoF4 x| ≤ Real.exp (-(1 / 2 + 1) * |x|) ∧
      |deriv odlyzkoF4 x| ≤ Real.exp (-(1 / 2 + 1) * |x|) := by
  obtain ⟨hf, hd⟩ := odlyzkoF4_and_deriv_eq_zero_of_eight_lt_abs hx
  rw [hf, hd]
  simp only [abs_zero]
  exact ⟨(Real.exp_pos _).le, (Real.exp_pos _).le⟩

/-- All elementary source hypotheses on the `b = 4` test function in
Odlyzko's survey, equation (2.1), are packaged in one theorem. The eventual
exponential bound uses the explicit positive constants `c = ε = 1`. -/
theorem odlyzkoF4_source_test_hypotheses :
    (∀ x : ℝ, odlyzkoF4 (-x) = odlyzkoF4 x) ∧
      odlyzkoF4 0 = 1 ∧ Differentiable ℝ odlyzkoF4 ∧
      ∀ x : ℝ, 8 < |x| →
        |odlyzkoF4 x| ≤ Real.exp (-(1 / 2 + 1) * |x|) ∧
          |deriv odlyzkoF4 x| ≤ Real.exp (-(1 / 2 + 1) * |x|) := by
  exact ⟨odlyzkoF4_even, odlyzkoF4_zero,
    odlyzkoF4_differentiable, odlyzkoF4_exp_decay⟩

end
end TraceEuclidean
