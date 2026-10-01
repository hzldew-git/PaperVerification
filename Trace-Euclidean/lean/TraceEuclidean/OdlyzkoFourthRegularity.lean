import TraceEuclidean.OdlyzkoDifferentiability
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Fourth-order boundary data for Odlyzko's compact kernel

The printed auxiliary function is smooth on its core interval. Its odd
derivatives of orders one and three vanish at the reflection point, and all
derivatives through order four vanish at the support endpoint. These exact
identities are the matching data needed to glue a global `C⁴` kernel.
-/

namespace TraceEuclidean

noncomputable section
open scoped Topology

private def hCoreD1 (t : ℝ) : ℝ :=
  (-2 + 2 * Real.cos (Real.pi * t) +
    Real.pi * (t - 2) * Real.sin (Real.pi * t)) / 6

private def hCoreD2 (t : ℝ) : ℝ :=
  Real.pi * (Real.pi * (t - 2) * Real.cos (Real.pi * t) -
    Real.sin (Real.pi * t)) / 6

private def hCoreD3 (t : ℝ) : ℝ :=
  -(Real.pi ^ 3 * (t - 2) * Real.sin (Real.pi * t)) / 6

private def hCoreD4 (t : ℝ) : ℝ :=
  -(Real.pi ^ 3 *
    (Real.pi * (t - 2) * Real.cos (Real.pi * t) +
      Real.sin (Real.pi * t))) / 6

private theorem h_arg_hasDerivAt (t : ℝ) :
    HasDerivAt (fun x : ℝ ↦ Real.pi * x) Real.pi t := by
  simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul Real.pi

private theorem h_cos_hasDerivAt (t : ℝ) :
    HasDerivAt (fun x : ℝ ↦ Real.cos (Real.pi * x))
      (-Real.sin (Real.pi * t) * Real.pi) t := by
  simpa only [Function.comp_def] using
    (Real.hasDerivAt_cos (Real.pi * t)).comp t (h_arg_hasDerivAt t)

private theorem h_sin_hasDerivAt (t : ℝ) :
    HasDerivAt (fun x : ℝ ↦ Real.sin (Real.pi * x))
      (Real.cos (Real.pi * t) * Real.pi) t := by
  simpa only [Function.comp_def] using
    (Real.hasDerivAt_sin (Real.pi * t)).comp t (h_arg_hasDerivAt t)

theorem odlyzkoHCore_hasDerivAt_d1 (t : ℝ) :
    HasDerivAt odlyzkoHCore (hCoreD1 t) t := by
  have hlin : HasDerivAt (fun x : ℝ ↦ 2 - x) (-1) t := by
    convert (hasDerivAt_const t 2).sub (hasDerivAt_id t) using 1
    all_goals first | rfl | norm_num
  unfold odlyzkoHCore hCoreD1
  convert ((hlin.mul ((hasDerivAt_const t 1).add
    ((h_cos_hasDerivAt t).div_const 2))).div_const 3).add
      ((h_sin_hasDerivAt t).div_const (2 * Real.pi)) using 1
  all_goals first | rfl | (dsimp; field_simp [Real.pi_ne_zero]; ring)

theorem hCoreD1_hasDerivAt_d2 (t : ℝ) :
    HasDerivAt hCoreD1 (hCoreD2 t) t := by
  have hlin : HasDerivAt (fun x : ℝ ↦ x - 2) 1 t := by
    convert (hasDerivAt_id t).sub (hasDerivAt_const t 2) using 1
    all_goals first | rfl | norm_num
  unfold hCoreD1 hCoreD2
  convert (((hasDerivAt_const t (-2)).add
      ((h_cos_hasDerivAt t).const_mul 2)).add
      (((hlin.mul (h_sin_hasDerivAt t)).const_mul Real.pi))).div_const 6 using 1
  all_goals first | rfl | (funext x; simp only [Pi.add_apply, Pi.mul_apply]; ring) | ring

theorem hCoreD2_hasDerivAt_d3 (t : ℝ) :
    HasDerivAt hCoreD2 (hCoreD3 t) t := by
  have hlin : HasDerivAt (fun x : ℝ ↦ x - 2) 1 t := by
    convert (hasDerivAt_id t).sub (hasDerivAt_const t 2) using 1
    all_goals first | rfl | norm_num
  unfold hCoreD2 hCoreD3
  convert (((hlin.mul (h_cos_hasDerivAt t)).const_mul Real.pi).sub
      (h_sin_hasDerivAt t)).const_mul Real.pi |>.div_const 6 using 1
  all_goals first | rfl | (funext x; simp only [Pi.mul_apply, Pi.sub_apply]; ring) | ring

theorem hCoreD3_hasDerivAt_d4 (t : ℝ) :
    HasDerivAt hCoreD3 (hCoreD4 t) t := by
  have hlin : HasDerivAt (fun x : ℝ ↦ x - 2) 1 t := by
    convert (hasDerivAt_id t).sub (hasDerivAt_const t 2) using 1
    all_goals first | rfl | norm_num
  unfold hCoreD3 hCoreD4
  convert ((hlin.mul (h_sin_hasDerivAt t)).const_mul (-(Real.pi ^ 3)))
      |>.div_const 6 using 1
  all_goals first | rfl | (funext x; simp only [Pi.mul_apply]; ring) | ring

/-- Mathematica cross-check: core derivative orders zero through four have
endpoint values `(1,0,-π²/3,0,π⁴/3)` at zero and all zero at two. -/
theorem odlyzkoHCore_fourth_order_boundary_data :
    odlyzkoHCore 0 = 1 ∧ hCoreD1 0 = 0 ∧
      hCoreD2 0 = -(Real.pi ^ 2) / 3 ∧
      hCoreD3 0 = 0 ∧ hCoreD4 0 = Real.pi ^ 4 / 3 ∧
      odlyzkoHCore 2 = 0 ∧ hCoreD1 2 = 0 ∧
      hCoreD2 2 = 0 ∧ hCoreD3 2 = 0 ∧
      hCoreD4 2 = 0 := by
  have hcos : Real.cos (Real.pi * 2) = 1 := by
    simpa only [mul_comm] using Real.cos_two_pi
  have hsin : Real.sin (Real.pi * 2) = 0 := by
    simpa only [mul_comm] using Real.sin_two_pi
  simp [odlyzkoHCore, hCoreD1, hCoreD2, hCoreD3,
    hCoreD4, hcos, hsin]
  constructor
  · ring
  constructor
  · ring
  · ring

/-- The printed trigonometric core is smooth to every finite order. -/
theorem odlyzkoHCore_contDiff : ContDiff ℝ 4 odlyzkoHCore := by
  unfold odlyzkoHCore
  fun_prop

private theorem fourth_hasDerivAt_if_le (f g : ℝ → ℝ) (a d : ℝ)
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

private theorem fourth_hasDerivAt_if_le_all (f g : ℝ → ℝ) (a : ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hfg : f a = g a) (hderiv : deriv f a = deriv g a) (x : ℝ) :
    HasDerivAt (fun y ↦ if y ≤ a then f y else g y)
      (if x ≤ a then deriv f x else deriv g x) x := by
  rcases lt_trichotomy x a with hlt | heq | hgt
  · have hlocal : (fun y ↦ if y ≤ a then f y else g y) =ᶠ[𝓝 x] f := by
      filter_upwards [Iio_mem_nhds hlt] with y hy
      change y < a at hy
      simp [hy.le]
    simpa [hlt.le] using (hf x).hasDerivAt.congr_of_eventuallyEq hlocal
  · subst x
    simpa using fourth_hasDerivAt_if_le f g a (deriv f a)
      (hf a).hasDerivAt (hderiv ▸ (hg a).hasDerivAt) hfg
  · have hlocal : (fun y ↦ if y ≤ a then f y else g y) =ᶠ[𝓝 x] g := by
      filter_upwards [Ioi_mem_nhds hgt] with y hy
      change a < y at hy
      simp [not_le_of_gt hy]
    simpa [not_le_of_gt hgt] using (hg x).hasDerivAt.congr_of_eventuallyEq hlocal

/-- A fourth-order one-dimensional gluing criterion: matching derivatives
through order four at the seam make the left/right splice `C⁴`. -/
theorem fourth_contDiff_if_le (f g : ℝ → ℝ) (a : ℝ)
    (hf : ContDiff ℝ 4 f) (hg : ContDiff ℝ 4 g)
    (hjets : ∀ k : ℕ, k ≤ 4 → iteratedDeriv k f a = iteratedDeriv k g a) :
    ContDiff ℝ 4 (fun x ↦ if x ≤ a then f x else g x) := by
  let h : ℝ → ℝ := fun x ↦ if x ≤ a then f x else g x
  let jet (k : ℕ) : ℝ → ℝ :=
    fun x ↦ if x ≤ a then iteratedDeriv k f x else iteratedDeriv k g x
  have hJetDeriv (k : ℕ) (hk : k < 4) :
      Differentiable ℝ (jet k) ∧ deriv (jet k) = jet (k + 1) := by
    have hk' : (k : WithTop ℕ∞) < 4 := by exact_mod_cast hk
    have hdf := hf.differentiable_iteratedDeriv k hk'
    have hdg := hg.differentiable_iteratedDeriv k hk'
    have hvalue := hjets k hk.le
    have hderiv : deriv (iteratedDeriv k f) a =
        deriv (iteratedDeriv k g) a := by
      simpa only [← iteratedDeriv_succ] using hjets (k + 1) hk
    have hderivAt := fourth_hasDerivAt_if_le_all
      (iteratedDeriv k f) (iteratedDeriv k g) a hdf hdg hvalue hderiv
    constructor
    · intro x
      exact (hderivAt x).differentiableAt
    · funext x
      simpa only [jet, iteratedDeriv_succ] using (hderivAt x).deriv
  have hJet (k : ℕ) (hk : k ≤ 4) : iteratedDeriv k h = jet k := by
    induction k with
    | zero =>
        funext x
        simp only [iteratedDeriv_zero, h, jet]
    | succ k ih =>
        have hk' : k < 4 := Nat.lt_of_succ_le hk
        rw [iteratedDeriv_succ, ih hk'.le]
        exact (hJetDeriv k hk').2
  apply contDiff_nat_iff_iteratedDeriv.2
  constructor
  · intro k hk
    rw [hJet k hk]
    have hk' : (k : WithTop ℕ∞) ≤ 4 := by exact_mod_cast hk
    have hcf := hf.continuous_iteratedDeriv k hk'
    have hcg := hg.continuous_iteratedDeriv k hk'
    change Continuous (fun x ↦ if x ≤ a then iteratedDeriv k f x
      else iteratedDeriv k g x)
    apply hcf.if _ hcg
    intro x hx
    have hxa : x = a := Set.mem_singleton_iff.mp (frontier_Iic_subset a hx)
    simpa only [hxa] using hjets k hk
  · intro k hk
    rw [hJet k hk.le]
    exact (hJetDeriv k hk).1

private theorem hCore_deriv_d1 : deriv odlyzkoHCore = hCoreD1 := by
  funext t
  exact (odlyzkoHCore_hasDerivAt_d1 t).deriv

private theorem hCore_deriv_d2 : deriv hCoreD1 = hCoreD2 := by
  funext t
  exact (hCoreD1_hasDerivAt_d2 t).deriv

private theorem hCore_deriv_d3 : deriv hCoreD2 = hCoreD3 := by
  funext t
  exact (hCoreD2_hasDerivAt_d3 t).deriv

private theorem hCore_deriv_d4 : deriv hCoreD3 = hCoreD4 := by
  funext t
  exact (hCoreD3_hasDerivAt_d4 t).deriv

private theorem hCore_iteratedDeriv_at_two (k : ℕ) (hk : k ≤ 4) :
    iteratedDeriv k odlyzkoHCore 2 = 0 := by
  obtain ⟨_, _, _, _, _, h₀, h₁, h₂, h₃, h₄⟩ :=
    odlyzkoHCore_fourth_order_boundary_data
  interval_cases k <;>
    simp [iteratedDeriv_succ, hCore_deriv_d1, hCore_deriv_d2,
      hCore_deriv_d3, hCore_deriv_d4, h₀, h₁, h₂, h₃, h₄]

private theorem hCore_iteratedDeriv_even_at_zero (k : ℕ) (hk : k ≤ 4) :
    (-1 : ℝ) ^ k * iteratedDeriv k odlyzkoHCore 0 =
      iteratedDeriv k odlyzkoHCore 0 := by
  obtain ⟨_, h₁, _, h₃, _, _, _, _, _, _⟩ :=
    odlyzkoHCore_fourth_order_boundary_data
  interval_cases k
  all_goals simp [iteratedDeriv_succ, hCore_deriv_d1, hCore_deriv_d2,
    hCore_deriv_d3, hCore_deriv_d4, h₁, h₃] <;> ring

private theorem odlyzkoHRight_contDiff_four : ContDiff ℝ 4 odlyzkoHRight := by
  unfold odlyzkoHRight
  apply fourth_contDiff_if_le odlyzkoHCore (fun _ ↦ 0) 2
    odlyzkoHCore_contDiff contDiff_const
  intro k hk
  rw [hCore_iteratedDeriv_at_two k hk]
  simp

private theorem odlyzkoHRight_jet_zero (k : ℕ) :
    iteratedDeriv k odlyzkoHRight 0 =
      iteratedDeriv k odlyzkoHCore 0 := by
  apply Filter.EventuallyEq.iteratedDeriv_eq k
  filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 2)] with x hx
  change x < 2 at hx
  simp [odlyzkoHRight, hx.le]

private theorem odlyzkoHMiddle_contDiff_four : ContDiff ℝ 4 odlyzkoHMiddle := by
  unfold odlyzkoHMiddle
  apply fourth_contDiff_if_le (fun x ↦ odlyzkoHCore (-x))
    odlyzkoHRight 0
    (odlyzkoHCore_contDiff.comp contDiff_neg)
    odlyzkoHRight_contDiff_four
  intro k hk
  rw [iteratedDeriv_comp_neg, neg_zero, smul_eq_mul,
    odlyzkoHRight_jet_zero k]
  exact hCore_iteratedDeriv_even_at_zero k hk

private theorem odlyzkoHMiddle_jet_neg_two (k : ℕ) (hk : k ≤ 4) :
    iteratedDeriv k odlyzkoHMiddle (-2) = 0 := by
  have hlocal : odlyzkoHMiddle =ᶠ[𝓝 (-2 : ℝ)]
      (fun x ↦ odlyzkoHCore (-x)) := by
    filter_upwards [Iio_mem_nhds (by norm_num : (-2 : ℝ) < 0)] with x hx
    change x < 0 at hx
    simp [odlyzkoHMiddle, hx.le]
  rw [Filter.EventuallyEq.iteratedDeriv_eq k hlocal,
    iteratedDeriv_comp_neg]
  norm_num only [neg_neg]
  rw [hCore_iteratedDeriv_at_two k hk]
  simp

private theorem odlyzkoHPiecewise_contDiff_four :
    ContDiff ℝ 4 odlyzkoHPiecewise := by
  unfold odlyzkoHPiecewise
  apply fourth_contDiff_if_le (fun _ ↦ 0) odlyzkoHMiddle (-2)
    contDiff_const odlyzkoHMiddle_contDiff_four
  intro k hk
  rw [odlyzkoHMiddle_jet_neg_two k hk]
  simp

/-- The exact compactly supported auxiliary kernel in Odlyzko's table is
globally four times continuously differentiable, including all seams. -/
theorem odlyzkoH_contDiff_four : ContDiff ℝ 4 odlyzkoH := by
  have hEq : odlyzkoH = odlyzkoHPiecewise :=
    funext odlyzkoH_eq_piecewise
  rw [hEq]
  exact odlyzkoHPiecewise_contDiff_four

/-- The exact `b = 4` test function is globally `C⁴`; its hyperbolic cosine
denominator is strictly positive on the real line. -/
theorem odlyzkoF4_contDiff_four : ContDiff ℝ 4 odlyzkoF4 := by
  unfold odlyzkoF4
  exact (odlyzkoH_contDiff_four.comp (contDiff_id.div_const 4)).div
    (Real.contDiff_cosh.comp (contDiff_id.div_const 2))
    (fun x ↦ (Real.cosh_pos (x / 2)).ne')

end
end TraceEuclidean
