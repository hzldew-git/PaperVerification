import TraceEuclidean.Finiteness
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

namespace TraceEuclidean

open Filter Asymptotics
open scoped Topology

noncomputable section

theorem tendsto_log_affine_div_atTop (c : ℝ) (b : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℝ ↦ Real.log (c * (x + b)) / x)
      atTop (𝓝 0) := by
  have haffine : Tendsto (fun x : ℝ ↦ c * (x + b)) atTop atTop :=
    (Filter.tendsto_atTop_add_const_right atTop b tendsto_id).const_mul_atTop hc
  have hsmall :
      (fun x : ℝ ↦ Real.log (c * (x + b))) =o[atTop]
        (fun x : ℝ ↦ c * (x + b)) := by
    change (Real.log ∘ fun x : ℝ ↦ c * (x + b)) =o[atTop]
      (id ∘ fun x : ℝ ↦ c * (x + b))
    exact Real.isLittleO_log_id_atTop.comp_tendsto haffine
  have hzero : Tendsto
      (fun x : ℝ ↦ Real.log (c * (x + b)) / (c * (x + b)))
      atTop (𝓝 0) := hsmall.tendsto_div_nhds_zero
  have hbdiv : Tendsto (fun x : ℝ ↦ b / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hratio0 : Tendsto (fun x : ℝ ↦ c * (1 + b / x))
      atTop (𝓝 c) := by
    convert (tendsto_const_nhds.add hbdiv).const_mul c using 1
    ring_nf
  have hratio : Tendsto (fun x : ℝ ↦ (c * (x + b)) / x)
      atTop (𝓝 c) := by
    apply hratio0.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
    field_simp
  have hprod := hzero.mul hratio
  have hcongr :
      (fun x : ℝ ↦ Real.log (c * (x + b)) / (c * (x + b)) *
        (c * (x + b) / x)) =ᶠ[atTop]
      (fun x : ℝ ↦ Real.log (c * (x + b)) / x) := by
    filter_upwards [eventually_ne_atTop (0 : ℝ),
      eventually_ne_atTop (-b)] with x hx hxb
    have hxb' : x + b ≠ 0 := by
      intro hzero
      apply hxb
      linarith
    field_simp [hc.ne', hx, hxb']
  simpa using hprod.congr' hcongr

/-- The manuscript's constant `b = e^2/(2π) - 1`. -/
def traceAnalyticB : ℝ :=
  Real.exp 1 ^ 2 / (2 * Real.pi) - 1

/-- The exact function `g_s(x,y)` from Section 4. -/
def gClassicReal (x y : ℝ) : ℝ :=
  Real.log (2 * Real.pi * (y + traceAnalyticB)) -
    Real.log (Real.pi * (x * y + 1 / 3)) / x +
      y * Real.log (2 * Real.pi / (Real.exp 1 * x))

/-- The exact function `g_n(x,y)` from Section 4. -/
def gIntegralReal (x y : ℝ) : ℝ :=
  y * Real.log 2 + gClassicReal x y

def gClassicNat (n d : ℕ) : ℝ :=
  gClassicReal n d

def gIntegralNat (n d : ℕ) : ℝ :=
  gIntegralReal n d

theorem tendsto_gClassicReal_div_degree (x : ℝ) (hx : 0 < x) :
    Tendsto (fun y : ℝ ↦ gClassicReal x y / y) atTop
      (𝓝 (Real.log (2 * Real.pi / (Real.exp 1 * x)))) := by
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hfirst := tendsto_log_affine_div_atTop
    (2 * Real.pi) traceAnalyticB hpi
  have hpix : 0 < Real.pi * x := mul_pos Real.pi_pos hx
  have hsecond0 := tendsto_log_affine_div_atTop
    (Real.pi * x) ((1 / 3) / x) hpix
  have hsecond : Tendsto
      (fun y : ℝ ↦ Real.log (Real.pi * (x * y + 1 / 3)) / y)
      atTop (𝓝 0) := by
    apply hsecond0.congr'
    filter_upwards with y
    congr 2
    field_simp [hx.ne']
  have hsecondx := hsecond.div_const x
  let k : ℝ := Real.log (2 * Real.pi / (Real.exp 1 * x))
  have hk : Tendsto (fun _ : ℝ ↦ k) atTop (𝓝 k) := tendsto_const_nhds
  have hbase : Tendsto
      (fun y : ℝ ↦
        Real.log (2 * Real.pi * (y + traceAnalyticB)) / y -
          (Real.log (Real.pi * (x * y + 1 / 3)) / y) / x + k)
      atTop (𝓝 k) := by
    convert (hfirst.sub hsecondx).add hk using 1
    simp
  apply hbase.congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with y hy
  dsimp only [gClassicReal, k]
  field_simp [hx.ne', hy]

theorem tendsto_atBot_of_div_tendsto_neg {f : ℝ → ℝ} {c : ℝ}
    (hc : c < 0)
    (hdiv : Tendsto (fun x : ℝ ↦ f x / x) atTop (𝓝 c)) :
    Tendsto f atTop atBot := by
  rw [Filter.tendsto_atBot]
  intro b
  have hhalf : c < c / 2 := by linarith
  have hratio : ∀ᶠ x : ℝ in atTop, f x / x < c / 2 :=
    hdiv (Iio_mem_nhds hhalf)
  have hlinear : Tendsto (fun x : ℝ ↦ x * (c / 2)) atTop atBot :=
    tendsto_id.atTop_mul_const_of_neg (by linarith)
  have hbelow : ∀ᶠ x : ℝ in atTop, x * (c / 2) ≤ b :=
    (Filter.tendsto_atBot.mp hlinear) b
  filter_upwards [hratio, hbelow, eventually_gt_atTop (0 : ℝ)] with x hr hb hx
  have hfx : f x < x * (c / 2) := by
    simpa [mul_comm] using (div_lt_iff₀ hx).mp hr
  exact (le_of_lt hfx).trans hb

theorem classic_degree_coefficient_neg {x : ℝ} (hx : 3 ≤ x) :
    Real.log (2 * Real.pi / (Real.exp 1 * x)) < 0 := by
  apply Real.log_neg
  · positivity
  · apply (div_lt_one (mul_pos (Real.exp_pos 1) (by linarith))).2
    have hscale : Real.exp 1 * 3 ≤ Real.exp 1 * x :=
      mul_le_mul_of_nonneg_left hx (Real.exp_pos 1).le
    nlinarith [Real.pi_lt_d2, Real.exp_one_gt_d9]

theorem gClassicNat_degree_tail (n : ℕ) (hn : 3 ≤ n) :
    Tendsto (gClassicNat n) atTop atBot := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hreal : Tendsto (fun y : ℝ ↦ gClassicReal n y) atTop atBot :=
    tendsto_atBot_of_div_tendsto_neg
      (classic_degree_coefficient_neg (by exact_mod_cast hn))
      (tendsto_gClassicReal_div_degree n hnpos)
  change Tendsto (fun d : ℕ ↦ gClassicReal (n : ℝ) (d : ℝ)) atTop atBot
  have hcomp := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  change Tendsto (fun d : ℕ ↦ gClassicReal (n : ℝ) (d : ℝ))
    atTop atBot at hcomp
  exact hcomp

theorem tendsto_gIntegralReal_div_degree (x : ℝ) (hx : 0 < x) :
    Tendsto (fun y : ℝ ↦ gIntegralReal x y / y) atTop
      (𝓝 (Real.log 2 +
        Real.log (2 * Real.pi / (Real.exp 1 * x)))) := by
  have hclassic := tendsto_gClassicReal_div_degree x hx
  have hlogTwo : Tendsto (fun _ : ℝ ↦ Real.log 2) atTop
      (𝓝 (Real.log 2)) := tendsto_const_nhds
  have hbase := hlogTwo.add hclassic
  apply hbase.congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with y hy
  dsimp only [gIntegralReal]
  field_simp [hy]

theorem integral_degree_coefficient_neg {x : ℝ} (hx : 5 ≤ x) :
    Real.log 2 + Real.log (2 * Real.pi / (Real.exp 1 * x)) < 0 := by
  have hden : 0 < Real.exp 1 * x :=
    mul_pos (Real.exp_pos 1) (by linarith)
  have hfrac : 0 < 2 * Real.pi / (Real.exp 1 * x) := by positivity
  rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hfrac.ne']
  apply Real.log_neg
  · positivity
  · have hbound : 4 * Real.pi < Real.exp 1 * x := by
      have hscale : Real.exp 1 * 5 ≤ Real.exp 1 * x :=
        mul_le_mul_of_nonneg_left hx (Real.exp_pos 1).le
      nlinarith [Real.pi_lt_d2, Real.exp_one_gt_d9]
    calc
      2 * (2 * Real.pi / (Real.exp 1 * x)) =
          (4 * Real.pi) / (Real.exp 1 * x) := by ring
      _ < 1 := (div_lt_one hden).2 hbound

theorem gIntegralNat_degree_tail (n : ℕ) (hn : 5 ≤ n) :
    Tendsto (gIntegralNat n) atTop atBot := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hreal : Tendsto (fun y : ℝ ↦ gIntegralReal n y) atTop atBot :=
    tendsto_atBot_of_div_tendsto_neg
      (integral_degree_coefficient_neg (by exact_mod_cast hn))
      (tendsto_gIntegralReal_div_degree n hnpos)
  change Tendsto (fun d : ℕ ↦ gIntegralReal (n : ℝ) (d : ℝ)) atTop atBot
  have hcomp := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  change Tendsto (fun d : ℕ ↦ gIntegralReal (n : ℝ) (d : ℝ))
    atTop atBot at hcomp
  exact hcomp

theorem tendsto_gClassicReal_rank_atBot (d : ℝ) (hd : 0 < d) :
    Tendsto (fun x : ℝ ↦ gClassicReal x d) atTop atBot := by
  have hpid : 0 < Real.pi * d := mul_pos Real.pi_pos hd
  have hlog0 := tendsto_log_affine_div_atTop
    (Real.pi * d) ((1 / 3) / d) hpid
  have hlog : Tendsto
      (fun x : ℝ ↦ Real.log (Real.pi * (x * d + 1 / 3)) / x)
      atTop (𝓝 0) := by
    apply hlog0.congr'
    filter_upwards with x
    congr 2
    field_simp [hd.ne']
  have hneglog : Tendsto
      (fun x : ℝ ↦ (-d) * Real.log x) atTop atBot :=
    Real.tendsto_log_atTop.const_mul_atTop_of_neg (by linarith)
  let c : ℝ := d * Real.log (2 * Real.pi / Real.exp 1)
  have hc : Tendsto (fun _ : ℝ ↦ c) atTop (𝓝 c) := tendsto_const_nhds
  have hthird0 : Tendsto
      (fun x : ℝ ↦ c + (-d) * Real.log x) atTop atBot :=
    hc.add_atBot hneglog
  have hthird : Tendsto
      (fun x : ℝ ↦ d * Real.log (2 * Real.pi / (Real.exp 1 * x)))
      atTop atBot := by
    apply hthird0.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
    dsimp only [c]
    rw [Real.log_div (mul_ne_zero (by positivity) Real.pi_ne_zero)
        (mul_ne_zero (Real.exp_ne_zero 1) hx),
      Real.log_mul (by positivity) Real.pi_ne_zero,
      Real.log_mul (Real.exp_ne_zero 1) hx,
      Real.log_div (mul_ne_zero (by positivity) Real.pi_ne_zero)
        (Real.exp_ne_zero 1)]
    simp only [Real.log_exp, neg_mul]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
    ring
  let a : ℝ := Real.log (2 * Real.pi * (d + traceAnalyticB))
  have ha : Tendsto (fun _ : ℝ ↦ a) atTop (𝓝 a) := tendsto_const_nhds
  have hfinite : Tendsto
      (fun x : ℝ ↦ a -
        Real.log (Real.pi * (x * d + 1 / 3)) / x)
      atTop (𝓝 a) := by
    convert ha.sub hlog using 1
    simp
  have hsum := hfinite.add_atBot hthird
  apply hsum.congr'
  filter_upwards with x
  simp only [gClassicReal, a]

theorem gClassicNat_rank_tail (d : ℕ) (hd : 1 ≤ d) :
    Tendsto (fun n ↦ gClassicNat n d) atTop atBot := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hreal := tendsto_gClassicReal_rank_atBot (d : ℝ) hdpos
  change Tendsto (fun n : ℕ ↦ gClassicReal (n : ℝ) (d : ℝ)) atTop atBot
  have hcomp := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  change Tendsto (fun n : ℕ ↦ gClassicReal (n : ℝ) (d : ℝ))
    atTop atBot at hcomp
  exact hcomp

theorem gIntegralNat_rank_tail (d : ℕ) (hd : 1 ≤ d) :
    Tendsto (fun n ↦ gIntegralNat n d) atTop atBot := by
  have hclassic := gClassicNat_rank_tail d hd
  have hconst : Tendsto (fun _ : ℕ ↦ (d : ℝ) * Real.log 2)
      atTop (𝓝 ((d : ℝ) * Real.log 2)) := tendsto_const_nhds
  have hsum := hconst.add_atBot hclassic
  apply hsum.congr'
  filter_upwards with n
  simp [gIntegralNat, gIntegralReal, gClassicNat]

def gClassicEnvelopeReal (base y : ℝ) : ℝ :=
  Real.log (2 * Real.pi * (y + traceAnalyticB)) +
    y * Real.log (2 * Real.pi / (Real.exp 1 * base))

def gIntegralEnvelopeReal (base y : ℝ) : ℝ :=
  Real.log (2 * Real.pi * (y + traceAnalyticB)) +
    y * (Real.log 2 +
      Real.log (2 * Real.pi / (Real.exp 1 * base)))

def gClassicEnvelopeNat (d : ℕ) : ℝ :=
  gClassicEnvelopeReal 3 d

def gIntegralEnvelopeNat (d : ℕ) : ℝ :=
  gIntegralEnvelopeReal 5 d

theorem gClassicReal_le_envelope {base x y : ℝ}
    (hbase : 1 ≤ base) (hbx : base ≤ x) (hy : 1 ≤ y) :
    gClassicReal x y ≤ gClassicEnvelopeReal base y := by
  have hx : 0 < x := lt_of_lt_of_le (by norm_num) (hbase.trans hbx)
  have hy0 : 0 ≤ y := by linarith
  have harg : 1 ≤ Real.pi * (x * y + 1 / 3) := by
    have hxy : 1 ≤ x * y := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (hbase.trans hbx))
        (sub_nonneg.mpr hy)]
    nlinarith [Real.pi_gt_three]
  have hlogNonneg : 0 ≤ Real.log (Real.pi * (x * y + 1 / 3)) :=
    Real.log_nonneg harg
  have hden : Real.exp 1 * base ≤ Real.exp 1 * x :=
    mul_le_mul_of_nonneg_left hbx (Real.exp_pos 1).le
  have hbasepos : 0 < base := by linarith
  have hfrac :
      2 * Real.pi / (Real.exp 1 * x) ≤
        2 * Real.pi / (Real.exp 1 * base) := by
    exact div_le_div_of_nonneg_left (by positivity)
      (mul_pos (Real.exp_pos 1) hbasepos) hden
  have hlog :
      Real.log (2 * Real.pi / (Real.exp 1 * x)) ≤
        Real.log (2 * Real.pi / (Real.exp 1 * base)) :=
    Real.log_le_log (by positivity) hfrac
  have hmul := mul_le_mul_of_nonneg_left hlog hy0
  simp only [gClassicReal, gClassicEnvelopeReal]
  have hdiv : 0 ≤ Real.log (Real.pi * (x * y + 1 / 3)) / x :=
    div_nonneg hlogNonneg hx.le
  linarith

theorem gIntegralReal_le_envelope {x y : ℝ}
    (hx : 5 ≤ x) (hy : 1 ≤ y) :
    gIntegralReal x y ≤ gIntegralEnvelopeReal 5 y := by
  have hclassic := gClassicReal_le_envelope
    (base := (5 : ℝ)) (x := x) (y := y) (by norm_num) hx hy
  calc
    gIntegralReal x y = y * Real.log 2 + gClassicReal x y := rfl
    _ ≤ y * Real.log 2 + gClassicEnvelopeReal 5 y :=
      add_le_add (le_refl _) hclassic
    _ = gIntegralEnvelopeReal 5 y := by
      simp only [gClassicEnvelopeReal, gIntegralEnvelopeReal]
      ring

theorem tendsto_gClassicEnvelopeReal_div (base : ℝ) (_hbase : 0 < base) :
    Tendsto (fun y : ℝ ↦ gClassicEnvelopeReal base y / y) atTop
      (𝓝 (Real.log (2 * Real.pi / (Real.exp 1 * base)))) := by
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hfirst := tendsto_log_affine_div_atTop
    (2 * Real.pi) traceAnalyticB hpi
  let k : ℝ := Real.log (2 * Real.pi / (Real.exp 1 * base))
  have hk : Tendsto (fun _ : ℝ ↦ k) atTop (𝓝 k) := tendsto_const_nhds
  have hbaseLimit : Tendsto
      (fun y : ℝ ↦
        Real.log (2 * Real.pi * (y + traceAnalyticB)) / y + k)
      atTop (𝓝 k) := by
    simpa using hfirst.add hk
  change Tendsto (fun y : ℝ ↦ gClassicEnvelopeReal base y / y)
    atTop (𝓝 k)
  apply hbaseLimit.congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with y hy
  dsimp only [gClassicEnvelopeReal, k]
  field_simp [hy]

theorem tendsto_gIntegralEnvelopeReal_div (base : ℝ) (_hbase : 0 < base) :
    Tendsto (fun y : ℝ ↦ gIntegralEnvelopeReal base y / y) atTop
      (𝓝 (Real.log 2 +
        Real.log (2 * Real.pi / (Real.exp 1 * base)))) := by
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hfirst := tendsto_log_affine_div_atTop
    (2 * Real.pi) traceAnalyticB hpi
  let k : ℝ := Real.log 2 +
    Real.log (2 * Real.pi / (Real.exp 1 * base))
  have hk : Tendsto (fun _ : ℝ ↦ k) atTop (𝓝 k) := tendsto_const_nhds
  have hbaseLimit : Tendsto
      (fun y : ℝ ↦
        Real.log (2 * Real.pi * (y + traceAnalyticB)) / y + k)
      atTop (𝓝 k) := by
    simpa using hfirst.add hk
  change Tendsto (fun y : ℝ ↦ gIntegralEnvelopeReal base y / y)
    atTop (𝓝 k)
  apply hbaseLimit.congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with y hy
  dsimp only [gIntegralEnvelopeReal, k]
  field_simp [hy]

theorem gClassicEnvelopeNat_tail :
    Tendsto gClassicEnvelopeNat atTop atBot := by
  have hreal : Tendsto (gClassicEnvelopeReal 3) atTop atBot :=
    tendsto_atBot_of_div_tendsto_neg
      (classic_degree_coefficient_neg (x := 3) (by norm_num))
      (tendsto_gClassicEnvelopeReal_div 3 (by norm_num))
  change Tendsto (fun d : ℕ ↦ gClassicEnvelopeReal 3 (d : ℝ)) atTop atBot
  have hcomp := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  change Tendsto (fun d : ℕ ↦ gClassicEnvelopeReal 3 (d : ℝ))
    atTop atBot at hcomp
  exact hcomp

theorem gIntegralEnvelopeNat_tail :
    Tendsto gIntegralEnvelopeNat atTop atBot := by
  have hreal : Tendsto (gIntegralEnvelopeReal 5) atTop atBot :=
    tendsto_atBot_of_div_tendsto_neg
      (integral_degree_coefficient_neg (x := 5) (by norm_num))
      (tendsto_gIntegralEnvelopeReal_div 5 (by norm_num))
  change Tendsto (fun d : ℕ ↦ gIntegralEnvelopeReal 5 (d : ℝ)) atTop atBot
  have hcomp := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  change Tendsto (fun d : ℕ ↦ gIntegralEnvelopeReal 5 (d : ℝ))
    atTop atBot at hcomp
  exact hcomp

theorem gClassicNat_le_envelope {n d : ℕ}
    (hn : 3 ≤ n) (hd : 1 ≤ d) :
    gClassicNat n d ≤ gClassicEnvelopeNat d := by
  exact gClassicReal_le_envelope (by norm_num) (by exact_mod_cast hn)
    (by exact_mod_cast hd)

theorem gIntegralNat_le_envelope {n d : ℕ}
    (hn : 5 ≤ n) (hd : 1 ≤ d) :
    gIntegralNat n d ≤ gIntegralEnvelopeNat d := by
  exact gIntegralReal_le_envelope (by exact_mod_cast hn)
    (by exact_mod_cast hd)

end

end TraceEuclidean
