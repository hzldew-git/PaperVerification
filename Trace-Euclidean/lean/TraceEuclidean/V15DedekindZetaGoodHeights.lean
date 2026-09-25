import TraceEuclidean.V15DedekindZetaLandau

/-!
# Good horizontal heights for the completed Dedekind zeta

The disk Landau estimate gives a quadratic bound for the number of nearby
zeros.  Choosing a height in the long interval `[T,2T]` leaves distance of
order `T/(N+1)` from every zero ordinate.  This is strong enough to turn the
quadratic zero count into a cubic logarithmic-derivative bound, which the
fourth-power decay of the Odlyzko transform can absorb.
-/

namespace TraceEuclidean

noncomputable section

open Complex Set Finset Filter

/-- In an interval of positive length, one of `|S|+1` equally spaced
midpoints stays a controlled distance from every point of the finite set. -/
lemma exists_far_point_in_interval
    (S : Finset ℝ) (a L : ℝ) (hL : 0 < L) :
    ∃ R : ℝ, a ≤ R ∧ R ≤ a + L ∧
      ∀ y ∈ S, L / (2 * ((S.card : ℝ) + 1)) ≤ |R - y| := by
  classical
  set n : ℕ := S.card with hn
  set δ : ℝ := L / (2 * ((n : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    positivity
  have hδn : 2 * ((n : ℝ) + 1) * δ = L := by
    rw [hδ]
    field_simp
  set cand : ℕ → ℝ := fun k ↦ a + (2 * (k : ℝ) + 1) * δ with hcand
  by_contra hcon
  push Not at hcon
  have hbad : ∀ k ∈ Finset.range (n + 1), ∃ y ∈ S, |cand k - y| < δ := by
    intro k hk
    have hk' : (k : ℝ) ≤ n := by
      exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h1 : a ≤ cand k := by
      simp only [hcand]
      nlinarith
    have h2 : cand k ≤ a + L := by
      simp only [hcand]
      have hmul :
          (2 * (k : ℝ) + 1) * δ ≤ (2 * (n : ℝ) + 1) * δ := by
        gcongr
      nlinarith
    obtain ⟨y, hy, hlt⟩ := hcon (cand k) h1 h2
    exact ⟨y, hy, hlt⟩
  choose! f hf using hbad
  have hmaps : Set.MapsTo f (Finset.range (n + 1)) S :=
    fun k hk ↦ (hf k hk).1
  obtain ⟨x, hx, y, hy, hxy, hfxy⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by simp [hn]) hmaps
  have h1 := (hf x hx).2
  have h2 := (hf y hy).2
  rw [hfxy] at h1
  have hdist : |cand x - cand y| = 2 * |(x : ℝ) - y| * δ := by
    simp only [hcand]
    rw [show a + (2 * (x : ℝ) + 1) * δ -
        (a + (2 * (y : ℝ) + 1) * δ) =
          (2 * δ) * ((x : ℝ) - y) by ring,
      abs_mul, abs_of_pos (by positivity)]
    ring
  have hxy1 : (1 : ℝ) ≤ |(x : ℝ) - y| := by
    rcases Nat.lt_or_gt_of_ne hxy with h | h
    · have : (x : ℝ) + 1 ≤ y := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have : (y : ℝ) + 1 ≤ x := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
  have htri : |cand x - cand y| < 2 * δ := by
    calc
      |cand x - cand y| = |(cand x - f y) - (cand y - f y)| := by ring_nf
      _ ≤ |cand x - f y| + |cand y - f y| := abs_sub _ _
      _ < δ + δ := add_lt_add h1 h2
      _ = 2 * δ := by ring
  rw [hdist] at htri
  nlinarith

/-- A zero of the constructed entire completion has positive natural analytic
order. -/
lemma v15_completedZetaPoleRemoved_one_le_order
    {K : Type*} [Field K] [NumberField K] {ρ : ℂ}
    (hρ : DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K ρ = 0) :
    1 ≤ analyticOrderNatAt
      (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ρ := by
  apply Nat.one_le_iff_ne_zero.mpr
  intro hnat
  have htop := v15_completedZetaPoleRemoved_order_ne_top (K := K) ρ
  have horderZero :
      analyticOrderAt
          (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ρ = 0 := by
    rw [← Nat.cast_analyticOrderNatAt htop, hnat]
    simp
  have hAnalytic : AnalyticAt ℂ
      (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ρ :=
    DedekindZeta.GlobalContinuation.completedZetaPoleRemoved_analyticOn K
      ρ (mem_univ ρ)
  exact (hAnalytic.analyticOrderAt_ne_zero.mpr hρ) horderZero

/-- The number of distinct zeros in a finite zero set is at most their total
analytic multiplicity. -/
lemma v15_completedZetaPoleRemoved_card_le_sum_order
    {K : Type*} [Field K] [NumberField K]
    (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z,
      DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K ρ = 0) :
    (Z.card : ℝ) ≤
      ∑ ρ ∈ Z,
        (analyticOrderNatAt
          (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ρ : ℝ) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro ρ hρ
  exact_mod_cast v15_completedZetaPoleRemoved_one_le_order (K := K) (hZ ρ hρ)

/-- Every point of the horizontal segment `-1 ≤ Re(s) ≤ 2` at a height in
`[T,2T]` lies in the inner Landau disk. -/
lemma v15_horizontal_mem_landau_inner_ball
    {c s : ℂ} {T R : ℝ} (hT : 1 ≤ T)
    (hTR : T ≤ R) (hR2 : R ≤ 2 * T)
    (hsim : s.im = R ∨ s.im = -R)
    (hsre₁ : -1 ≤ s.re) (hsre₂ : s.re ≤ 2) :
    s ∈ Metric.closedBall c
      (83 / 100 * v15DedekindZetaLandauRadius c T) := by
  have hR : 0 ≤ R := le_trans (by linarith) hTR
  have hsreAbs : |s.re| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hsimAbs : |s.im| = R := by
    rcases hsim with h | h
    · rw [h, abs_of_nonneg hR]
    · rw [h, abs_neg, abs_of_nonneg hR]
  have hcre : |c.re| ≤ ‖c‖ := Complex.abs_re_le_norm c
  have hcim : |c.im| ≤ ‖c‖ := Complex.abs_im_le_norm c
  rw [Metric.mem_closedBall, dist_eq_norm]
  calc
    ‖s - c‖ ≤ |(s - c).re| + |(s - c).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = |s.re - c.re| + |s.im - c.im| := by simp
    _ ≤ (|s.re| + |c.re|) + (|s.im| + |c.im|) :=
      add_le_add (abs_sub _ _) (abs_sub _ _)
    _ ≤ 2 + ‖c‖ + (R + ‖c‖) := by
      rw [hsimAbs]
      linarith
    _ ≤ 83 / 100 * v15DedekindZetaLandauRadius c T := by
      dsimp [v15DedekindZetaLandauRadius]
      rw [abs_of_nonneg (by linarith)]
      nlinarith [norm_nonneg c]

/-- Good heights for the pole-removed completed Dedekind zeta.  At a selected
height in `[T,2T]`, the logarithmic derivative on the whole horizontal strip
segment has a uniform cubic bound. -/
theorem exists_v15_completedZetaPoleRemoved_good_height_bound
    (K : Type*) [Field K] [NumberField K] :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ T : ℝ, 1 ≤ T →
      ∃ R : ℝ, T ≤ R ∧ R ≤ 2 * T ∧
        ∀ s : ℂ, (s.im = R ∨ s.im = -R) →
          -1 ≤ s.re → s.re ≤ 2 →
          DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s ≠ 0 ∧
          ‖logDeriv
            (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s‖ ≤
              Cg * (1 + T) ^ 3 := by
  classical
  let F := DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K
  obtain ⟨c, C, hC, hLandau⟩ :=
    exists_v15_completedZetaPoleRemoved_polynomial_landau_data K
  let Cg : ℝ := C + 4 * C * (C + 1)
  have hCg : 0 ≤ Cg := by
    dsimp [Cg]
    positivity
  refine ⟨Cg, hCg, ?_⟩
  intro T hT
  obtain ⟨Z, hZ, hCount, hError⟩ := hLandau T
  let S : Finset ℝ := Z.image (fun ρ : ℂ ↦ |ρ.im|)
  obtain ⟨R, hTR, hRsum, hfar⟩ :=
    exists_far_point_in_interval S T T (by linarith)
  have hR2 : R ≤ 2 * T := by linarith
  have hRnonneg : 0 ≤ R := by linarith
  let δ : ℝ := T / (2 * ((S.card : ℝ) + 1))
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  have hZzero : ∀ ρ ∈ Z, F ρ = 0 := by
    intro ρ hρ
    have hρSet : ρ ∈ (Z : Set ℂ) := hρ
    rw [hZ] at hρSet
    exact hρSet.2
  have hCardZ : (Z.card : ℝ) ≤
      ∑ ρ ∈ Z, (analyticOrderNatAt F ρ : ℝ) := by
    exact v15_completedZetaPoleRemoved_card_le_sum_order Z hZzero
  have hCardS : (S.card : ℝ) ≤
      ∑ ρ ∈ Z, (analyticOrderNatAt F ρ : ℝ) := by
    have hnat : S.card ≤ Z.card := Finset.card_image_le
    have hnatReal : (S.card : ℝ) ≤ (Z.card : ℝ) := by
      exact_mod_cast hnat
    exact hnatReal.trans hCardZ
  have hTabs : |T| = T := abs_of_nonneg (by linarith)
  have hCountT :
      ∑ ρ ∈ Z, (analyticOrderNatAt F ρ : ℝ) ≤ C * (1 + T) ^ 2 := by
    simpa [hTabs] using hCount
  have hSbound : (S.card : ℝ) ≤ C * (1 + T) ^ 2 :=
    hCardS.trans hCountT
  refine ⟨R, hTR, hR2, ?_⟩
  intro s hsim hsre₁ hsre₂
  have hsInner : s ∈ Metric.closedBall c
      (83 / 100 * v15DedekindZetaLandauRadius c T) :=
    v15_horizontal_mem_landau_inner_ball hT hTR hR2 hsim hsre₁ hsre₂
  have hsAbs : |s.im| = R := by
    rcases hsim with h | h
    · rw [h, abs_of_nonneg hRnonneg]
    · rw [h, abs_neg, abs_of_nonneg hRnonneg]
  have hFne : F s ≠ 0 := by
    intro hzero
    have hsOuter : s ∈ Metric.closedBall c
        (22 / 25 * v15DedekindZetaLandauRadius c T) := by
      apply Metric.closedBall_subset_closedBall _ hsInner
      have hRad : 0 ≤ v15DedekindZetaLandauRadius c T := by
        dsimp [v15DedekindZetaLandauRadius]
        positivity
      nlinarith
    have hsZ : s ∈ Z := by
      have hsSet : s ∈ (Z : Set ℂ) := by
        rw [hZ]
        exact ⟨hsOuter, hzero⟩
      exact hsSet
    have hsS : |s.im| ∈ S := by
      exact Finset.mem_image.mpr ⟨s, hsZ, rfl⟩
    have hgap := hfar _ hsS
    change δ ≤ abs (R - |s.im|) at hgap
    rw [hsAbs, sub_self, abs_zero] at hgap
    linarith
  refine ⟨hFne, ?_⟩
  have hRegular := hError s hsInner hFne
  have hTerm : ∀ ρ ∈ Z,
      ‖(analyticOrderNatAt F ρ : ℂ) / (s - ρ)‖ ≤
        (analyticOrderNatAt F ρ : ℝ) * (1 / δ) := by
    intro ρ hρ
    have hρS : |ρ.im| ∈ S :=
      Finset.mem_image.mpr ⟨ρ, hρ, rfl⟩
    have hgap := hfar _ hρS
    change δ ≤ abs (R - |ρ.im|) at hgap
    have hreverse : abs (R - |ρ.im|) ≤ |s.im - ρ.im| := by
      calc
        abs (R - |ρ.im|) = abs (|s.im| - |ρ.im|) := by rw [hsAbs]
        _ ≤ |s.im - ρ.im| := abs_abs_sub_abs_le_abs_sub _ _
    have himNorm : |s.im - ρ.im| ≤ ‖s - ρ‖ := by
      rw [← Complex.sub_im]
      exact Complex.abs_im_le_norm _
    have hdist : δ ≤ ‖s - ρ‖ := hgap.trans (hreverse.trans himNorm)
    rw [norm_div, Complex.norm_natCast, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left
      (one_div_le_one_div_of_le hδpos hdist)
      (Nat.cast_nonneg _)
  have hZeroSum :
      ‖∑ ρ ∈ Z, (analyticOrderNatAt F ρ : ℂ) / (s - ρ)‖ ≤
        (∑ ρ ∈ Z, (analyticOrderNatAt F ρ : ℝ)) * (1 / δ) := by
    calc
      _ ≤ ∑ ρ ∈ Z, ‖(analyticOrderNatAt F ρ : ℂ) / (s - ρ)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z,
          (analyticOrderNatAt F ρ : ℝ) * (1 / δ) := by
        exact Finset.sum_le_sum fun ρ hρ ↦ hTerm ρ hρ
      _ = (∑ ρ ∈ Z, (analyticOrderNatAt F ρ : ℝ)) * (1 / δ) := by
        rw [Finset.sum_mul]
  have hδinv : 1 / δ = 2 * ((S.card : ℝ) + 1) / T := by
    dsimp [δ]
    rw [one_div_div]
  let U : ℝ := 1 + T
  have hU : 2 ≤ U := by dsimp [U]; linarith
  have hUSq : 1 ≤ U ^ 2 := by nlinarith
  have hSplus : (S.card : ℝ) + 1 ≤ (C + 1) * U ^ 2 := by
    calc
      (S.card : ℝ) + 1 ≤ C * U ^ 2 + 1 := by
        dsimp [U] at hSbound ⊢
        linarith
      _ ≤ C * U ^ 2 + U ^ 2 := by linarith
      _ = (C + 1) * U ^ 2 := by ring
  have hInvBound : 1 / δ ≤ 2 * ((C + 1) * U ^ 2) / T := by
    rw [hδinv]
    apply (div_le_div_iff_of_pos_right (by linarith : 0 < T)).2
    nlinarith
  have hSumNonneg :
      0 ≤ ∑ ρ ∈ Z, (analyticOrderNatAt F ρ : ℝ) := by
    positivity
  have hInvNonneg : 0 ≤ 1 / δ := le_of_lt (one_div_pos.mpr hδpos)
  have hProduct :
      (∑ ρ ∈ Z, (analyticOrderNatAt F ρ : ℝ)) * (1 / δ) ≤
        2 * C * (C + 1) * U ^ 4 / T := by
    calc
      _ ≤ (C * U ^ 2) *
          (2 * ((C + 1) * U ^ 2) / T) :=
        mul_le_mul (by simpa [U] using hCountT) hInvBound
          hInvNonneg (mul_nonneg hC (sq_nonneg U))
      _ = 2 * C * (C + 1) * U ^ 4 / T := by ring
  have hUle : U ≤ 2 * T := by
    dsimp [U]
    linarith
  have hPowDiv : U ^ 4 / T ≤ 2 * U ^ 3 := by
    apply (div_le_iff₀ (by linarith : 0 < T)).2
    have hmul := mul_le_mul_of_nonneg_right hUle
      (pow_nonneg (by linarith : 0 ≤ U) 3)
    nlinarith
  have hZeroSumCubic :
      ‖∑ ρ ∈ Z, (analyticOrderNatAt F ρ : ℂ) / (s - ρ)‖ ≤
        4 * C * (C + 1) * U ^ 3 := by
    calc
      _ ≤ (∑ ρ ∈ Z, (analyticOrderNatAt F ρ : ℝ)) * (1 / δ) := hZeroSum
      _ ≤ 2 * C * (C + 1) * U ^ 4 / T := hProduct
      _ ≤ 4 * C * (C + 1) * U ^ 3 := by
        have hcoef : 0 ≤ 2 * C * (C + 1) := by positivity
        calc
          2 * C * (C + 1) * U ^ 4 / T =
              (2 * C * (C + 1)) * (U ^ 4 / T) := by ring
          _ ≤ (2 * C * (C + 1)) * (2 * U ^ 3) :=
            mul_le_mul_of_nonneg_left hPowDiv hcoef
          _ = 4 * C * (C + 1) * U ^ 3 := by ring
  have hTriangle :
      ‖logDeriv F s‖ ≤
        ‖logDeriv F s -
          ∑ ρ ∈ Z, (analyticOrderNatAt F ρ : ℂ) / (s - ρ)‖ +
        ‖∑ ρ ∈ Z, (analyticOrderNatAt F ρ : ℂ) / (s - ρ)‖ :=
    norm_le_norm_sub_add _ _
  have hUSqCube : U ^ 2 ≤ U ^ 3 := by nlinarith
  calc
    ‖logDeriv F s‖ ≤
        ‖logDeriv F s -
          ∑ ρ ∈ Z, (analyticOrderNatAt F ρ : ℂ) / (s - ρ)‖ +
        ‖∑ ρ ∈ Z, (analyticOrderNatAt F ρ : ℂ) / (s - ρ)‖ := hTriangle
    _ ≤ C * U ^ 2 + 4 * C * (C + 1) * U ^ 3 := by
      exact add_le_add (by simpa [U, F, hTabs] using hRegular) hZeroSumCubic
    _ ≤ (C + 4 * C * (C + 1)) * U ^ 3 := by
      nlinarith [mul_le_mul_of_nonneg_left hUSqCube hC]
    _ = Cg * (1 + T) ^ 3 := by rfl

/-- A sequence of good horizontal heights tending to infinity.  The cubic
bound is expressed in the sequence index so it can be combined directly with
the fourth-power decay of the Odlyzko transform. -/
theorem exists_v15_completedZetaPoleRemoved_good_height_sequence
    (K : Type*) [Field K] [NumberField K] :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∃ R : ℕ → ℝ,
      Tendsto R atTop atTop ∧
      ∀ n : ℕ,
        (n : ℝ) + 1 ≤ R n ∧ R n ≤ 2 * ((n : ℝ) + 1) ∧
        ∀ s : ℂ, (s.im = R n ∨ s.im = -R n) →
          -1 ≤ s.re → s.re ≤ 2 →
          DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s ≠ 0 ∧
          ‖logDeriv
            (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s‖ ≤
              Cg * ((n : ℝ) + 2) ^ 3 := by
  obtain ⟨Cg, hCg, hgood⟩ :=
    exists_v15_completedZetaPoleRemoved_good_height_bound K
  have hpick : ∀ n : ℕ, ∃ R : ℝ,
      (n : ℝ) + 1 ≤ R ∧ R ≤ 2 * ((n : ℝ) + 1) ∧
      ∀ s : ℂ, (s.im = R ∨ s.im = -R) →
        -1 ≤ s.re → s.re ≤ 2 →
        DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s ≠ 0 ∧
        ‖logDeriv
          (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s‖ ≤
            Cg * ((n : ℝ) + 2) ^ 3 := by
    intro n
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    obtain ⟨R, hR₁, hR₂, hR⟩ := hgood ((n : ℝ) + 1) (by linarith)
    refine ⟨R, hR₁, hR₂, ?_⟩
    intro s hsim hs₁ hs₂
    obtain ⟨hzero, hbound⟩ := hR s hsim hs₁ hs₂
    refine ⟨hzero, ?_⟩
    convert hbound using 1 <;> ring
  choose R hR₁ hR₂ hRbound using hpick
  have hbase : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hRTop : Tendsto R atTop atTop := tendsto_atTop_mono hR₁ hbase
  exact ⟨Cg, hCg, R, hRTop, fun n ↦ ⟨hR₁ n, hR₂ n, hRbound n⟩⟩

end

end TraceEuclidean
