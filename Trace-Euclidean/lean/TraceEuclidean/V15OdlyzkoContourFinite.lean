import TraceEuclidean.Analytic.RectangleLogDeriv
import TraceEuclidean.V15OdlyzkoEntire
import TraceEuclidean.V15DedekindZetaCompletedJensen
import DedekindZeta.LogDeriv
import Mathlib.Order.Interval.Set.Infinite

/-!
# The finite Odlyzko contour identity

This module applies the weighted argument principle to the entire
pole-removed completed Dedekind zeta function and Odlyzko's entire test
transform.  At every finite rectangle whose boundary contains no zero, the
normalized boundary integral is exactly the sum of the test transform over
the enclosed zeros, counted with analytic multiplicity.

The underlying rectangle residue theorem is adapted from
`anthropics/zeta-23-lean` commit
`fbdc36bbf17d20af3fd0447c6d1a8a02773c9844` and ultimately from
`AlexKontorovich/PrimeNumberTheoremAnd`; both sources are Apache 2.0.
-/

namespace TraceEuclidean

noncomputable section

open Complex Set

variable {K : Type*} [Field K] [NumberField K]

/-- The lower-left corner of the symmetric explicit-formula rectangle. -/
def v15OdlyzkoContourLower (c R : ℝ) : ℂ :=
  ((1 - c : ℝ) : ℂ) - R * I

/-- The upper-right corner of the symmetric explicit-formula rectangle. -/
def v15OdlyzkoContourUpper (c R : ℝ) : ℂ :=
  (c : ℂ) + R * I

/-- The pole-removed completed Dedekind zeta has no zero in its original
half-plane of absolute convergence. -/
theorem v15_completedZetaPoleRemoved_ne_zero_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have : s = 1 := sub_eq_zero.mp h
    subst s
    norm_num at hs
  have hZ : DedekindZeta.ZInfty K s ≠ 0 :=
    DedekindZeta.LogDeriv.ZInfty_ne_zero_of_re_pos K (by linarith)
  have hzeta : NumberField.dedekindZeta K s ≠ 0 :=
    DedekindZeta.dedekindZeta_ne_zero_of_one_lt_re K hs
  rw [DedekindZeta.GlobalContinuation.completedZetaPoleRemoved_eq_zeta K hs]
  exact mul_ne_zero (mul_ne_zero hs0 hs1) (mul_ne_zero hZ hzeta)

/-- The functional equation reflects right-half-plane nonvanishing to the
open left half-plane. -/
theorem v15_completedZetaPoleRemoved_ne_zero_of_re_lt_zero
    {s : ℂ} (hs : s.re < 0) :
    DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s ≠ 0 := by
  rw [DedekindZeta.FractionalIdealRescaling.completedZetaPoleRemoved_reflection K s]
  apply v15_completedZetaPoleRemoved_ne_zero_of_one_lt_re
  simp only [sub_re, one_re]
  linarith

/-- Every zero of the entire pole-removed completion lies in the closed
critical strip.  This formulation deliberately includes possible boundary
zeros and therefore does not require a separate prime-ideal theorem on
`Re(s) = 1`. -/
theorem v15_completedZetaPoleRemoved_zero_mem_closedStrip
    {s : ℂ}
    (hs : DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s = 0) :
    0 ≤ s.re ∧ s.re ≤ 1 := by
  constructor
  · by_contra h
    exact v15_completedZetaPoleRemoved_ne_zero_of_re_lt_zero
      (K := K) (lt_of_not_ge h) hs
  · by_contra h
    exact v15_completedZetaPoleRemoved_ne_zero_of_one_lt_re
      (K := K) (lt_of_not_ge h) hs

/-- Each completed-zeta zero contributes a term with nonnegative real part
to the Odlyzko zero sum, including zeros on either boundary of the strip. -/
theorem v15_completedZetaPoleRemoved_zero_weight_re_nonneg
    {s : ℂ}
    (hs : DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s = 0) :
    0 ≤ ((analyticOrderNatAt
      (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s : ℂ) *
        v15OdlyzkoPhi s).re := by
  have hstrip := v15_completedZetaPoleRemoved_zero_mem_closedStrip
    (K := K) hs
  rw [Complex.mul_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  exact mul_nonneg (Nat.cast_nonneg _)
    (v15OdlyzkoPhi_re_nonneg_of_mem_closed_strip s hstrip.1 hstrip.2)

/-- Any finite completed-zeta zero sum has nonnegative real part. -/
theorem v15_completedZetaPoleRemoved_zero_finset_re_nonneg
    (Z : Finset ℂ)
    (hZ : ∀ s ∈ Z,
      DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s = 0) :
    0 ≤ (∑ s ∈ Z,
      (analyticOrderNatAt
        (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s : ℂ) *
          v15OdlyzkoPhi s).re := by
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro s hs
  exact v15_completedZetaPoleRemoved_zero_weight_re_nonneg
    (K := K) (hZ s hs)

/-- In every unit interval above a nonnegative starting height there is a
height whose two horizontal lines contain no completed-zeta zero.  Only
finiteness of zeros in a compact rectangle is used. -/
theorem exists_v15_completedZetaPoleRemoved_zeroFree_horizontal_height
    (K : Type*) [Field K] [NumberField K] (T : ℝ) (hT : 0 ≤ T) :
    ∃ R : ℝ, T < R ∧ R < T + 1 ∧
      ∀ s : ℂ, (s.im = R ∨ s.im = -R) →
        DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s ≠ 0 := by
  let z : ℂ := Complex.mk (-1) (-(T + 1))
  let w : ℂ := Complex.mk 2 (T + 1)
  let F := DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K
  have hre : z.re ≤ w.re := by
    norm_num [z, w]
  have him : z.im ≤ w.im := by
    simp [z, w]
    linarith
  have hmem (s : ℂ) :
      s ∈ Rectangle z w ↔
        (-1 ≤ s.re ∧ s.re ≤ 2) ∧
          (-(T + 1) ≤ s.im ∧ s.im ≤ T + 1) := by
    rw [mem_Rect hre him]
    simp only [z, w]
    tauto
  have htwo : (2 : ℂ) ∈ Rectangle z w := by
    rw [hmem]
    constructor
    · norm_num
    · constructor <;> norm_num <;> linarith
  have htwoNonzero : F (2 : ℂ) ≠ 0 := by
    exact v15_completedZetaPoleRemoved_ne_zero_of_one_lt_re
      (K := K) (by norm_num)
  have hfinite : (Rectangle z w ∩ F ⁻¹' ({0} : Set ℂ)).Finite :=
    Analytic.finite_zeros_rectangle
      ((DedekindZeta.GlobalContinuation.completedZetaPoleRemoved_analyticOn K).mono
        (subset_univ _))
      htwo htwoNonzero
  let forbidden : Set ℝ :=
    (fun s : ℂ ↦ |s.im|) '' (Rectangle z w ∩ F ⁻¹' ({0} : Set ℂ))
  have hforbidden : forbidden.Finite := hfinite.image _
  have hinterval : (Set.Ioo T (T + 1)).Infinite :=
    Set.Ioo_infinite (by linarith)
  obtain ⟨R, hR, hRnot⟩ := hinterval.exists_notMem_finite hforbidden
  refine ⟨R, hR.1, hR.2, ?_⟩
  intro s hsHorizontal hsZero
  have hRpos : 0 < R := lt_of_le_of_lt hT hR.1
  have habs : |s.im| = R := by
    rcases hsHorizontal with hs | hs
    · rw [hs, abs_of_pos hRpos]
    · rw [hs, abs_neg, abs_of_pos hRpos]
  have himBound : |s.im| ≤ T + 1 := by
    rw [habs]
    exact hR.2.le
  have himBounds : -(T + 1) ≤ s.im ∧ s.im ≤ T + 1 :=
    abs_le.mp himBound
  have hstrip := v15_completedZetaPoleRemoved_zero_mem_closedStrip
    (K := K) hsZero
  have hsRectangle : s ∈ Rectangle z w := by
    rw [hmem]
    exact ⟨⟨by linarith [hstrip.1], by linarith [hstrip.2]⟩, himBounds⟩
  have hsForbidden : |s.im| ∈ forbidden :=
    ⟨s, ⟨hsRectangle, hsZero⟩, rfl⟩
  exact hRnot (habs ▸ hsForbidden)

/-- For every `c > 1` and every starting height, one can choose the next
height so that the whole symmetric contour is zero-free. -/
theorem exists_v15_completedZetaPoleRemoved_zeroFree_symmetric_boundary
    (K : Type*) [Field K] [NumberField K]
    {c T : ℝ} (hc : 1 < c) (hT : 0 ≤ T) :
    ∃ R : ℝ, T < R ∧ R < T + 1 ∧
      ∀ s ∈ RectangleBorder (v15OdlyzkoContourLower c R)
          (v15OdlyzkoContourUpper c R),
        DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s ≠ 0 := by
  obtain ⟨R, hTR, hRT, hhorizontal⟩ :=
    exists_v15_completedZetaPoleRemoved_zeroFree_horizontal_height K T hT
  refine ⟨R, hTR, hRT, ?_⟩
  intro s hs
  obtain ⟨⟨hbottom | hleft⟩ | htop⟩ | hright := hs
  · apply hhorizontal s
    right
    simpa [v15OdlyzkoContourLower] using hbottom.2
  · apply v15_completedZetaPoleRemoved_ne_zero_of_re_lt_zero
    have hsre : s.re = 1 - c := by
      simpa [v15OdlyzkoContourLower] using hleft.1
    rw [hsre]
    linarith
  · apply hhorizontal s
    left
    simpa [v15OdlyzkoContourUpper] using htop.2
  · apply v15_completedZetaPoleRemoved_ne_zero_of_one_lt_re
    have hsre : s.re = c := by
      simpa [v15OdlyzkoContourUpper] using hright.1
    rw [hsre]
    exact hc

/-- The completed function is analytic on a neighbourhood of every
rectangle. -/
private theorem completedZetaPoleRemoved_analyticOn_rectangle
    (K : Type*) [Field K] [NumberField K] (z w : ℂ) :
    AnalyticOnNhd ℂ
      (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K)
      (Rectangle z w) :=
  (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved_analyticOn K).mono
    (subset_univ _)

/-- Odlyzko's transform is analytic on a neighbourhood of every rectangle. -/
private theorem v15OdlyzkoPhi_analyticOn_rectangle (z w : ℂ) :
    AnalyticOnNhd ℂ v15OdlyzkoPhi (Rectangle z w) := by
  intro s _
  exact v15OdlyzkoPhi_differentiable.analyticAt s

/-- Weighted argument principle for the constructed completed Dedekind zeta
on an arbitrary finite rectangle.  The supplied finite set is required to be
exactly the zero set in the rectangle; the conclusion records every zero
with its analytic multiplicity. -/
theorem v15_completedZetaPoleRemoved_weighted_rectangle
    {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hborder : ∀ s ∈ RectangleBorder z w,
      DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s ≠ 0)
    (Z : Finset ℂ)
    (hZ : ∀ s ∈ Rectangle z w,
      DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s = 0 ↔
        s ∈ Z)
    (hZsub : (Z : Set ℂ) ⊆ Rectangle z w) :
    RectangleIntegral'
        (fun s ↦ v15OdlyzkoPhi s *
          logDeriv
            (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s)
        z w =
      ∑ ρ ∈ Z,
        (analyticOrderNatAt
          (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ρ : ℂ) *
            v15OdlyzkoPhi ρ := by
  exact Analytic.rectangleIntegral'_mul_logDeriv hre him
    (completedZetaPoleRemoved_analyticOn_rectangle K z w)
    (v15OdlyzkoPhi_analyticOn_rectangle z w) hborder Z hZ hZsub

/-- A boundary-zero-free finite rectangle has a concrete finite zero set and
satisfies the exact weighted argument-principle identity. -/
theorem exists_v15_completedZetaPoleRemoved_weighted_rectangle
    {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hborder : ∀ s ∈ RectangleBorder z w,
      DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s ≠ 0) :
    ∃ Z : Finset ℂ,
      (Z : Set ℂ) =
        Rectangle z w ∩
          (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ⁻¹'
            ({0} : Set ℂ) ∧
      RectangleIntegral'
          (fun s ↦ v15OdlyzkoPhi s *
            logDeriv
              (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s)
          z w =
        ∑ ρ ∈ Z,
          (analyticOrderNatAt
            (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ρ : ℂ) *
              v15OdlyzkoPhi ρ := by
  let F := DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K
  have hzBorder : z ∈ RectangleBorder z w :=
    Or.inl (Or.inl (Or.inl ⟨left_mem_uIcc, rfl⟩))
  have hzRectangle : z ∈ Rectangle z w :=
    rectangleBorder_subset_rectangle z w hzBorder
  have hzNonzero : F z ≠ 0 := hborder z hzBorder
  have hfinite : (Rectangle z w ∩ F ⁻¹' ({0} : Set ℂ)).Finite :=
    Analytic.finite_zeros_rectangle
      (completedZetaPoleRemoved_analyticOn_rectangle K z w)
      hzRectangle hzNonzero
  let Z : Finset ℂ := hfinite.toFinset
  have hZset : (Z : Set ℂ) = Rectangle z w ∩ F ⁻¹' ({0} : Set ℂ) :=
    hfinite.coe_toFinset
  refine ⟨Z, hZset, ?_⟩
  · apply v15_completedZetaPoleRemoved_weighted_rectangle hre him hborder Z
    · intro s hs
      change F s = 0 ↔ s ∈ Z
      simp only [Z, Set.Finite.mem_toFinset, mem_inter_iff, mem_preimage,
        mem_singleton_iff, hs, true_and]
    · intro s hs
      have hs' : s ∈ Rectangle z w ∩ F ⁻¹' ({0} : Set ℂ) := by
        rw [← hZset]
        exact hs
      exact hs'.1

/-- The same finite identity on the symmetric source rectangle
`[1-c,c] × [-R,R]`. -/
theorem exists_v15_odlyzko_symmetric_rectangle_identity
    {c R : ℝ} (hc : 1 / 2 ≤ c) (hR : 0 ≤ R)
    (hborder : ∀ s ∈
        RectangleBorder (v15OdlyzkoContourLower c R)
          (v15OdlyzkoContourUpper c R),
      DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s ≠ 0) :
    ∃ Z : Finset ℂ,
      (Z : Set ℂ) =
        Rectangle (v15OdlyzkoContourLower c R)
            (v15OdlyzkoContourUpper c R) ∩
          (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ⁻¹'
            ({0} : Set ℂ) ∧
      RectangleIntegral'
          (fun s ↦ v15OdlyzkoPhi s *
            logDeriv
              (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s)
          (v15OdlyzkoContourLower c R) (v15OdlyzkoContourUpper c R) =
        ∑ ρ ∈ Z,
          (analyticOrderNatAt
            (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ρ : ℂ) *
              v15OdlyzkoPhi ρ := by
  apply exists_v15_completedZetaPoleRemoved_weighted_rectangle
  · simp [v15OdlyzkoContourLower, v15OdlyzkoContourUpper]
    linarith
  · simp [v15OdlyzkoContourLower, v15OdlyzkoContourUpper]
    linarith
  · exact hborder

/-- Above every nonnegative starting height, one can choose a zero-free
symmetric contour and obtain its exact finite weighted zero identity.  The
real part of the resulting zero sum is nonnegative.  This packages all finite
contour facts needed before the limiting argument. -/
theorem exists_v15_odlyzko_symmetric_rectangle_identity_above
    (K : Type*) [Field K] [NumberField K]
    {c T : ℝ} (hc : 1 < c) (hT : 0 ≤ T) :
    ∃ R : ℝ, T < R ∧ R < T + 1 ∧
      (∀ s ∈ RectangleBorder (v15OdlyzkoContourLower c R)
          (v15OdlyzkoContourUpper c R),
        DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s ≠ 0) ∧
      ∃ Z : Finset ℂ,
        (Z : Set ℂ) =
          Rectangle (v15OdlyzkoContourLower c R)
              (v15OdlyzkoContourUpper c R) ∩
            (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ⁻¹'
              ({0} : Set ℂ) ∧
        RectangleIntegral'
            (fun s ↦ v15OdlyzkoPhi s *
              logDeriv
                (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s)
            (v15OdlyzkoContourLower c R) (v15OdlyzkoContourUpper c R) =
          ∑ ρ ∈ Z,
            (analyticOrderNatAt
              (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ρ : ℂ) *
                v15OdlyzkoPhi ρ ∧
        0 ≤ (∑ ρ ∈ Z,
          (analyticOrderNatAt
            (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) ρ : ℂ) *
              v15OdlyzkoPhi ρ).re := by
  obtain ⟨R, hTR, hRT, hborder⟩ :=
    exists_v15_completedZetaPoleRemoved_zeroFree_symmetric_boundary
      K hc hT
  have hR : 0 ≤ R := hT.trans hTR.le
  obtain ⟨Z, hZset, hidentity⟩ :=
    exists_v15_odlyzko_symmetric_rectangle_identity
      (K := K) (c := c) (R := R) (by linarith) hR hborder
  have hzeros : ∀ s ∈ Z,
      DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K s = 0 := by
    intro s hs
    have hsSet : s ∈ (Z : Set ℂ) := hs
    rw [hZset] at hsSet
    exact hsSet.2
  exact ⟨R, hTR, hRT, hborder, Z, hZset, hidentity,
    v15_completedZetaPoleRemoved_zero_finset_re_nonneg Z hzeros⟩

end

end TraceEuclidean
