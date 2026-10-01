import TraceEuclidean.DegreeFiveRolleCompleteness
import TraceEuclidean.DegreeFiveRolleStageFour

/-!
# Completeness of the fourth Rolle stage for degree five

This module proves that every sharpened Hunter quintic reaches one of the
generated cubic rows and that its next coefficient belongs to that row's
kernel-checked finite range.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Membership in a certified third-stage row and its exact `a2` interval
places the corresponding coefficient triple in the explicit 191-element
frontier. -/
theorem degreeFiveStageThree_prefix_mem
    (entry : DegreeFiveStageThreeEntry)
    (hentry : entry ∈ degreeFiveStageThreeEntries)
    {a2 : ℤ} (ha2 : a2 ∈ entry.a2Candidates) :
    (entry.a4, entry.a3, a2) ∈ degreeFiveStageThreePrefixes := by
  have hrange :
      (entry.a4, entry.a3,
        cubicTranslationLowerBound entry.baseCoefficients
          entry.firstRoot 10,
        cubicTranslationUpperBound entry.baseCoefficients
          (-10) entry.secondRoot) ∈
        degreeFiveStageThreeExpectedRanges := by
    rw [← degreeFiveStageThreeRanges_checked]
    exact List.mem_map_of_mem hentry
  have ha2Bounds :
      cubicTranslationLowerBound entry.baseCoefficients
          entry.firstRoot 10 ≤ a2 ∧
        a2 ≤ cubicTranslationUpperBound entry.baseCoefficients
          (-10) entry.secondRoot := by
    simpa [DegreeFiveStageThreeEntry.a2Candidates,
      cubicTranslationCandidates, integerIcc] using ha2
  simp only [degreeFiveStageThreeExpectedRanges, List.mem_cons,
    List.not_mem_nil, or_false, Prod.mk.injEq] at hrange
  rcases hrange with h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨ha4, ha3, hlower, hupper⟩
  all_goals rw [hlower, hupper] at ha2Bounds
  all_goals rw [ha4, ha3]
  all_goals first
    | exact degreeFiveStageThreePrefixesRow000_mem_of_bounds
        ha2Bounds.1 ha2Bounds.2
    | exact degreeFiveStageThreePrefixesRow001_mem_of_bounds
        ha2Bounds.1 ha2Bounds.2
    | exact degreeFiveStageThreePrefixesRow002_mem_of_bounds
        ha2Bounds.1 ha2Bounds.2
    | exact degreeFiveStageThreePrefixesRow003_mem_of_bounds
        ha2Bounds.1 ha2Bounds.2
    | exact degreeFiveStageThreePrefixesRow004_mem_of_bounds
        ha2Bounds.1 ha2Bounds.2
    | exact degreeFiveStageThreePrefixesRow005_mem_of_bounds
        ha2Bounds.1 ha2Bounds.2
    | exact degreeFiveStageThreePrefixesRow006_mem_of_bounds
        ha2Bounds.1 ha2Bounds.2
    | exact degreeFiveStageThreePrefixesRow007_mem_of_bounds
        ha2Bounds.1 ha2Bounds.2
    | exact degreeFiveStageThreePrefixesRow008_mem_of_bounds
        ha2Bounds.1 ha2Bounds.2
    | exact degreeFiveStageThreePrefixesRow009_mem_of_bounds
        ha2Bounds.1 ha2Bounds.2
    | exact degreeFiveStageThreePrefixesRow010_mem_of_bounds
        ha2Bounds.1 ha2Bounds.2
    | exact degreeFiveStageThreePrefixesRow011_mem_of_bounds
        ha2Bounds.1 ha2Bounds.2
    | exact degreeFiveStageThreePrefixesRow012_mem_of_bounds
        ha2Bounds.1 ha2Bounds.2
    | exact degreeFiveStageThreePrefixesRow013_mem_of_bounds
        ha2Bounds.1 ha2Bounds.2
    | exact degreeFiveStageThreePrefixesRow014_mem_of_bounds
        ha2Bounds.1 ha2Bounds.2
    | exact degreeFiveStageThreePrefixesRow015_mem_of_bounds
        ha2Bounds.1 ha2Bounds.2
    | exact degreeFiveStageThreePrefixesRow016_mem_of_bounds
        ha2Bounds.1 ha2Bounds.2
    | exact degreeFiveStageThreePrefixesRow017_mem_of_bounds
        ha2Bounds.1 ha2Bounds.2
    | exact degreeFiveStageThreePrefixesRow018_mem_of_bounds
        ha2Bounds.1 ha2Bounds.2
    | exact degreeFiveStageThreePrefixesRow019_mem_of_bounds
        ha2Bounds.1 ha2Bounds.2

set_option maxRecDepth 100000 in
/-- A common root of a real polynomial and its derivative witnesses
nonseparability. -/
theorem not_separable_of_common_real_root {p : ℝ[X]} {x : ℝ}
    (hp : p.eval x = 0) (hderivative : p.derivative.eval x = 0) :
    ¬p.Separable := by
  intro hseparable
  have hne := hseparable.eval₂_derivative_ne_zero (RingHom.id ℝ)
    (x := x) (by simpa only [Polynomial.eval₂_id] using hp)
  exact hne (by simpa only [Polynomial.eval₂_id] using hderivative)

/-- The first discarded cubic has the double root `1`. -/
theorem degreeFive_rejectedCubic_0_not_separable :
    ¬(integerPolynomialReal [8, -6, -12, 10]).Separable := by
  apply not_separable_of_common_real_root (x := 1)
  · norm_num [integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval]
  · rw [integerPolynomialReal_derivative]
    norm_num [integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval,
      DensePolynomial.derivative, DensePolynomial.add]

/-- The second discarded cubic has the double root `0`. -/
theorem degreeFive_rejectedCubic_1_not_separable :
    ¬(integerPolynomialReal [0, 0, -12, 10]).Separable := by
  apply not_separable_of_common_real_root (x := 0)
  · norm_num [integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval]
  · rw [integerPolynomialReal_derivative]
    norm_num [integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval,
      DensePolynomial.derivative, DensePolynomial.add]

/-- The third discarded cubic has the double root `1`. -/
theorem degreeFive_rejectedCubic_2_not_separable :
    ¬(integerPolynomialReal [14, -18, -6, 10]).Separable := by
  apply not_separable_of_common_real_root (x := 1)
  · norm_num [integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval]
  · rw [integerPolynomialReal_derivative]
    norm_num [integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval,
      DensePolynomial.derivative, DensePolynomial.add]

/-- The fourth discarded cubic has the double root `0`. -/
theorem degreeFive_rejectedCubic_3_not_separable :
    ¬(integerPolynomialReal [0, 0, -6, 10]).Separable := by
  apply not_separable_of_common_real_root (x := 0)
  · norm_num [integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval]
  · rw [integerPolynomialReal_derivative]
    norm_num [integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval,
      DensePolynomial.derivative, DensePolynomial.add]

/-- Every separable cubic triple in the 191-element frontier is represented
by one of the 187 generated fourth-stage rows. -/
theorem degreeFiveStageFour_exists_entry_of_prefix
    {a4 a3 a2 : ℤ}
    (hprefix :
      (a4, a3, a2) ∈ degreeFiveStageThreePrefixes)
    (hseparable :
      (integerPolynomialReal
        [a2, 3 * a3, 6 * a4, 10]).Separable) :
    ∃ entry ∈ degreeFiveStageFourEntries,
      entry.a4 = a4 ∧ entry.a3 = a3 ∧ entry.a2 = a2 := by
  have hpartition :
      (a4, a3, a2) ∈
        degreeFiveStageFourTopTriples.toFinset ∪
          degreeFiveStageFourRejectedTriples.toFinset := by
    rw [← degreeFiveStageFour_partition]
    simpa using hprefix
  rw [Finset.mem_union] at hpartition
  rcases hpartition with htop | hrejected
  · have htopList :
        (a4, a3, a2) ∈ degreeFiveStageFourTopTriples := by
      simpa using htop
    rw [← degreeFiveStageFourTopTriples_checked] at htopList
    obtain ⟨entry, hentry, hcoefficients⟩ :=
      List.mem_map.mp htopList
    refine ⟨entry, hentry, ?_⟩
    simpa only [Prod.mk.injEq] using hcoefficients
  · have hrejectedList :
        (a4, a3, a2) ∈ degreeFiveStageFourRejectedTriples := by
      simpa using hrejected
    simp only [degreeFiveStageFourRejectedTriples, List.mem_cons,
      List.not_mem_nil, or_false, Prod.mk.injEq] at hrejectedList
    rcases hrejectedList with h | h | h | h
    · rcases h with ⟨rfl, rfl, rfl⟩
      exact (degreeFive_rejectedCubic_0_not_separable
        hseparable).elim
    · rcases h with ⟨rfl, rfl, rfl⟩
      exact (degreeFive_rejectedCubic_1_not_separable
        hseparable).elim
    · rcases h with ⟨rfl, rfl, rfl⟩
      exact (degreeFive_rejectedCubic_2_not_separable
        hseparable).elim
    · rcases h with ⟨rfl, rfl, rfl⟩
      exact (degreeFive_rejectedCubic_3_not_separable
        hseparable).elim

/-- Every sharpened quintic Hunter candidate reaches a certified cubic row
whose three stored coefficients are its actual top coefficients. -/
theorem degreeFive_minimumHunterCandidate_stageFour_complete
    {f : ℤ[X]} (h : HunterPolynomialCandidate 5 67 f) :
    ∃ entry ∈ degreeFiveStageFourEntries,
      entry.a4 = f.coeff 4 ∧ entry.a3 = f.coeff 3 ∧
        entry.a2 = f.coeff 2 := by
  obtain ⟨parent, hparent, ha4, ha3, ha2⟩ :=
    degreeFive_minimumHunterCandidate_stageThree_frontier_complete h
  have hprefix :
      (f.coeff 4, f.coeff 3, f.coeff 2) ∈
        degreeFiveStageThreePrefixes := by
    have hparentPrefix :=
      degreeFiveStageThree_prefix_mem parent hparent ha2
    simpa [ha4, ha3] using hparentPrefix
  let p : ℝ[X] := f.map (algebraMap ℤ ℝ)
  have hpdegree : p.natDegree = 5 := by
    dsimp [p]
    rw [Polynomial.natDegree_map_eq_of_injective
      (Int.cast_injective : Function.Injective (algebraMap ℤ ℝ)),
      h.2.2.1]
  have hpseparable : p.Separable := by
    simpa [p] using hunterPolynomialCandidate_separable_real h
  have hstageEq :
      integerPolynomialReal
          [f.coeff 2, 3 * f.coeff 3, 6 * f.coeff 4, 10] =
        voightDerivativeStage p 2 := by
    symm
    simpa [p] using
      degreeFive_secondDerivativeStage_eq h.1 h.2.2.1
  have hstageSeparable :
      (integerPolynomialReal
        [f.coeff 2, 3 * f.coeff 3, 6 * f.coeff 4, 10]).Separable := by
    rw [hstageEq]
    exact voightDerivativeStage_separable h.2.2.2.1 hpseparable
      (by rw [hpdegree]; norm_num)
  exact degreeFiveStageFour_exists_entry_of_prefix
    hprefix hstageSeparable

/-- The normalized first derivative of a monic quintic is the quartic used
at the next coefficient-pruning step. -/
theorem degreeFive_firstDerivativeStage_eq
    {f : ℤ[X]} (hmonic : f.Monic) (hdegree : f.natDegree = 5) :
    voightDerivativeStage (f.map (algebraMap ℤ ℝ)) 1 =
      integerPolynomialReal
        [f.coeff 1, 2 * f.coeff 2, 3 * f.coeff 3,
          4 * f.coeff 4, 5] := by
  ext m
  rw [voightDerivativeStage_coeff]
  rw [integerPolynomialReal, Polynomial.coeff_map]
  rw [Polynomial.coeff_map]
  rw [DensePolynomial.coeff_toPolynomial]
  by_cases hm0 : m = 0
  · subst m
    norm_num
  by_cases hm1 : m = 1
  · subst m
    norm_num
  by_cases hm2 : m = 2
  · subst m
    norm_num
  by_cases hm3 : m = 3
  · subst m
    norm_num
  by_cases hm4 : m = 4
  · subst m
    have hcoeff : f.coeff 5 = 1 := by
      rw [← hdegree]
      exact hmonic.coeff_natDegree
    norm_num [hcoeff]
  have hm5 : 5 ≤ m := by omega
  have hright :
      [f.coeff 1, 2 * f.coeff 2, 3 * f.coeff 3,
        4 * f.coeff 4, 5].getD m 0 = 0 := by
    rw [List.getD_eq_default]
    simp
    omega
  rw [hright, map_zero]
  have hcoeff : f.coeff (m + 1) = 0 := by
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    rw [hdegree]
    omega
  rw [hcoeff, map_zero]
  ring

/-- The derivative of the quartic stage is twice the certified cubic stage,
so the two polynomials have the same three critical roots. -/
theorem degreeFive_quartic_derivative_eq
    (a1 a2 a3 a4 : ℤ) :
    (integerPolynomialReal
      [a1, 2 * a2, 3 * a3, 4 * a4, 5]).derivative =
      C 2 * integerPolynomialReal
        [a2, 3 * a3, 6 * a4, 10] := by
  rw [integerPolynomialReal_derivative]
  ext n
  rw [integerPolynomialReal, Polynomial.coeff_map,
    DensePolynomial.coeff_toPolynomial]
  rw [Polynomial.coeff_C_mul,
    integerPolynomialReal, Polynomial.coeff_map,
    DensePolynomial.coeff_toPolynomial]
  by_cases hn : n ≤ 4
  · interval_cases n <;>
      norm_num [DensePolynomial.derivative,
        DensePolynomial.add] <;> ring
  · have hn' : 5 ≤ n := by omega
    rw [List.getD_eq_default, List.getD_eq_default]
    all_goals norm_num [DensePolynomial.derivative,
      DensePolynomial.add] at *
    all_goals omega

/-- Once a certified cubic row is identified, the next coefficient belongs
to its exact kernel-checked `a1` interval. -/
theorem degreeFive_minimumHunterCandidate_a1_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 5 67 f)
    (entry : DegreeFiveStageFourEntry)
    (hentry : entry ∈ degreeFiveStageFourEntries)
    (ha4 : entry.a4 = f.coeff 4)
    (ha3 : entry.a3 = f.coeff 3)
    (ha2 : entry.a2 = f.coeff 2) :
    f.coeff 1 ∈ entry.a1Candidates := by
  have hvalid : entry.Valid :=
    (List.forall_iff_forall_mem.mp
      degreeFiveStageFourEntries_valid) entry hentry
  let p : ℝ[X] := f.map (algebraMap ℤ ℝ)
  let q : ℝ[X] := integerPolynomialReal
    [f.coeff 1, 2 * entry.a2, 3 * entry.a3, 4 * entry.a4, 5]
  let r : ℝ[X] := integerPolynomialReal entry.derivativeCoefficients
  have hpdegree : p.natDegree = 5 := by
    dsimp [p]
    rw [Polynomial.natDegree_map_eq_of_injective
      (Int.cast_injective : Function.Injective (algebraMap ℤ ℝ)),
      h.2.2.1]
  have hpseparable : p.Separable := by
    simpa [p] using hunterPolynomialCandidate_separable_real h
  have hqEq : q = voightDerivativeStage p 1 := by
    symm
    simpa [p, q, ha4, ha3, ha2] using
      degreeFive_firstDerivativeStage_eq h.1 h.2.2.1
  have hqsplit : q.Splits := by
    rw [hqEq]
    exact voightDerivativeStage_splits h.2.2.2.1 1
  have hqseparable : q.Separable := by
    rw [hqEq]
    exact voightDerivativeStage_separable h.2.2.2.1 hpseparable
      (by rw [hpdegree]; norm_num)
  have hqdegree : q.natDegree = 4 := by
    apply integerPolynomial_natDegree_of_generalRootIntervals
    · norm_num
    · norm_num
  have hqlead : 0 < q.leadingCoeff := by
    rw [hqEq]
    exact voightDerivativeStage_leadingCoeff_pos
      (h.1.map (algebraMap ℤ ℝ))
      (by rw [hpdegree]; norm_num)
  have hqbounds : ∀ z ∈ q.roots, (-10 : ℝ) < z ∧ z < 10 := by
    rw [hqEq]
    apply voightDerivativeStage_roots_strict_bounds
      h.2.2.2.1 hpseparable
    · simpa [p] using
        degreeFive_minimumHunterCandidate_root_bounds h
    · rw [hpdegree]
      norm_num
  have hrsplit : r.Splits :=
    integerPolynomial_splits_of_generalRootIntervals hvalid
  have hrdegree : r.natDegree = 3 :=
    integerPolynomial_natDegree_of_generalRootIntervals
      hvalid.2.1 hvalid.2.2.1
  have hqderivEq : q.derivative = C 2 * r := by
    simpa [q, r,
      DegreeFiveStageFourEntry.derivativeCoefficients] using
      degreeFive_quartic_derivative_eq
        (f.coeff 1) entry.a2 entry.a3 entry.a4
  let i0 : Fin r.natDegree := ⟨0, by rw [hrdegree]; norm_num⟩
  let i1 : Fin r.natDegree := ⟨1, by rw [hrdegree]; norm_num⟩
  let i2 : Fin r.natDegree := ⟨2, by rw [hrdegree]; norm_num⟩
  let qi0 : Fin q.derivative.natDegree :=
    ⟨i0, by
      rw [hqderivEq, Polynomial.natDegree_C_mul
        (by norm_num : (2 : ℝ) ≠ 0)]
      exact i0.isLt⟩
  let qi1 : Fin q.derivative.natDegree :=
    ⟨i1, by
      rw [hqderivEq, Polynomial.natDegree_C_mul
        (by norm_num : (2 : ℝ) ≠ 0)]
      exact i1.isLt⟩
  let qi2 : Fin q.derivative.natDegree :=
    ⟨i2, by
      rw [hqderivEq, Polynomial.natDegree_C_mul
        (by norm_num : (2 : ℝ) ≠ 0)]
      exact i2.isLt⟩
  have hrootEq0 :
      voightSortedRoot q.derivative
          (splits_derivative_of_splits_real hqsplit) qi0 =
        voightSortedRoot r hrsplit i0 := by
    simpa [qi0] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (2 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hqsplit)
        hrsplit hqderivEq i0
  have hrootEq1 :
      voightSortedRoot q.derivative
          (splits_derivative_of_splits_real hqsplit) qi1 =
        voightSortedRoot r hrsplit i1 := by
    simpa [qi1] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (2 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hqsplit)
        hrsplit hqderivEq i1
  have hrootEq2 :
      voightSortedRoot q.derivative
          (splits_derivative_of_splits_real hqsplit) qi2 =
        voightSortedRoot r hrsplit i2 := by
    simpa [qi2] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (2 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hqsplit)
        hrsplit hqderivEq i2
  let firstIndex : Fin entry.rootIntervals.length :=
    ⟨0, by simp [DegreeFiveStageFourEntry.rootIntervals]⟩
  let secondIndex : Fin entry.rootIntervals.length :=
    ⟨1, by simp [DegreeFiveStageFourEntry.rootIntervals]⟩
  let thirdIndex : Fin entry.rootIntervals.length :=
    ⟨2, by simp [DegreeFiveStageFourEntry.rootIntervals]⟩
  have hfirstMem : voightSortedRoot r hrsplit i0 ∈
      Set.Icc (entry.firstRoot.lower : ℝ)
        (entry.firstRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid firstIndex
    simpa [r, i0, firstIndex,
      DegreeFiveStageFourEntry.rootIntervals] using hmem
  have hsecondMem : voightSortedRoot r hrsplit i1 ∈
      Set.Icc (entry.secondRoot.lower : ℝ)
        (entry.secondRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid secondIndex
    simpa [r, i1, secondIndex,
      DegreeFiveStageFourEntry.rootIntervals] using hmem
  have hthirdMem : voightSortedRoot r hrsplit i2 ∈
      Set.Icc (entry.thirdRoot.lower : ℝ)
        (entry.thirdRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid thirdIndex
    simpa [r, i2, thirdIndex,
      DegreeFiveStageFourEntry.rootIntervals] using hmem
  have hfirstSign :
      q.eval (voightSortedRoot r hrsplit i0) ≤ 0 := by
    have hsign :=
      eval_sign_at_derivativeSortedRoot_of_leadingCoeff_pos
        hqsplit hqlead hqseparable qi0
    rw [hrootEq0] at hsign
    norm_num [hqdegree, qi0, i0] at hsign
    linarith
  have hsecondSign :
      0 ≤ q.eval (voightSortedRoot r hrsplit i1) := by
    have hsign :=
      eval_sign_at_derivativeSortedRoot_of_leadingCoeff_pos
        hqsplit hqlead hqseparable qi1
    rw [hrootEq1] at hsign
    simpa [hqdegree, qi1, i1] using hsign
  have hthirdSign :
      q.eval (voightSortedRoot r hrsplit i2) ≤ 0 := by
    have hsign :=
      eval_sign_at_derivativeSortedRoot_of_leadingCoeff_pos
        hqsplit hqlead hqseparable qi2
    rw [hrootEq2] at hsign
    norm_num [hqdegree, qi2, i2] at hsign
    linarith
  have hleftSign : 0 ≤ q.eval (-10) := by
    have hsign :=
      eval_sign_left_of_all_roots_of_leadingCoeff_pos
        hqsplit hqlead (-10) (by
          intro y hy
          exact (hqbounds y hy).1.le)
    norm_num [hqdegree] at hsign
    exact hsign
  have hrightSign : 0 ≤ q.eval 10 :=
    eval_nonneg_right_of_all_roots_of_leadingCoeff_pos
      hqsplit hqlead 10 (by
        intro y hy
        exact (hqbounds y hy).2.le)
  apply mem_quarticTranslationCandidates_of_signs
    entry.baseCoefficients (-10) 10 entry.firstRoot entry.secondRoot
    entry.thirdRoot
    (by
      have hforall := (List.forall_iff_forall_mem.mp
        hvalid.2.2.2.2.1) entry.firstRoot
        (by simp [DegreeFiveStageFourEntry.rootIntervals])
      exact hforall.1.le)
    (by
      have hforall := (List.forall_iff_forall_mem.mp
        hvalid.2.2.2.2.1) entry.secondRoot
        (by simp [DegreeFiveStageFourEntry.rootIntervals])
      exact hforall.1.le)
    (by
      have hforall := (List.forall_iff_forall_mem.mp
        hvalid.2.2.2.2.1) entry.thirdRoot
        (by simp [DegreeFiveStageFourEntry.rootIntervals])
      exact hforall.1.le)
    (voightSortedRoot r hrsplit i0)
    (voightSortedRoot r hrsplit i1)
    (voightSortedRoot r hrsplit i2)
    hfirstMem hsecondMem hthirdMem (f.coeff 1)
  · simpa [q, DegreeFiveStageFourEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval] using hleftSign
  · simpa [q, DegreeFiveStageFourEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hfirstSign
  · simpa [q, DegreeFiveStageFourEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hsecondSign
  · simpa [q, DegreeFiveStageFourEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hthirdSign
  · simpa [q, DegreeFiveStageFourEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hrightSign

/-- Complete second recursion frontier: every sharpened Hunter quintic has a
generated cubic row and its actual `a1` is one of that row's certified values. -/
theorem degreeFive_minimumHunterCandidate_stageFour_frontier_complete
    {f : ℤ[X]} (h : HunterPolynomialCandidate 5 67 f) :
    ∃ entry ∈ degreeFiveStageFourEntries,
      entry.a4 = f.coeff 4 ∧ entry.a3 = f.coeff 3 ∧
        entry.a2 = f.coeff 2 ∧ f.coeff 1 ∈ entry.a1Candidates := by
  obtain ⟨entry, hentry, ha4, ha3, ha2⟩ :=
    degreeFive_minimumHunterCandidate_stageFour_complete h
  exact ⟨entry, hentry, ha4, ha3, ha2,
    degreeFive_minimumHunterCandidate_a1_mem
      h entry hentry ha4 ha3 ha2⟩

end

end TraceEuclidean
