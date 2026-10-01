import TraceEuclidean.DegreeSevenRolleStageThreeCompleteness
import TraceEuclidean.DegreeSevenRolleStageFour

/-!
# Completeness of the fourth Rolle stage for degree seven

This module proves that every sharpened Hunter septic reaches one of the
generated cubic rows and that its next coefficient belongs to that row's
kernel-checked finite range.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

/-- Membership in a certified third-stage row and its exact `a4` interval
places the corresponding coefficient triple in the explicit 1,641-element
frontier. -/
theorem degreeSevenStageThree_prefix_mem
    (entry : DegreeSevenStageThreeEntry)
    (hentry : entry ∈ degreeSevenStageThreeEntries)
    {a4 : ℤ} (ha4 : a4 ∈ entry.a4Candidates) :
    (entry.a6, entry.a5, a4) ∈ degreeSevenStageThreePrefixes := by
  rw [degreeSevenStageThreePrefixes, List.mem_flatMap]
  refine ⟨entry, hentry, ?_⟩
  rw [List.mem_map]
  exact ⟨a4, Finset.mem_toList.mpr ha4, rfl⟩

set_option maxRecDepth 100000 in
/-- A common root of a real polynomial and its derivative witnesses
nonseparability. -/
theorem degreeSeven_not_separable_of_common_real_root
    {p : ℝ[X]} {x : ℝ}
    (hp : p.eval x = 0) (hderivative : p.derivative.eval x = 0) :
    ¬p.Separable := by
  intro hseparable
  have hne := hseparable.eval₂_derivative_ne_zero (RingHom.id ℝ)
    (x := x) (by simpa only [Polynomial.eval₂_id] using hp)
  exact hne (by simpa only [Polynomial.eval₂_id] using hderivative)

/-- The first discarded cubic has the double root `1`. -/
theorem degreeSeven_rejectedCubic_0_not_separable :
    ¬(integerPolynomialReal [25, -15, -45, 35]).Separable := by
  apply degreeSeven_not_separable_of_common_real_root (x := 1)
  · norm_num [integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval]
  · rw [integerPolynomialReal_derivative]
    norm_num [integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval,
      DensePolynomial.derivative, DensePolynomial.add]

/-- The second discarded cubic has the double root `0`. -/
theorem degreeSeven_rejectedCubic_1_not_separable :
    ¬(integerPolynomialReal [0, 0, -45, 35]).Separable := by
  apply degreeSeven_not_separable_of_common_real_root (x := 0)
  · norm_num [integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval]
  · rw [integerPolynomialReal_derivative]
    norm_num [integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval,
      DensePolynomial.derivative, DensePolynomial.add]

/-- The third discarded cubic has the double root `1`. -/
theorem degreeSeven_rejectedCubic_2_not_separable :
    ¬(integerPolynomialReal [40, -45, -30, 35]).Separable := by
  apply degreeSeven_not_separable_of_common_real_root (x := 1)
  · norm_num [integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval]
  · rw [integerPolynomialReal_derivative]
    norm_num [integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval,
      DensePolynomial.derivative, DensePolynomial.add]

/-- The fourth discarded cubic has the double root `0`. -/
theorem degreeSeven_rejectedCubic_3_not_separable :
    ¬(integerPolynomialReal [0, 0, -30, 35]).Separable := by
  apply degreeSeven_not_separable_of_common_real_root (x := 0)
  · norm_num [integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval]
  · rw [integerPolynomialReal_derivative]
    norm_num [integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval,
      DensePolynomial.derivative, DensePolynomial.add]

/-- The fifth discarded cubic has the double root `0`. -/
theorem degreeSeven_rejectedCubic_4_not_separable :
    ¬(integerPolynomialReal [0, 0, -15, 35]).Separable := by
  apply degreeSeven_not_separable_of_common_real_root (x := 0)
  · norm_num [integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval]
  · rw [integerPolynomialReal_derivative]
    norm_num [integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval,
      DensePolynomial.derivative, DensePolynomial.add]

/-- Every separable next coefficient of a certified quadratic parent is
represented by one of the 1,636 generated fourth-stage rows. -/
theorem degreeSevenStageFour_exists_entry_of_parent
    (parent : DegreeSevenStageThreeEntry)
    (hparent : parent ∈ degreeSevenStageThreeEntries)
    {a4 : ℤ} (ha4 : a4 ∈ parent.a4Candidates)
    (hseparable : (integerPolynomialReal
      [a4, 5 * parent.a5, 15 * parent.a6, 35]).Separable) :
    ∃ entry ∈ degreeSevenStageFourEntries,
      entry.a6 = parent.a6 ∧ entry.a5 = parent.a5 ∧
        entry.a4 = a4 := by
  have hparentMap :
      parent ∈ degreeSevenStageFourCoverages.map
        DegreeSevenStageFourCoverage.parent := by
    rw [degreeSevenStageFourCoverage_parents_checked]
    exact hparent
  obtain ⟨coverage, hcoverage, hcoverageParent⟩ :=
    List.mem_map.mp hparentMap
  have hcoverageValid : coverage.Valid :=
    (List.forall_iff_forall_mem.mp
      degreeSevenStageFourCoverages_valid) coverage hcoverage
  have hclassified :
      a4 ∈ coverage.surviving.toFinset ∪ coverage.rejected.toFinset := by
    rw [← hcoverageValid, hcoverageParent]
    exact ha4
  rw [Finset.mem_union] at hclassified
  rcases hclassified with hsurviving | hrejected
  · have hsurvivingList : a4 ∈ coverage.surviving := by
      simpa using hsurviving
    have hcoverageTriple :
        (parent.a6, parent.a5, a4) ∈
          degreeSevenStageFourCoverageSurvivingTriples := by
      rw [degreeSevenStageFourCoverageSurvivingTriples,
        List.mem_flatMap]
      refine ⟨coverage, hcoverage, ?_⟩
      rw [List.mem_map]
      refine ⟨a4, hsurvivingList, ?_⟩
      simp [hcoverageParent]
    have htopList :
        (parent.a6, parent.a5, a4) ∈
          degreeSevenStageFourTopTriples := by
      rw [← degreeSevenStageFourCoverage_surviving_checked]
      exact hcoverageTriple
    rw [← degreeSevenStageFourTopTriples_checked] at htopList
    obtain ⟨entry, hentry, hcoefficients⟩ :=
      List.mem_map.mp htopList
    refine ⟨entry, hentry, ?_⟩
    simpa only [Prod.mk.injEq] using hcoefficients
  · have hrejectedList : a4 ∈ coverage.rejected := by
      simpa using hrejected
    have hcoverageTriple :
        (parent.a6, parent.a5, a4) ∈
          degreeSevenStageFourCoverageRejectedTriples := by
      rw [degreeSevenStageFourCoverageRejectedTriples,
        List.mem_flatMap]
      refine ⟨coverage, hcoverage, ?_⟩
      rw [List.mem_map]
      refine ⟨a4, hrejectedList, ?_⟩
      simp [hcoverageParent]
    have hrejectedList :
        (parent.a6, parent.a5, a4) ∈
          degreeSevenStageFourRejectedTriples := by
      rw [← degreeSevenStageFourCoverage_rejected_checked]
      exact hcoverageTriple
    simp only [degreeSevenStageFourRejectedTriples, List.mem_cons,
      List.not_mem_nil, or_false, Prod.mk.injEq] at hrejectedList
    rcases hrejectedList with h | h | h | h | h
    · rcases h with ⟨ha6, ha5, ha4⟩
      exact (degreeSeven_rejectedCubic_0_not_separable
        (by simpa [ha6, ha5, ha4] using hseparable)).elim
    · rcases h with ⟨ha6, ha5, ha4⟩
      exact (degreeSeven_rejectedCubic_1_not_separable
        (by simpa [ha6, ha5, ha4] using hseparable)).elim
    · rcases h with ⟨ha6, ha5, ha4⟩
      exact (degreeSeven_rejectedCubic_2_not_separable
        (by simpa [ha6, ha5, ha4] using hseparable)).elim
    · rcases h with ⟨ha6, ha5, ha4⟩
      exact (degreeSeven_rejectedCubic_3_not_separable
        (by simpa [ha6, ha5, ha4] using hseparable)).elim
    · rcases h with ⟨ha6, ha5, ha4⟩
      exact (degreeSeven_rejectedCubic_4_not_separable
        (by simpa [ha6, ha5, ha4] using hseparable)).elim

/-- Every sharpened septic Hunter candidate reaches a certified cubic row
whose three stored coefficients are its actual top coefficients. -/
theorem degreeSeven_minimumHunterCandidate_stageFour_complete
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f) :
    ∃ entry ∈ degreeSevenStageFourEntries,
      entry.a6 = f.coeff 6 ∧ entry.a5 = f.coeff 5 ∧
        entry.a4 = f.coeff 4 := by
  obtain ⟨parent, hparent, ha6, ha5, ha4⟩ :=
    degreeSeven_minimumHunterCandidate_stageThree_frontier_complete h
  let p : ℝ[X] := f.map (algebraMap ℤ ℝ)
  have hpdegree : p.natDegree = 7 := by
    dsimp [p]
    rw [Polynomial.natDegree_map_eq_of_injective
      (Int.cast_injective : Function.Injective (algebraMap ℤ ℝ)),
      h.2.2.1]
  have hpseparable : p.Separable := by
    simpa [p] using hunterPolynomialCandidate_separable_real_general h
  have hstageEq :
      integerPolynomialReal
          [f.coeff 4, 5 * f.coeff 5, 15 * f.coeff 6, 35] =
        voightDerivativeStage p 4 := by
    symm
    simpa [p] using
      degreeSeven_fourthDerivativeStage_eq h.1 h.2.2.1
  have hstageSeparable :
      (integerPolynomialReal
        [f.coeff 4, 5 * f.coeff 5, 15 * f.coeff 6, 35]).Separable := by
    rw [hstageEq]
    exact voightDerivativeStage_separable h.2.2.2.1 hpseparable
      (by rw [hpdegree]; norm_num)
  obtain ⟨entry, hentry, hentry6, hentry5, hentry4⟩ :=
    degreeSevenStageFour_exists_entry_of_parent
      parent hparent ha4 (by simpa [ha6, ha5] using hstageSeparable)
  exact ⟨entry, hentry, hentry6.trans ha6, hentry5.trans ha5,
    hentry4⟩

/-- The normalized third derivative of a monic septic is the quartic used
at the next coefficient-pruning step. -/
theorem degreeSeven_thirdDerivativeStage_eq
    {f : ℤ[X]} (hmonic : f.Monic) (hdegree : f.natDegree = 7) :
    voightDerivativeStage (f.map (algebraMap ℤ ℝ)) 3 =
      integerPolynomialReal
        [f.coeff 3, 4 * f.coeff 4, 10 * f.coeff 5,
          20 * f.coeff 6, 35] := by
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
    have hcoeff : f.coeff 7 = 1 := by
      rw [← hdegree]
      exact hmonic.coeff_natDegree
    norm_num [hcoeff]
  have hm5 : 5 ≤ m := by omega
  have hright :
      [f.coeff 3, 4 * f.coeff 4, 10 * f.coeff 5,
        20 * f.coeff 6, 35].getD m 0 = 0 := by
    rw [List.getD_eq_default]
    simp
    omega
  rw [hright, map_zero]
  have hcoeff : f.coeff (m + 3) = 0 := by
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    rw [hdegree]
    omega
  rw [hcoeff, map_zero]
  ring

/-- The derivative of the quartic stage is four times the certified cubic stage,
so the two polynomials have the same three critical roots. -/
theorem degreeSeven_quartic_derivative_eq
    (a3 a4 a5 a6 : ℤ) :
    (integerPolynomialReal
      [a3, 4 * a4, 10 * a5, 20 * a6, 35]).derivative =
      C 4 * integerPolynomialReal
        [a4, 5 * a5, 15 * a6, 35] := by
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
to its exact kernel-checked `a3` interval. -/
theorem degreeSeven_minimumHunterCandidate_a3_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (entry : DegreeSevenStageFourEntry)
    (hentry : entry ∈ degreeSevenStageFourEntries)
    (ha6 : entry.a6 = f.coeff 6)
    (ha5 : entry.a5 = f.coeff 5)
    (ha4 : entry.a4 = f.coeff 4) :
    f.coeff 3 ∈ entry.a3Candidates := by
  have hvalid : entry.Valid :=
    (List.forall_iff_forall_mem.mp
      degreeSevenStageFourEntries_valid) entry hentry
  let p : ℝ[X] := f.map (algebraMap ℤ ℝ)
  let q : ℝ[X] := integerPolynomialReal
    [f.coeff 3, 4 * entry.a4, 10 * entry.a5, 20 * entry.a6, 35]
  let r : ℝ[X] := integerPolynomialReal entry.derivativeCoefficients
  have hpdegree : p.natDegree = 7 := by
    dsimp [p]
    rw [Polynomial.natDegree_map_eq_of_injective
      (Int.cast_injective : Function.Injective (algebraMap ℤ ℝ)),
      h.2.2.1]
  have hpseparable : p.Separable := by
    simpa [p] using hunterPolynomialCandidate_separable_real_general h
  have hqEq : q = voightDerivativeStage p 3 := by
    symm
    simpa [p, q, ha6, ha5, ha4] using
      degreeSeven_thirdDerivativeStage_eq h.1 h.2.2.1
  have hqsplit : q.Splits := by
    rw [hqEq]
    exact voightDerivativeStage_splits h.2.2.2.1 3
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
  have hqbounds : ∀ z ∈ q.roots, (-16 : ℝ) < z ∧ z < 16 := by
    rw [hqEq]
    apply voightDerivativeStage_roots_strict_bounds
      h.2.2.2.1 hpseparable
    · simpa [p] using
        degreeSeven_minimumHunterCandidate_root_bounds h
    · rw [hpdegree]
      norm_num
  have hrsplit : r.Splits :=
    integerPolynomial_splits_of_generalRootIntervals hvalid
  have hrdegree : r.natDegree = 3 :=
    integerPolynomial_natDegree_of_generalRootIntervals
      hvalid.2.1 hvalid.2.2.1
  have hqderivEq : q.derivative = C 4 * r := by
    simpa [q, r,
      DegreeSevenStageFourEntry.derivativeCoefficients] using
      degreeSeven_quartic_derivative_eq
        (f.coeff 3) entry.a4 entry.a5 entry.a6
  let i0 : Fin r.natDegree := ⟨0, by rw [hrdegree]; norm_num⟩
  let i1 : Fin r.natDegree := ⟨1, by rw [hrdegree]; norm_num⟩
  let i2 : Fin r.natDegree := ⟨2, by rw [hrdegree]; norm_num⟩
  let qi0 : Fin q.derivative.natDegree :=
    ⟨i0, by
      rw [hqderivEq, Polynomial.natDegree_C_mul
        (by norm_num : (4 : ℝ) ≠ 0)]
      exact i0.isLt⟩
  let qi1 : Fin q.derivative.natDegree :=
    ⟨i1, by
      rw [hqderivEq, Polynomial.natDegree_C_mul
        (by norm_num : (4 : ℝ) ≠ 0)]
      exact i1.isLt⟩
  let qi2 : Fin q.derivative.natDegree :=
    ⟨i2, by
      rw [hqderivEq, Polynomial.natDegree_C_mul
        (by norm_num : (4 : ℝ) ≠ 0)]
      exact i2.isLt⟩
  have hrootEq0 :
      voightSortedRoot q.derivative
          (splits_derivative_of_splits_real hqsplit) qi0 =
        voightSortedRoot r hrsplit i0 := by
    simpa [qi0] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (4 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hqsplit)
        hrsplit hqderivEq i0
  have hrootEq1 :
      voightSortedRoot q.derivative
          (splits_derivative_of_splits_real hqsplit) qi1 =
        voightSortedRoot r hrsplit i1 := by
    simpa [qi1] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (4 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hqsplit)
        hrsplit hqderivEq i1
  have hrootEq2 :
      voightSortedRoot q.derivative
          (splits_derivative_of_splits_real hqsplit) qi2 =
        voightSortedRoot r hrsplit i2 := by
    simpa [qi2] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (4 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hqsplit)
        hrsplit hqderivEq i2
  let firstIndex : Fin entry.rootIntervals.length :=
    ⟨0, by simp [DegreeSevenStageFourEntry.rootIntervals]⟩
  let secondIndex : Fin entry.rootIntervals.length :=
    ⟨1, by simp [DegreeSevenStageFourEntry.rootIntervals]⟩
  let thirdIndex : Fin entry.rootIntervals.length :=
    ⟨2, by simp [DegreeSevenStageFourEntry.rootIntervals]⟩
  have hfirstMem : voightSortedRoot r hrsplit i0 ∈
      Set.Icc (entry.firstRoot.lower : ℝ)
        (entry.firstRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid firstIndex
    simpa [r, i0, firstIndex,
      DegreeSevenStageFourEntry.rootIntervals] using hmem
  have hsecondMem : voightSortedRoot r hrsplit i1 ∈
      Set.Icc (entry.secondRoot.lower : ℝ)
        (entry.secondRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid secondIndex
    simpa [r, i1, secondIndex,
      DegreeSevenStageFourEntry.rootIntervals] using hmem
  have hthirdMem : voightSortedRoot r hrsplit i2 ∈
      Set.Icc (entry.thirdRoot.lower : ℝ)
        (entry.thirdRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid thirdIndex
    simpa [r, i2, thirdIndex,
      DegreeSevenStageFourEntry.rootIntervals] using hmem
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
  have hleftSign : 0 ≤ q.eval (-16) := by
    have hsign :=
      eval_sign_left_of_all_roots_of_leadingCoeff_pos
        hqsplit hqlead (-16) (by
          intro y hy
          exact (hqbounds y hy).1.le)
    norm_num [hqdegree] at hsign
    exact hsign
  have hrightSign : 0 ≤ q.eval 16 :=
    eval_nonneg_right_of_all_roots_of_leadingCoeff_pos
      hqsplit hqlead 16 (by
        intro y hy
        exact (hqbounds y hy).2.le)
  apply mem_quarticTranslationCandidates_of_signs
    entry.baseCoefficients (-16) 16 entry.firstRoot entry.secondRoot
    entry.thirdRoot
    (by
      have hforall := (List.forall_iff_forall_mem.mp
        hvalid.2.2.2.2.1) entry.firstRoot
        (by simp [DegreeSevenStageFourEntry.rootIntervals])
      exact hforall.1.le)
    (by
      have hforall := (List.forall_iff_forall_mem.mp
        hvalid.2.2.2.2.1) entry.secondRoot
        (by simp [DegreeSevenStageFourEntry.rootIntervals])
      exact hforall.1.le)
    (by
      have hforall := (List.forall_iff_forall_mem.mp
        hvalid.2.2.2.2.1) entry.thirdRoot
        (by simp [DegreeSevenStageFourEntry.rootIntervals])
      exact hforall.1.le)
    (voightSortedRoot r hrsplit i0)
    (voightSortedRoot r hrsplit i1)
    (voightSortedRoot r hrsplit i2)
    hfirstMem hsecondMem hthirdMem (f.coeff 3)
  · simpa [q, DegreeSevenStageFourEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval] using hleftSign
  · simpa [q, DegreeSevenStageFourEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hfirstSign
  · simpa [q, DegreeSevenStageFourEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hsecondSign
  · simpa [q, DegreeSevenStageFourEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hthirdSign
  · simpa [q, DegreeSevenStageFourEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hrightSign

/-- Complete second recursion frontier: every sharpened Hunter septic has a
generated cubic row and its actual `a3` is one of that row's certified values. -/
theorem degreeSeven_minimumHunterCandidate_stageFour_frontier_complete
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f) :
    ∃ entry ∈ degreeSevenStageFourEntries,
      entry.a6 = f.coeff 6 ∧ entry.a5 = f.coeff 5 ∧
        entry.a4 = f.coeff 4 ∧ f.coeff 3 ∈ entry.a3Candidates := by
  obtain ⟨entry, hentry, ha6, ha5, ha4⟩ :=
    degreeSeven_minimumHunterCandidate_stageFour_complete h
  exact ⟨entry, hentry, ha6, ha5, ha4,
    degreeSeven_minimumHunterCandidate_a3_mem
      h entry hentry ha6 ha5 ha4⟩

end

end TraceEuclidean
