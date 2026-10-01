import TraceEuclidean.DegreeFiveRolleStageFourCompleteness
import TraceEuclidean.DegreeFiveRolleStageFive

/-!
# Completeness of the final Rolle stage for degree five

This module connects every fourth-stage coefficient interval to the generated
quartic root certificates, rejects the multiple-root cases inside Lean, and
places the constant coefficient of every sharpened Hunter quintic in the
final finite frontier.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

/-- Exact rational evaluation agrees with real evaluation at an integral
argument. -/
theorem integerPolynomial_eval_intCast
    (coefficients : List ℤ) (x : ℤ) :
    (integerPolynomialReal coefficients).eval (x : ℝ) =
      (integerPolynomialRationalEval coefficients (x : ℚ) : ℝ) := by
  rw [integerPolynomialReal, ← DensePolynomial.toPolynomial_map]
  rw [DensePolynomial.eval_toPolynomial]
  change DensePolynomial.eval
      (coefficients.map (Int.castRingHom ℝ)) (x : ℝ) = _
  rw [show coefficients.map (Int.castRingHom ℝ) =
      (coefficients.map (Int.castRingHom ℚ)).map
        (algebraMap ℚ ℝ) by simp]
  have hx : (x : ℝ) = algebraMap ℚ ℝ (x : ℚ) := by
    norm_num
  rw [hx]
  change DensePolynomial.eval
      ((coefficients.map (Int.castRingHom ℚ)).map
        (algebraMap ℚ ℝ)) (algebraMap ℚ ℝ (x : ℚ)) =
    algebraMap ℚ ℝ
      (integerPolynomialRationalEval coefficients (x : ℚ))
  unfold integerPolynomialRationalEval
  exact DensePolynomial.eval_map (algebraMap ℚ ℝ)
    (coefficients.map (Int.castRingHom ℚ)) (x : ℚ)

/-- A fourth-stage row and one of its certified `a1` values are classified
by one generated coverage record. -/
theorem degreeFiveStageFour_candidate_classified
    (entry : DegreeFiveStageFourEntry)
    (hentry : entry ∈ degreeFiveStageFourEntries)
    {a1 : ℤ} (ha1 : a1 ∈ entry.a1Candidates) :
    ∃ coverage ∈ degreeFiveStageFiveCoverages,
      coverage.a4 = entry.a4 ∧
      coverage.a3 = entry.a3 ∧
      coverage.a2 = entry.a2 ∧
      (a1 ∈ coverage.survivingA1 ∨
        ∃ root, (a1, root) ∈ coverage.rejectedA1Roots) := by
  have hrange :
      (entry.a4, entry.a3, entry.a2,
        quarticTranslationLowerBound entry.baseCoefficients
          (-10) 10 entry.secondRoot,
        quarticTranslationUpperBound entry.baseCoefficients
          entry.firstRoot entry.thirdRoot) ∈
        degreeFiveStageFourExpectedRanges := by
    rw [← degreeFiveStageFourRanges_checked]
    exact List.mem_map_of_mem hentry
  rw [← degreeFiveStageFiveCoverageRanges_checked] at hrange
  obtain ⟨coverage, hcoverage, hrangeEq⟩ := List.mem_map.mp hrange
  have hcoverageValid : coverage.Valid :=
    (List.forall_iff_forall_mem.mp
      degreeFiveStageFiveCoverages_valid) coverage hcoverage
  have ha1Bounds :
      quarticTranslationLowerBound entry.baseCoefficients
          (-10) 10 entry.secondRoot ≤ a1 ∧
        a1 ≤ quarticTranslationUpperBound entry.baseCoefficients
          entry.firstRoot entry.thirdRoot := by
    simpa [DegreeFiveStageFourEntry.a1Candidates,
      quarticTranslationCandidates, integerIcc] using ha1
  have hcomponents :
      coverage.a4 = entry.a4 ∧
      coverage.a3 = entry.a3 ∧
      coverage.a2 = entry.a2 ∧
      coverage.lower =
        quarticTranslationLowerBound entry.baseCoefficients
          (-10) 10 entry.secondRoot ∧
      coverage.upper =
        quarticTranslationUpperBound entry.baseCoefficients
          entry.firstRoot entry.thirdRoot := by
    simpa [DegreeFiveStageFiveCoverage.rangeRecord,
      Prod.mk.injEq] using hrangeEq
  rcases hcomponents with ⟨ha4, ha3, ha2, hlower, hupper⟩
  have ha1Coverage :
      a1 ∈ integerIcc coverage.lower coverage.upper := by
    rw [integerIcc, Finset.mem_Icc, hlower, hupper]
    exact ha1Bounds
  rw [hcoverageValid] at ha1Coverage
  have ha1List :
      a1 ∈ coverage.survivingA1 ++
        coverage.rejectedA1Roots.map Prod.fst :=
    List.mem_toFinset.mp ha1Coverage
  rw [List.mem_append] at ha1List
  refine ⟨coverage, hcoverage, ha4, ha3, ha2, ?_⟩
  rcases ha1List with hsurviving | hrejected
  · exact Or.inl hsurviving
  · obtain ⟨pair, hpair, hpairFirst⟩ := List.mem_map.mp hrejected
    rcases pair with ⟨candidate, root⟩
    simp only at hpairFirst
    subst candidate
    exact Or.inr ⟨root, hpair⟩

/-- Every recorded multiple-root exception really is nonseparable over the
reals. -/
theorem degreeFive_rejectedCoverage_not_separable
    (coverage : DegreeFiveStageFiveCoverage)
    (hcoverage : coverage ∈ degreeFiveStageFiveCoverages)
    {a1 root : ℤ}
    (hrejected : (a1, root) ∈ coverage.rejectedA1Roots) :
    ¬(integerPolynomialReal
      [a1, 2 * coverage.a2, 3 * coverage.a3,
        4 * coverage.a4, 5]).Separable := by
  let witness : DegreeFiveRejectedQuarticWitness :=
    ⟨coverage.a4, coverage.a3, coverage.a2, a1, root⟩
  have hwitnessCoverage :
      witness ∈ coverage.rejectedWitnesses := by
    exact List.mem_map.mpr ⟨(a1, root), hrejected, rfl⟩
  have hwitness :
      witness ∈ degreeFiveStageFiveRejectedWitnesses := by
    exact List.mem_flatMap.mpr
      ⟨coverage, hcoverage, hwitnessCoverage⟩
  have hvalues := (List.forall_iff_forall_mem.mp
    degreeFiveStageFiveRejectedWitnesses_valid) witness hwitness
  have hquartic :
      (integerPolynomialReal
        [a1, 2 * coverage.a2, 3 * coverage.a3,
          4 * coverage.a4, 5]).eval (root : ℝ) = 0 := by
    rw [integerPolynomial_eval_intCast]
    simp only [witness] at hvalues
    rw [hvalues.1]
    norm_num
  have hcubic :
      (integerPolynomialReal
        [coverage.a2, 3 * coverage.a3,
          6 * coverage.a4, 10]).eval (root : ℝ) = 0 := by
    rw [integerPolynomial_eval_intCast]
    simp only [witness] at hvalues
    rw [hvalues.2]
    norm_num
  apply not_separable_of_common_real_root hquartic
  rw [degreeFive_quartic_derivative_eq]
  simp [hcubic]

/-- Every separable fourth-stage candidate reaches one of the 864 generated
quartic rows. -/
theorem degreeFiveStageFive_exists_entry
    (parent : DegreeFiveStageFourEntry)
    (hparent : parent ∈ degreeFiveStageFourEntries)
    {a1 : ℤ} (ha1 : a1 ∈ parent.a1Candidates)
    (hseparable :
      (integerPolynomialReal
        [a1, 2 * parent.a2, 3 * parent.a3,
          4 * parent.a4, 5]).Separable) :
    ∃ entry ∈ degreeFiveStageFiveEntries,
      entry.a4 = parent.a4 ∧
      entry.a3 = parent.a3 ∧
      entry.a2 = parent.a2 ∧
      entry.a1 = a1 := by
  obtain ⟨coverage, hcoverage, ha4, ha3, ha2,
      hclassification⟩ :=
    degreeFiveStageFour_candidate_classified parent hparent ha1
  rcases hclassification with hsurviving | hrejected
  · have htop :
        (coverage.a4, coverage.a3, coverage.a2, a1) ∈
          degreeFiveStageFiveTopQuadruples := by
      rw [degreeFiveStageFiveTopQuadruples]
      exact List.mem_flatMap.mpr
        ⟨coverage, hcoverage,
          List.mem_map.mpr ⟨a1, hsurviving, rfl⟩⟩
    rw [← degreeFiveStageFiveTopQuadruples_checked] at htop
    obtain ⟨entry, hentry, hkey⟩ := List.mem_map.mp htop
    have hcomponents :
        entry.a4 = coverage.a4 ∧
        entry.a3 = coverage.a3 ∧
        entry.a2 = coverage.a2 ∧
        entry.a1 = a1 := by
      simpa [Prod.mk.injEq] using hkey
    rcases hcomponents with ⟨he4, he3, he2, he1⟩
    exact ⟨entry, hentry, he4.trans ha4, he3.trans ha3,
      he2.trans ha2, he1⟩
  · obtain ⟨root, hroot⟩ := hrejected
    have hnot := degreeFive_rejectedCoverage_not_separable
      coverage hcoverage hroot
    apply (hnot ?_).elim
    simpa [ha4, ha3, ha2] using hseparable

/-- Every sharpened quintic Hunter candidate reaches a certified quartic row
whose four stored coefficients are its actual nonconstant coefficients. -/
theorem degreeFive_minimumHunterCandidate_stageFive_complete
    {f : ℤ[X]} (h : HunterPolynomialCandidate 5 67 f) :
    ∃ entry ∈ degreeFiveStageFiveEntries,
      entry.a4 = f.coeff 4 ∧
      entry.a3 = f.coeff 3 ∧
      entry.a2 = f.coeff 2 ∧
      entry.a1 = f.coeff 1 := by
  obtain ⟨parent, hparent, ha4, ha3, ha2, ha1⟩ :=
    degreeFive_minimumHunterCandidate_stageFour_frontier_complete h
  let p : ℝ[X] := f.map (algebraMap ℤ ℝ)
  let q : ℝ[X] := integerPolynomialReal
    [f.coeff 1, 2 * parent.a2, 3 * parent.a3,
      4 * parent.a4, 5]
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
  have hqseparable : q.Separable := by
    rw [hqEq]
    exact voightDerivativeStage_separable h.2.2.2.1 hpseparable
      (by rw [hpdegree]; norm_num)
  obtain ⟨entry, hentry, he4, he3, he2, he1⟩ :=
    degreeFiveStageFive_exists_entry parent hparent ha1 hqseparable
  exact ⟨entry, hentry, he4.trans ha4, he3.trans ha3,
    he2.trans ha2, he1⟩

/-- A monic quintic is exactly its six-term dense coefficient expansion after
mapping to the reals. -/
theorem degreeFive_realPolynomial_eq_dense
    {f : ℤ[X]} (hmonic : f.Monic) (hdegree : f.natDegree = 5) :
    f.map (algebraMap ℤ ℝ) =
      integerPolynomialReal
        [f.coeff 0, f.coeff 1, f.coeff 2,
          f.coeff 3, f.coeff 4, 1] := by
  ext m
  rw [Polynomial.coeff_map]
  rw [integerPolynomialReal, Polynomial.coeff_map]
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
    norm_num
  by_cases hm5 : m = 5
  · subst m
    have hcoeff : f.coeff 5 = 1 := by
      rw [← hdegree]
      exact hmonic.coeff_natDegree
    norm_num [hcoeff]
  have hm6 : 6 ≤ m := by omega
  have hright :
      [f.coeff 0, f.coeff 1, f.coeff 2,
        f.coeff 3, f.coeff 4, 1].getD m 0 = 0 := by
    rw [List.getD_eq_default]
    simp
    omega
  rw [hright, map_zero]
  have hcoeff : f.coeff m = 0 := by
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    rw [hdegree]
    omega
  rw [hcoeff, map_zero]

/-- Once a certified quartic row is identified, the constant coefficient of
the Hunter quintic belongs to its exact kernel-checked interval. -/
theorem degreeFive_minimumHunterCandidate_a0_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 5 67 f)
    (entry : DegreeFiveStageFiveEntry)
    (hentry : entry ∈ degreeFiveStageFiveEntries)
    (ha4 : entry.a4 = f.coeff 4)
    (ha3 : entry.a3 = f.coeff 3)
    (ha2 : entry.a2 = f.coeff 2)
    (ha1 : entry.a1 = f.coeff 1) :
    f.coeff 0 ∈ entry.a0Candidates := by
  have hvalid : entry.Valid :=
    (List.forall_iff_forall_mem.mp
      degreeFiveStageFiveEntries_valid) entry hentry
  let q : ℝ[X] := integerPolynomialReal
    [f.coeff 0, entry.a1, entry.a2, entry.a3, entry.a4, 1]
  let r : ℝ[X] :=
    integerPolynomialReal entry.derivativeCoefficients
  have hqEq : q = f.map (algebraMap ℤ ℝ) := by
    simpa [q, ha4, ha3, ha2, ha1] using
      (degreeFive_realPolynomial_eq_dense h.1 h.2.2.1).symm
  have hqdegree : q.natDegree = 5 := by
    rw [hqEq, Polynomial.natDegree_map_eq_of_injective
      (Int.cast_injective : Function.Injective (algebraMap ℤ ℝ)),
      h.2.2.1]
  have hqsplit : q.Splits := by
    rw [hqEq]
    exact h.2.2.2.1
  have hqseparable : q.Separable := by
    rw [hqEq]
    exact hunterPolynomialCandidate_separable_real h
  have hqmonic : q.Monic := by
    rw [hqEq]
    exact h.1.map (algebraMap ℤ ℝ)
  have hqlead : 0 < q.leadingCoeff := by
    rw [hqmonic.leadingCoeff]
    norm_num
  have hqbounds : ∀ z ∈ q.roots, (-10 : ℝ) < z ∧ z < 10 := by
    rw [hqEq]
    simpa using degreeFive_minimumHunterCandidate_root_bounds h
  have hrsplit : r.Splits :=
    integerPolynomial_splits_of_generalRootIntervals hvalid
  have hrdegree : r.natDegree = 4 :=
    integerPolynomial_natDegree_of_generalRootIntervals
      hvalid.2.1 hvalid.2.2.1
  have hqderivEq : q.derivative = r := by
    calc
      q.derivative = (f.map (algebraMap ℤ ℝ)).derivative := by
        rw [hqEq]
      _ = voightDerivativeStage
          (f.map (algebraMap ℤ ℝ)) 1 := by
        simp [voightDerivativeStage]
      _ = r := by
        simpa [r, DegreeFiveStageFiveEntry.derivativeCoefficients,
          ha4, ha3, ha2, ha1] using
          degreeFive_firstDerivativeStage_eq h.1 h.2.2.1
  have hqderivEqC : q.derivative = C 1 * r := by
    simpa using hqderivEq
  let i0 : Fin r.natDegree := ⟨0, by rw [hrdegree]; norm_num⟩
  let i1 : Fin r.natDegree := ⟨1, by rw [hrdegree]; norm_num⟩
  let i2 : Fin r.natDegree := ⟨2, by rw [hrdegree]; norm_num⟩
  let i3 : Fin r.natDegree := ⟨3, by rw [hrdegree]; norm_num⟩
  let qi0 : Fin q.derivative.natDegree :=
    ⟨i0, by
      rw [hqderivEqC, Polynomial.natDegree_C_mul
        (by norm_num : (1 : ℝ) ≠ 0)]
      exact i0.isLt⟩
  let qi1 : Fin q.derivative.natDegree :=
    ⟨i1, by
      rw [hqderivEqC, Polynomial.natDegree_C_mul
        (by norm_num : (1 : ℝ) ≠ 0)]
      exact i1.isLt⟩
  let qi2 : Fin q.derivative.natDegree :=
    ⟨i2, by
      rw [hqderivEqC, Polynomial.natDegree_C_mul
        (by norm_num : (1 : ℝ) ≠ 0)]
      exact i2.isLt⟩
  let qi3 : Fin q.derivative.natDegree :=
    ⟨i3, by
      rw [hqderivEqC, Polynomial.natDegree_C_mul
        (by norm_num : (1 : ℝ) ≠ 0)]
      exact i3.isLt⟩
  have hrootEq0 :
      voightSortedRoot q.derivative
          (splits_derivative_of_splits_real hqsplit) qi0 =
        voightSortedRoot r hrsplit i0 := by
    simpa [qi0] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (1 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hqsplit)
        hrsplit hqderivEqC i0
  have hrootEq1 :
      voightSortedRoot q.derivative
          (splits_derivative_of_splits_real hqsplit) qi1 =
        voightSortedRoot r hrsplit i1 := by
    simpa [qi1] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (1 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hqsplit)
        hrsplit hqderivEqC i1
  have hrootEq2 :
      voightSortedRoot q.derivative
          (splits_derivative_of_splits_real hqsplit) qi2 =
        voightSortedRoot r hrsplit i2 := by
    simpa [qi2] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (1 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hqsplit)
        hrsplit hqderivEqC i2
  have hrootEq3 :
      voightSortedRoot q.derivative
          (splits_derivative_of_splits_real hqsplit) qi3 =
        voightSortedRoot r hrsplit i3 := by
    simpa [qi3] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (1 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hqsplit)
        hrsplit hqderivEqC i3
  let firstIndex : Fin entry.rootIntervals.length :=
    ⟨0, by simp [DegreeFiveStageFiveEntry.rootIntervals]⟩
  let secondIndex : Fin entry.rootIntervals.length :=
    ⟨1, by simp [DegreeFiveStageFiveEntry.rootIntervals]⟩
  let thirdIndex : Fin entry.rootIntervals.length :=
    ⟨2, by simp [DegreeFiveStageFiveEntry.rootIntervals]⟩
  let fourthIndex : Fin entry.rootIntervals.length :=
    ⟨3, by simp [DegreeFiveStageFiveEntry.rootIntervals]⟩
  have hfirstMem : voightSortedRoot r hrsplit i0 ∈
      Set.Icc (entry.firstRoot.lower : ℝ)
        (entry.firstRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid firstIndex
    simpa [r, i0, firstIndex,
      DegreeFiveStageFiveEntry.rootIntervals] using hmem
  have hsecondMem : voightSortedRoot r hrsplit i1 ∈
      Set.Icc (entry.secondRoot.lower : ℝ)
        (entry.secondRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid secondIndex
    simpa [r, i1, secondIndex,
      DegreeFiveStageFiveEntry.rootIntervals] using hmem
  have hthirdMem : voightSortedRoot r hrsplit i2 ∈
      Set.Icc (entry.thirdRoot.lower : ℝ)
        (entry.thirdRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid thirdIndex
    simpa [r, i2, thirdIndex,
      DegreeFiveStageFiveEntry.rootIntervals] using hmem
  have hfourthMem : voightSortedRoot r hrsplit i3 ∈
      Set.Icc (entry.fourthRoot.lower : ℝ)
        (entry.fourthRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid fourthIndex
    simpa [r, i3, fourthIndex,
      DegreeFiveStageFiveEntry.rootIntervals] using hmem
  have hfirstSign :
      0 ≤ q.eval (voightSortedRoot r hrsplit i0) := by
    have hsign :=
      eval_sign_at_derivativeSortedRoot_of_leadingCoeff_pos
        hqsplit hqlead hqseparable qi0
    rw [hrootEq0] at hsign
    norm_num [hqdegree, qi0, i0] at hsign
    exact hsign
  have hsecondSign :
      q.eval (voightSortedRoot r hrsplit i1) ≤ 0 := by
    have hsign :=
      eval_sign_at_derivativeSortedRoot_of_leadingCoeff_pos
        hqsplit hqlead hqseparable qi1
    rw [hrootEq1] at hsign
    norm_num [hqdegree, qi1, i1] at hsign
    linarith
  have hthirdSign :
      0 ≤ q.eval (voightSortedRoot r hrsplit i2) := by
    have hsign :=
      eval_sign_at_derivativeSortedRoot_of_leadingCoeff_pos
        hqsplit hqlead hqseparable qi2
    rw [hrootEq2] at hsign
    simpa [hqdegree, qi2, i2] using hsign
  have hfourthSign :
      q.eval (voightSortedRoot r hrsplit i3) ≤ 0 := by
    have hsign :=
      eval_sign_at_derivativeSortedRoot_of_leadingCoeff_pos
        hqsplit hqlead hqseparable qi3
    rw [hrootEq3] at hsign
    norm_num [hqdegree, qi3, i3] at hsign
    linarith
  have hleftSign : q.eval (-10) ≤ 0 := by
    have hsign :=
      eval_sign_left_of_all_roots_of_leadingCoeff_pos
        hqsplit hqlead (-10) (by
          intro y hy
          exact (hqbounds y hy).1.le)
    norm_num [hqdegree] at hsign
    linarith
  have hrightSign : 0 ≤ q.eval 10 :=
    eval_nonneg_right_of_all_roots_of_leadingCoeff_pos
      hqsplit hqlead 10 (by
        intro y hy
        exact (hqbounds y hy).2.le)
  apply mem_quinticTranslationCandidates_of_signs
    entry.baseCoefficients (-10) 10 entry.firstRoot entry.secondRoot
    entry.thirdRoot entry.fourthRoot
    (by
      have hforall := (List.forall_iff_forall_mem.mp
        hvalid.2.2.2.2.1) entry.firstRoot
        (by simp [DegreeFiveStageFiveEntry.rootIntervals])
      exact hforall.1.le)
    (by
      have hforall := (List.forall_iff_forall_mem.mp
        hvalid.2.2.2.2.1) entry.secondRoot
        (by simp [DegreeFiveStageFiveEntry.rootIntervals])
      exact hforall.1.le)
    (by
      have hforall := (List.forall_iff_forall_mem.mp
        hvalid.2.2.2.2.1) entry.thirdRoot
        (by simp [DegreeFiveStageFiveEntry.rootIntervals])
      exact hforall.1.le)
    (by
      have hforall := (List.forall_iff_forall_mem.mp
        hvalid.2.2.2.2.1) entry.fourthRoot
        (by simp [DegreeFiveStageFiveEntry.rootIntervals])
      exact hforall.1.le)
    (voightSortedRoot r hrsplit i0)
    (voightSortedRoot r hrsplit i1)
    (voightSortedRoot r hrsplit i2)
    (voightSortedRoot r hrsplit i3)
    hfirstMem hsecondMem hthirdMem hfourthMem (f.coeff 0)
  · simpa [q, DegreeFiveStageFiveEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval] using hleftSign
  · simpa [q, DegreeFiveStageFiveEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hfirstSign
  · simpa [q, DegreeFiveStageFiveEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hsecondSign
  · simpa [q, DegreeFiveStageFiveEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hthirdSign
  · simpa [q, DegreeFiveStageFiveEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hfourthSign
  · simpa [q, DegreeFiveStageFiveEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hrightSign

/-- Complete final recursion frontier: every sharpened Hunter quintic is one
of the 1,217 kernel-checked coefficient candidates. -/
theorem degreeFive_minimumHunterCandidate_stageFive_frontier_complete
    {f : ℤ[X]} (h : HunterPolynomialCandidate 5 67 f) :
    ∃ entry ∈ degreeFiveStageFiveEntries,
      entry.a4 = f.coeff 4 ∧
      entry.a3 = f.coeff 3 ∧
      entry.a2 = f.coeff 2 ∧
      entry.a1 = f.coeff 1 ∧
      f.coeff 0 ∈ entry.a0Candidates := by
  obtain ⟨entry, hentry, ha4, ha3, ha2, ha1⟩ :=
    degreeFive_minimumHunterCandidate_stageFive_complete h
  exact ⟨entry, hentry, ha4, ha3, ha2, ha1,
    degreeFive_minimumHunterCandidate_a0_mem
      h entry hentry ha4 ha3 ha2 ha1⟩

end

end TraceEuclidean
