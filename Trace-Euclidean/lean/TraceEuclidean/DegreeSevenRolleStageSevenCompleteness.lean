import TraceEuclidean.DegreeSevenRolleStageSevenScaled

/-!
# Mathematical bridge for the final degree-seven Rolle stage

A valid six-root certificate for the first derivative of a septic Hunter
candidate gives the alternating critical-point signs needed by the exact
translation bound.  Consequently the constant coefficient belongs to the
finite `a0` set computed from those six intervals.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

/-- Exact first-derivative root intervals force the constant coefficient of a
degree-seven Hunter candidate into the certified final finite set. -/
theorem degreeSeven_minimumHunterCandidate_a0_mem_of_stageSeven
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (entry : DegreeSevenStageSevenEntry)
    (hvalid : entry.Valid)
    (ha6 : entry.a6 = f.coeff 6)
    (ha5 : entry.a5 = f.coeff 5)
    (ha4 : entry.a4 = f.coeff 4)
    (ha3 : entry.a3 = f.coeff 3)
    (ha2 : entry.a2 = f.coeff 2)
    (ha1 : entry.a1 = f.coeff 1) :
    f.coeff 0 ∈ entry.a0Candidates := by
  let p : ℝ[X] := integerPolynomialReal
    [f.coeff 0, f.coeff 1, f.coeff 2, f.coeff 3,
      f.coeff 4, f.coeff 5, f.coeff 6, 1]
  let q : ℝ[X] :=
    integerPolynomialReal entry.derivativeCoefficients
  have hpEq : p = f.map (algebraMap ℤ ℝ) := by
    simpa [p] using (degreeSeven_realPolynomial_eq_dense
      h.1 h.2.2.1).symm
  have hpdegree : p.natDegree = 7 := by
    rw [hpEq, Polynomial.natDegree_map_eq_of_injective
      (Int.cast_injective : Function.Injective (algebraMap ℤ ℝ)),
      h.2.2.1]
  have hpsplit : p.Splits := by
    rw [hpEq]
    exact h.2.2.2.1
  have hpseparable : p.Separable := by
    rw [hpEq]
    exact hunterPolynomialCandidate_separable_real_general h
  have hpmonic : p.Monic := by
    rw [hpEq]
    exact h.1.map (algebraMap ℤ ℝ)
  have hplead : 0 < p.leadingCoeff := by
    rw [hpmonic.leadingCoeff]
    norm_num
  have hqStage : q =
      voightDerivativeStage (f.map (algebraMap ℤ ℝ)) 1 := by
    symm
    simpa [q, DegreeSevenStageSevenEntry.derivativeCoefficients,
      ha6, ha5, ha4, ha3, ha2, ha1] using
      degreeSeven_firstDerivativeStage_eq h.1 h.2.2.1
  have hqsplit : q.Splits := by
    simpa [q] using
      integerPolynomial_splits_of_generalRootIntervals hvalid
  have hqdegree : q.natDegree = 6 := by
    simpa [q] using
      integerPolynomial_natDegree_of_generalRootIntervals
        hvalid.2.1 hvalid.2.2.1
  have hpderivEq : p.derivative = q := by
    calc
      p.derivative = (f.map (algebraMap ℤ ℝ)).derivative := by
        rw [hpEq]
      _ = voightDerivativeStage
          (f.map (algebraMap ℤ ℝ)) 1 := by
        simp [voightDerivativeStage]
      _ = q := hqStage.symm
  have hpderivEqC : p.derivative = C 1 * q := by
    simpa using hpderivEq
  let i0 : Fin q.natDegree := ⟨0, by rw [hqdegree]; norm_num⟩
  let i1 : Fin q.natDegree := ⟨1, by rw [hqdegree]; norm_num⟩
  let i2 : Fin q.natDegree := ⟨2, by rw [hqdegree]; norm_num⟩
  let i3 : Fin q.natDegree := ⟨3, by rw [hqdegree]; norm_num⟩
  let i4 : Fin q.natDegree := ⟨4, by rw [hqdegree]; norm_num⟩
  let i5 : Fin q.natDegree := ⟨5, by rw [hqdegree]; norm_num⟩
  let pi0 : Fin p.derivative.natDegree :=
    ⟨i0, by
      rw [hpderivEqC, Polynomial.natDegree_C_mul
        (by norm_num : (1 : ℝ) ≠ 0)]
      exact i0.isLt⟩
  let pi1 : Fin p.derivative.natDegree :=
    ⟨i1, by
      rw [hpderivEqC, Polynomial.natDegree_C_mul
        (by norm_num : (1 : ℝ) ≠ 0)]
      exact i1.isLt⟩
  let pi2 : Fin p.derivative.natDegree :=
    ⟨i2, by
      rw [hpderivEqC, Polynomial.natDegree_C_mul
        (by norm_num : (1 : ℝ) ≠ 0)]
      exact i2.isLt⟩
  let pi3 : Fin p.derivative.natDegree :=
    ⟨i3, by
      rw [hpderivEqC, Polynomial.natDegree_C_mul
        (by norm_num : (1 : ℝ) ≠ 0)]
      exact i3.isLt⟩
  let pi4 : Fin p.derivative.natDegree :=
    ⟨i4, by
      rw [hpderivEqC, Polynomial.natDegree_C_mul
        (by norm_num : (1 : ℝ) ≠ 0)]
      exact i4.isLt⟩
  let pi5 : Fin p.derivative.natDegree :=
    ⟨i5, by
      rw [hpderivEqC, Polynomial.natDegree_C_mul
        (by norm_num : (1 : ℝ) ≠ 0)]
      exact i5.isLt⟩
  have hrootEq0 :
      voightSortedRoot p.derivative
          (splits_derivative_of_splits_real hpsplit) pi0 =
        voightSortedRoot q hqsplit i0 := by
    simpa [pi0] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (1 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hpsplit)
        hqsplit hpderivEqC i0
  have hrootEq1 :
      voightSortedRoot p.derivative
          (splits_derivative_of_splits_real hpsplit) pi1 =
        voightSortedRoot q hqsplit i1 := by
    simpa [pi1] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (1 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hpsplit)
        hqsplit hpderivEqC i1
  have hrootEq2 :
      voightSortedRoot p.derivative
          (splits_derivative_of_splits_real hpsplit) pi2 =
        voightSortedRoot q hqsplit i2 := by
    simpa [pi2] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (1 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hpsplit)
        hqsplit hpderivEqC i2
  have hrootEq3 :
      voightSortedRoot p.derivative
          (splits_derivative_of_splits_real hpsplit) pi3 =
        voightSortedRoot q hqsplit i3 := by
    simpa [pi3] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (1 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hpsplit)
        hqsplit hpderivEqC i3
  have hrootEq4 :
      voightSortedRoot p.derivative
          (splits_derivative_of_splits_real hpsplit) pi4 =
        voightSortedRoot q hqsplit i4 := by
    simpa [pi4] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (1 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hpsplit)
        hqsplit hpderivEqC i4
  have hrootEq5 :
      voightSortedRoot p.derivative
          (splits_derivative_of_splits_real hpsplit) pi5 =
        voightSortedRoot q hqsplit i5 := by
    simpa [pi5] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (1 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hpsplit)
        hqsplit hpderivEqC i5
  let c0Index : Fin entry.rootIntervals.length :=
    ⟨0, by simp [DegreeSevenStageSevenEntry.rootIntervals]⟩
  let c1Index : Fin entry.rootIntervals.length :=
    ⟨1, by simp [DegreeSevenStageSevenEntry.rootIntervals]⟩
  let c2Index : Fin entry.rootIntervals.length :=
    ⟨2, by simp [DegreeSevenStageSevenEntry.rootIntervals]⟩
  let c3Index : Fin entry.rootIntervals.length :=
    ⟨3, by simp [DegreeSevenStageSevenEntry.rootIntervals]⟩
  let c4Index : Fin entry.rootIntervals.length :=
    ⟨4, by simp [DegreeSevenStageSevenEntry.rootIntervals]⟩
  let c5Index : Fin entry.rootIntervals.length :=
    ⟨5, by simp [DegreeSevenStageSevenEntry.rootIntervals]⟩
  have hmem0 : voightSortedRoot q hqsplit i0 ∈
      Set.Icc (entry.firstRoot.lower : ℝ)
        (entry.firstRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid c0Index
    simpa [q, i0, c0Index,
      DegreeSevenStageSevenEntry.rootIntervals] using hmem
  have hmem1 : voightSortedRoot q hqsplit i1 ∈
      Set.Icc (entry.secondRoot.lower : ℝ)
        (entry.secondRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid c1Index
    simpa [q, i1, c1Index,
      DegreeSevenStageSevenEntry.rootIntervals] using hmem
  have hmem2 : voightSortedRoot q hqsplit i2 ∈
      Set.Icc (entry.thirdRoot.lower : ℝ)
        (entry.thirdRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid c2Index
    simpa [q, i2, c2Index,
      DegreeSevenStageSevenEntry.rootIntervals] using hmem
  have hmem3 : voightSortedRoot q hqsplit i3 ∈
      Set.Icc (entry.fourthRoot.lower : ℝ)
        (entry.fourthRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid c3Index
    simpa [q, i3, c3Index,
      DegreeSevenStageSevenEntry.rootIntervals] using hmem
  have hmem4 : voightSortedRoot q hqsplit i4 ∈
      Set.Icc (entry.fifthRoot.lower : ℝ)
        (entry.fifthRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid c4Index
    simpa [q, i4, c4Index,
      DegreeSevenStageSevenEntry.rootIntervals] using hmem
  have hmem5 : voightSortedRoot q hqsplit i5 ∈
      Set.Icc (entry.sixthRoot.lower : ℝ)
        (entry.sixthRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid c5Index
    simpa [q, i5, c5Index,
      DegreeSevenStageSevenEntry.rootIntervals] using hmem
  have hordered0 : entry.firstRoot.lower ≤ entry.firstRoot.upper := by
    exact_mod_cast hmem0.1.trans hmem0.2
  have hordered1 : entry.secondRoot.lower ≤ entry.secondRoot.upper := by
    exact_mod_cast hmem1.1.trans hmem1.2
  have hordered2 : entry.thirdRoot.lower ≤ entry.thirdRoot.upper := by
    exact_mod_cast hmem2.1.trans hmem2.2
  have hordered3 : entry.fourthRoot.lower ≤ entry.fourthRoot.upper := by
    exact_mod_cast hmem3.1.trans hmem3.2
  have hordered4 : entry.fifthRoot.lower ≤ entry.fifthRoot.upper := by
    exact_mod_cast hmem4.1.trans hmem4.2
  have hordered5 : entry.sixthRoot.lower ≤ entry.sixthRoot.upper := by
    exact_mod_cast hmem5.1.trans hmem5.2
  have hsign0 : 0 ≤ p.eval (voightSortedRoot q hqsplit i0) := by
    have hs := eval_sign_at_derivativeSortedRoot_of_leadingCoeff_pos
      hpsplit hplead hpseparable pi0
    rw [hrootEq0] at hs
    norm_num [hpdegree, pi0, i0] at hs
    exact hs
  have hsign1 : p.eval (voightSortedRoot q hqsplit i1) ≤ 0 := by
    have hs := eval_sign_at_derivativeSortedRoot_of_leadingCoeff_pos
      hpsplit hplead hpseparable pi1
    rw [hrootEq1] at hs
    norm_num [hpdegree, pi1, i1] at hs
    linarith
  have hsign2 : 0 ≤ p.eval (voightSortedRoot q hqsplit i2) := by
    have hs := eval_sign_at_derivativeSortedRoot_of_leadingCoeff_pos
      hpsplit hplead hpseparable pi2
    rw [hrootEq2] at hs
    norm_num [hpdegree, pi2, i2] at hs
    exact hs
  have hsign3 : p.eval (voightSortedRoot q hqsplit i3) ≤ 0 := by
    have hs := eval_sign_at_derivativeSortedRoot_of_leadingCoeff_pos
      hpsplit hplead hpseparable pi3
    rw [hrootEq3] at hs
    norm_num [hpdegree, pi3, i3] at hs
    linarith
  have hsign4 : 0 ≤ p.eval (voightSortedRoot q hqsplit i4) := by
    have hs := eval_sign_at_derivativeSortedRoot_of_leadingCoeff_pos
      hpsplit hplead hpseparable pi4
    rw [hrootEq4] at hs
    norm_num [hpdegree, pi4, i4] at hs
    exact hs
  have hsign5 : p.eval (voightSortedRoot q hqsplit i5) ≤ 0 := by
    have hs := eval_sign_at_derivativeSortedRoot_of_leadingCoeff_pos
      hpsplit hplead hpseparable pi5
    rw [hrootEq5] at hs
    norm_num [hpdegree, pi5, i5] at hs
    linarith
  have hleftSign : p.eval (entry.leftEndpoint : ℝ) ≤ 0 := by
    have hs := eval_sign_left_of_all_roots_of_leadingCoeff_pos
      hpsplit hplead (entry.leftEndpoint : ℝ) (by
        intro y hy
        rw [hpEq] at hy
        have hb :=
          (degreeSeven_minimumHunterCandidate_root_lagrange_strict_bounds
            h y hy).1.le
        simpa [DegreeSevenStageSevenEntry.leftEndpoint, ha6] using hb)
    norm_num [hpdegree] at hs
    linarith
  have hrightSign : 0 ≤ p.eval (entry.rightEndpoint : ℝ) := by
    apply eval_nonneg_right_of_all_roots_of_leadingCoeff_pos
      hpsplit hplead
    intro y hy
    rw [hpEq] at hy
    have hb :=
      (degreeSeven_minimumHunterCandidate_root_lagrange_strict_bounds
        h y hy).2.le
    simpa [DegreeSevenStageSevenEntry.rightEndpoint, ha6] using hb
  rw [DegreeSevenStageSevenEntry.a0Candidates]
  apply mem_septicTranslationCandidates_of_signs
    entry.baseCoefficients entry.leftEndpoint entry.rightEndpoint
    entry.firstRoot entry.secondRoot entry.thirdRoot entry.fourthRoot
    entry.fifthRoot entry.sixthRoot
    hordered0 hordered1 hordered2 hordered3 hordered4 hordered5
    (voightSortedRoot q hqsplit i0)
    (voightSortedRoot q hqsplit i1)
    (voightSortedRoot q hqsplit i2)
    (voightSortedRoot q hqsplit i3)
    (voightSortedRoot q hqsplit i4)
    (voightSortedRoot q hqsplit i5)
    hmem0 hmem1 hmem2 hmem3 hmem4 hmem5 (f.coeff 0)
  all_goals
    simp only [DegreeSevenStageSevenEntry.baseCoefficients]
  · simpa [p, integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval,
      ha6, ha5, ha4, ha3, ha2, ha1, add_comm] using hleftSign
  · simpa [p, integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval,
      ha6, ha5, ha4, ha3, ha2, ha1, add_comm] using hsign0
  · simpa [p, integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval,
      ha6, ha5, ha4, ha3, ha2, ha1, add_comm] using hsign1
  · simpa [p, integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval,
      ha6, ha5, ha4, ha3, ha2, ha1, add_comm] using hsign2
  · simpa [p, integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval,
      ha6, ha5, ha4, ha3, ha2, ha1, add_comm] using hsign3
  · simpa [p, integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval,
      ha6, ha5, ha4, ha3, ha2, ha1, add_comm] using hsign4
  · simpa [p, integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval,
      ha6, ha5, ha4, ha3, ha2, ha1, add_comm] using hsign5
  · simpa [p, integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval,
      ha6, ha5, ha4, ha3, ha2, ha1, add_comm] using hrightSign

end

end TraceEuclidean
