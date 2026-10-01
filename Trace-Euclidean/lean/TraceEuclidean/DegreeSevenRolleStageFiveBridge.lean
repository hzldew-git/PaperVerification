import TraceEuclidean.DegreeSevenRolleStageFourCompleteness
import TraceEuclidean.DegreeSevenRolleStageFiveBase
import TraceEuclidean.DegreeSevenLagrangeRootBound

/-!
# Mathematical bridge for the fifth Rolle stage in degree seven

This module proves the part independent of the generated finite table: any
valid rational isolation of the quartic third-derivative stage forces the
actual next coefficient `a2` into the exact quintic translation interval.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

/-- The normalized second derivative of a monic septic is the quintic used at
the fifth coefficient-pruning step. -/
theorem degreeSeven_secondDerivativeStage_eq
    {f : ℤ[X]} (hmonic : f.Monic) (hdegree : f.natDegree = 7) :
    voightDerivativeStage (f.map (algebraMap ℤ ℝ)) 2 =
      integerPolynomialReal
        [f.coeff 2, 3 * f.coeff 3, 6 * f.coeff 4,
          10 * f.coeff 5, 15 * f.coeff 6, 21] := by
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
    norm_num
  by_cases hm5 : m = 5
  · subst m
    have hcoeff : f.coeff 7 = 1 := by
      rw [← hdegree]
      exact hmonic.coeff_natDegree
    norm_num [hcoeff]
  have hm6 : 6 ≤ m := by omega
  have hright :
      [f.coeff 2, 3 * f.coeff 3, 6 * f.coeff 4,
        10 * f.coeff 5, 15 * f.coeff 6, 21].getD m 0 = 0 := by
    rw [List.getD_eq_default]
    simp
    omega
  rw [hright, map_zero]
  have hcoeff : f.coeff (m + 2) = 0 := by
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    rw [hdegree]
    omega
  rw [hcoeff, map_zero]
  ring

/-- The derivative of the quintic second-derivative stage is three times its
quartic third-derivative stage. -/
theorem degreeSeven_quintic_derivative_eq
    (a2 a3 a4 a5 a6 : ℤ) :
    (integerPolynomialReal
      [a2, 3 * a3, 6 * a4, 10 * a5, 15 * a6, 21]).derivative =
      C 3 * integerPolynomialReal
        [a3, 4 * a4, 10 * a5, 20 * a6, 35] := by
  rw [integerPolynomialReal_derivative]
  ext n
  rw [integerPolynomialReal, Polynomial.coeff_map,
    DensePolynomial.coeff_toPolynomial]
  rw [Polynomial.coeff_C_mul,
    integerPolynomialReal, Polynomial.coeff_map,
    DensePolynomial.coeff_toPolynomial]
  by_cases hn : n ≤ 5
  · interval_cases n <;>
      norm_num [DensePolynomial.derivative,
        DensePolynomial.add] <;> ring
  · have hn' : 6 ≤ n := by omega
    rw [List.getD_eq_default, List.getD_eq_default]
    all_goals norm_num [DensePolynomial.derivative,
      DensePolynomial.add] at *
    all_goals omega

/-- A valid quartic root certificate for the actual top four coefficients of
a sharpened septic forces its coefficient `a2` into the exact candidate set. -/
theorem degreeSeven_minimumHunterCandidate_a2_mem_of_valid
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (entry : DegreeSevenStageFiveEntry)
    (hvalid : entry.Valid)
    (ha6 : entry.a6 = f.coeff 6)
    (ha5 : entry.a5 = f.coeff 5)
    (ha4 : entry.a4 = f.coeff 4)
    (ha3 : entry.a3 = f.coeff 3) :
    f.coeff 2 ∈ entry.a2Candidates := by
  let p : ℝ[X] := f.map (algebraMap ℤ ℝ)
  let q : ℝ[X] := integerPolynomialReal
    [f.coeff 2, 3 * entry.a3, 6 * entry.a4,
      10 * entry.a5, 15 * entry.a6, 21]
  let r : ℝ[X] := integerPolynomialReal entry.derivativeCoefficients
  have hpdegree : p.natDegree = 7 := by
    dsimp [p]
    rw [Polynomial.natDegree_map_eq_of_injective
      (Int.cast_injective : Function.Injective (algebraMap ℤ ℝ)),
      h.2.2.1]
  have hpseparable : p.Separable := by
    simpa [p] using hunterPolynomialCandidate_separable_real_general h
  have hqEq : q = voightDerivativeStage p 2 := by
    symm
    simpa [p, q, ha6, ha5, ha4, ha3] using
      degreeSeven_secondDerivativeStage_eq h.1 h.2.2.1
  have hqsplit : q.Splits := by
    rw [hqEq]
    exact voightDerivativeStage_splits h.2.2.2.1 2
  have hqseparable : q.Separable := by
    rw [hqEq]
    exact voightDerivativeStage_separable h.2.2.2.1 hpseparable
      (by rw [hpdegree]; norm_num)
  have hqdegree : q.natDegree = 5 := by
    apply integerPolynomial_natDegree_of_generalRootIntervals
    · norm_num
    · norm_num
  have hqlead : 0 < q.leadingCoeff := by
    rw [hqEq]
    exact voightDerivativeStage_leadingCoeff_pos
      (h.1.map (algebraMap ℤ ℝ))
      (by rw [hpdegree]; norm_num)
  have hqbounds : ∀ z ∈ q.roots,
      (entry.leftEndpoint : ℝ) < z ∧
        z < (entry.rightEndpoint : ℝ) := by
    rw [hqEq]
    apply voightDerivativeStage_roots_strict_bounds
      h.2.2.2.1 hpseparable
    · intro z hz
      have hbound :=
        degreeSeven_minimumHunterCandidate_root_lagrange_strict_bounds
          h z hz
      simpa [p, DegreeSevenStageFiveEntry.leftEndpoint,
        DegreeSevenStageFiveEntry.rightEndpoint, ha6] using hbound
    · rw [hpdegree]
      norm_num
  have hrsplit : r.Splits :=
    integerPolynomial_splits_of_generalRootIntervals hvalid
  have hrdegree : r.natDegree = 4 :=
    integerPolynomial_natDegree_of_generalRootIntervals
      hvalid.2.1 hvalid.2.2.1
  have hqderivEq : q.derivative = C 3 * r := by
    simpa [q, r,
      DegreeSevenStageFiveEntry.derivativeCoefficients] using
      degreeSeven_quintic_derivative_eq
        (f.coeff 2) entry.a3 entry.a4 entry.a5 entry.a6
  let i0 : Fin r.natDegree := ⟨0, by rw [hrdegree]; norm_num⟩
  let i1 : Fin r.natDegree := ⟨1, by rw [hrdegree]; norm_num⟩
  let i2 : Fin r.natDegree := ⟨2, by rw [hrdegree]; norm_num⟩
  let i3 : Fin r.natDegree := ⟨3, by rw [hrdegree]; norm_num⟩
  let qi0 : Fin q.derivative.natDegree :=
    ⟨i0, by
      rw [hqderivEq, Polynomial.natDegree_C_mul
        (by norm_num : (3 : ℝ) ≠ 0)]
      exact i0.isLt⟩
  let qi1 : Fin q.derivative.natDegree :=
    ⟨i1, by
      rw [hqderivEq, Polynomial.natDegree_C_mul
        (by norm_num : (3 : ℝ) ≠ 0)]
      exact i1.isLt⟩
  let qi2 : Fin q.derivative.natDegree :=
    ⟨i2, by
      rw [hqderivEq, Polynomial.natDegree_C_mul
        (by norm_num : (3 : ℝ) ≠ 0)]
      exact i2.isLt⟩
  let qi3 : Fin q.derivative.natDegree :=
    ⟨i3, by
      rw [hqderivEq, Polynomial.natDegree_C_mul
        (by norm_num : (3 : ℝ) ≠ 0)]
      exact i3.isLt⟩
  have hrootEq0 :
      voightSortedRoot q.derivative
          (splits_derivative_of_splits_real hqsplit) qi0 =
        voightSortedRoot r hrsplit i0 := by
    simpa [qi0] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (3 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hqsplit)
        hrsplit hqderivEq i0
  have hrootEq1 :
      voightSortedRoot q.derivative
          (splits_derivative_of_splits_real hqsplit) qi1 =
        voightSortedRoot r hrsplit i1 := by
    simpa [qi1] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (3 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hqsplit)
        hrsplit hqderivEq i1
  have hrootEq2 :
      voightSortedRoot q.derivative
          (splits_derivative_of_splits_real hqsplit) qi2 =
        voightSortedRoot r hrsplit i2 := by
    simpa [qi2] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (3 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hqsplit)
        hrsplit hqderivEq i2
  have hrootEq3 :
      voightSortedRoot q.derivative
          (splits_derivative_of_splits_real hqsplit) qi3 =
        voightSortedRoot r hrsplit i3 := by
    simpa [qi3] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (3 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hqsplit)
        hrsplit hqderivEq i3
  let firstIndex : Fin entry.rootIntervals.length :=
    ⟨0, by simp [DegreeSevenStageFiveEntry.rootIntervals]⟩
  let secondIndex : Fin entry.rootIntervals.length :=
    ⟨1, by simp [DegreeSevenStageFiveEntry.rootIntervals]⟩
  let thirdIndex : Fin entry.rootIntervals.length :=
    ⟨2, by simp [DegreeSevenStageFiveEntry.rootIntervals]⟩
  let fourthIndex : Fin entry.rootIntervals.length :=
    ⟨3, by simp [DegreeSevenStageFiveEntry.rootIntervals]⟩
  have hfirstMem : voightSortedRoot r hrsplit i0 ∈
      Set.Icc (entry.firstRoot.lower : ℝ)
        (entry.firstRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid firstIndex
    simpa [r, i0, firstIndex,
      DegreeSevenStageFiveEntry.rootIntervals] using hmem
  have hsecondMem : voightSortedRoot r hrsplit i1 ∈
      Set.Icc (entry.secondRoot.lower : ℝ)
        (entry.secondRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid secondIndex
    simpa [r, i1, secondIndex,
      DegreeSevenStageFiveEntry.rootIntervals] using hmem
  have hthirdMem : voightSortedRoot r hrsplit i2 ∈
      Set.Icc (entry.thirdRoot.lower : ℝ)
        (entry.thirdRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid thirdIndex
    simpa [r, i2, thirdIndex,
      DegreeSevenStageFiveEntry.rootIntervals] using hmem
  have hfourthMem : voightSortedRoot r hrsplit i3 ∈
      Set.Icc (entry.fourthRoot.lower : ℝ)
        (entry.fourthRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid fourthIndex
    simpa [r, i3, fourthIndex,
      DegreeSevenStageFiveEntry.rootIntervals] using hmem
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
  have hleftSign : q.eval (entry.leftEndpoint : ℝ) ≤ 0 := by
    have hsign :=
      eval_sign_left_of_all_roots_of_leadingCoeff_pos
        hqsplit hqlead (entry.leftEndpoint : ℝ) (by
          intro y hy
          exact (hqbounds y hy).1.le)
    norm_num [hqdegree] at hsign
    linarith
  have hrightSign : 0 ≤ q.eval (entry.rightEndpoint : ℝ) :=
    eval_nonneg_right_of_all_roots_of_leadingCoeff_pos
      hqsplit hqlead (entry.rightEndpoint : ℝ) (by
        intro y hy
        exact (hqbounds y hy).2.le)
  apply mem_quinticTranslationCandidates_of_signs
    entry.baseCoefficients entry.leftEndpoint entry.rightEndpoint
    entry.firstRoot entry.secondRoot entry.thirdRoot entry.fourthRoot
    (by
      have hforall := (List.forall_iff_forall_mem.mp
        hvalid.2.2.2.2.1) entry.firstRoot
        (by simp [DegreeSevenStageFiveEntry.rootIntervals])
      exact hforall.1.le)
    (by
      have hforall := (List.forall_iff_forall_mem.mp
        hvalid.2.2.2.2.1) entry.secondRoot
        (by simp [DegreeSevenStageFiveEntry.rootIntervals])
      exact hforall.1.le)
    (by
      have hforall := (List.forall_iff_forall_mem.mp
        hvalid.2.2.2.2.1) entry.thirdRoot
        (by simp [DegreeSevenStageFiveEntry.rootIntervals])
      exact hforall.1.le)
    (by
      have hforall := (List.forall_iff_forall_mem.mp
        hvalid.2.2.2.2.1) entry.fourthRoot
        (by simp [DegreeSevenStageFiveEntry.rootIntervals])
      exact hforall.1.le)
    (voightSortedRoot r hrsplit i0)
    (voightSortedRoot r hrsplit i1)
    (voightSortedRoot r hrsplit i2)
    (voightSortedRoot r hrsplit i3)
    hfirstMem hsecondMem hthirdMem hfourthMem (f.coeff 2)
  · simpa [q, DegreeSevenStageFiveEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hleftSign
  · simpa [q, DegreeSevenStageFiveEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hfirstSign
  · simpa [q, DegreeSevenStageFiveEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hsecondSign
  · simpa [q, DegreeSevenStageFiveEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hthirdSign
  · simpa [q, DegreeSevenStageFiveEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hfourthSign
  · simpa [q, DegreeSevenStageFiveEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hrightSign

end

end TraceEuclidean
