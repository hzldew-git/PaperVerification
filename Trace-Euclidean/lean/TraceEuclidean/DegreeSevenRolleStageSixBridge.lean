import TraceEuclidean.DegreeSevenRolleStageFiveCompleteness
import TraceEuclidean.DegreeSevenRolleStageSixBase

/-!
# Mathematical bridge for the sixth Rolle stage in degree seven

This module proves the part independent of the generated finite table: any
valid rational isolation of the quintic second-derivative stage forces the
actual next coefficient `a1` into the exact sextic translation interval.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

/-- The normalized first derivative of a monic septic is the sextic used at
the sixth coefficient-pruning step. -/
theorem degreeSeven_firstDerivativeStage_eq
    {f : ℤ[X]} (hmonic : f.Monic) (hdegree : f.natDegree = 7) :
    voightDerivativeStage (f.map (algebraMap ℤ ℝ)) 1 =
      integerPolynomialReal
        [f.coeff 1, 2 * f.coeff 2, 3 * f.coeff 3,
          4 * f.coeff 4, 5 * f.coeff 5, 6 * f.coeff 6, 7] := by
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
    norm_num
  by_cases hm6 : m = 6
  · subst m
    have hcoeff : f.coeff 7 = 1 := by
      rw [← hdegree]
      exact hmonic.coeff_natDegree
    norm_num [hcoeff]
  have hm7 : 7 ≤ m := by omega
  have hright :
      [f.coeff 1, 2 * f.coeff 2, 3 * f.coeff 3,
        4 * f.coeff 4, 5 * f.coeff 5, 6 * f.coeff 6, 7].getD m 0 = 0 := by
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

/-- The derivative of the sextic first-derivative stage is twice its quintic
second-derivative stage. -/
theorem degreeSeven_sextic_derivative_eq
    (a1 a2 a3 a4 a5 a6 : ℤ) :
    (integerPolynomialReal
      [a1, 2 * a2, 3 * a3, 4 * a4, 5 * a5, 6 * a6, 7]).derivative =
      C 2 * integerPolynomialReal
        [a2, 3 * a3, 6 * a4, 10 * a5, 15 * a6, 21] := by
  rw [integerPolynomialReal_derivative]
  ext n
  rw [integerPolynomialReal, Polynomial.coeff_map,
    DensePolynomial.coeff_toPolynomial]
  rw [Polynomial.coeff_C_mul,
    integerPolynomialReal, Polynomial.coeff_map,
    DensePolynomial.coeff_toPolynomial]
  by_cases hn : n ≤ 6
  · interval_cases n <;>
      norm_num [DensePolynomial.derivative,
        DensePolynomial.add] <;> ring
  · have hn' : 7 ≤ n := by omega
    rw [List.getD_eq_default, List.getD_eq_default]
    all_goals norm_num [DensePolynomial.derivative,
      DensePolynomial.add] at *
    all_goals omega

/-- A valid quintic root certificate for the actual top five coefficients of
a sharpened septic forces its coefficient `a1` into the exact candidate set. -/
theorem degreeSeven_minimumHunterCandidate_a1_mem_of_valid
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (entry : DegreeSevenStageSixEntry)
    (hvalid : entry.Valid)
    (ha6 : entry.a6 = f.coeff 6)
    (ha5 : entry.a5 = f.coeff 5)
    (ha4 : entry.a4 = f.coeff 4)
    (ha3 : entry.a3 = f.coeff 3)
    (ha2 : entry.a2 = f.coeff 2) :
    f.coeff 1 ∈ entry.a1Candidates := by
  let p : ℝ[X] := f.map (algebraMap ℤ ℝ)
  let q : ℝ[X] := integerPolynomialReal
    [f.coeff 1, 2 * entry.a2, 3 * entry.a3, 4 * entry.a4,
      5 * entry.a5, 6 * entry.a6, 7]
  let r : ℝ[X] := integerPolynomialReal entry.derivativeCoefficients
  have hpdegree : p.natDegree = 7 := by
    dsimp [p]
    rw [Polynomial.natDegree_map_eq_of_injective
      (Int.cast_injective : Function.Injective (algebraMap ℤ ℝ)),
      h.2.2.1]
  have hpseparable : p.Separable := by
    simpa [p] using hunterPolynomialCandidate_separable_real_general h
  have hqEq : q = voightDerivativeStage p 1 := by
    symm
    simpa [p, q, ha6, ha5, ha4, ha3, ha2] using
      degreeSeven_firstDerivativeStage_eq h.1 h.2.2.1
  have hqsplit : q.Splits := by
    rw [hqEq]
    exact voightDerivativeStage_splits h.2.2.2.1 1
  have hqseparable : q.Separable := by
    rw [hqEq]
    exact voightDerivativeStage_separable h.2.2.2.1 hpseparable
      (by rw [hpdegree]; norm_num)
  have hqdegree : q.natDegree = 6 := by
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
      simpa [p, DegreeSevenStageSixEntry.leftEndpoint,
        DegreeSevenStageSixEntry.rightEndpoint, ha6] using hbound
    · rw [hpdegree]
      norm_num
  have hrsplit : r.Splits :=
    integerPolynomial_splits_of_generalRootIntervals hvalid
  have hrdegree : r.natDegree = 5 :=
    integerPolynomial_natDegree_of_generalRootIntervals
      hvalid.2.1 hvalid.2.2.1
  have hqderivEq : q.derivative = C 2 * r := by
    simpa [q, r,
      DegreeSevenStageSixEntry.derivativeCoefficients] using
      degreeSeven_sextic_derivative_eq
        (f.coeff 1) entry.a2 entry.a3 entry.a4 entry.a5 entry.a6
  let i0 : Fin r.natDegree := ⟨0, by rw [hrdegree]; norm_num⟩
  let i1 : Fin r.natDegree := ⟨1, by rw [hrdegree]; norm_num⟩
  let i2 : Fin r.natDegree := ⟨2, by rw [hrdegree]; norm_num⟩
  let i3 : Fin r.natDegree := ⟨3, by rw [hrdegree]; norm_num⟩
  let i4 : Fin r.natDegree := ⟨4, by rw [hrdegree]; norm_num⟩
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
  let qi3 : Fin q.derivative.natDegree :=
    ⟨i3, by
      rw [hqderivEq, Polynomial.natDegree_C_mul
        (by norm_num : (2 : ℝ) ≠ 0)]
      exact i3.isLt⟩
  let qi4 : Fin q.derivative.natDegree :=
    ⟨i4, by
      rw [hqderivEq, Polynomial.natDegree_C_mul
        (by norm_num : (2 : ℝ) ≠ 0)]
      exact i4.isLt⟩
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
  have hrootEq3 :
      voightSortedRoot q.derivative
          (splits_derivative_of_splits_real hqsplit) qi3 =
        voightSortedRoot r hrsplit i3 := by
    simpa [qi3] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (2 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hqsplit)
        hrsplit hqderivEq i3
  have hrootEq4 :
      voightSortedRoot q.derivative
          (splits_derivative_of_splits_real hqsplit) qi4 =
        voightSortedRoot r hrsplit i4 := by
    simpa [qi4] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (2 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hqsplit)
        hrsplit hqderivEq i4
  let firstIndex : Fin entry.rootIntervals.length :=
    ⟨0, by simp [DegreeSevenStageSixEntry.rootIntervals]⟩
  let secondIndex : Fin entry.rootIntervals.length :=
    ⟨1, by simp [DegreeSevenStageSixEntry.rootIntervals]⟩
  let thirdIndex : Fin entry.rootIntervals.length :=
    ⟨2, by simp [DegreeSevenStageSixEntry.rootIntervals]⟩
  let fourthIndex : Fin entry.rootIntervals.length :=
    ⟨3, by simp [DegreeSevenStageSixEntry.rootIntervals]⟩
  let fifthIndex : Fin entry.rootIntervals.length :=
    ⟨4, by simp [DegreeSevenStageSixEntry.rootIntervals]⟩
  have hfirstMem : voightSortedRoot r hrsplit i0 ∈
      Set.Icc (entry.firstRoot.lower : ℝ)
        (entry.firstRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid firstIndex
    simpa [r, i0, firstIndex,
      DegreeSevenStageSixEntry.rootIntervals] using hmem
  have hsecondMem : voightSortedRoot r hrsplit i1 ∈
      Set.Icc (entry.secondRoot.lower : ℝ)
        (entry.secondRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid secondIndex
    simpa [r, i1, secondIndex,
      DegreeSevenStageSixEntry.rootIntervals] using hmem
  have hthirdMem : voightSortedRoot r hrsplit i2 ∈
      Set.Icc (entry.thirdRoot.lower : ℝ)
        (entry.thirdRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid thirdIndex
    simpa [r, i2, thirdIndex,
      DegreeSevenStageSixEntry.rootIntervals] using hmem
  have hfourthMem : voightSortedRoot r hrsplit i3 ∈
      Set.Icc (entry.fourthRoot.lower : ℝ)
        (entry.fourthRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid fourthIndex
    simpa [r, i3, fourthIndex,
      DegreeSevenStageSixEntry.rootIntervals] using hmem
  have hfifthMem : voightSortedRoot r hrsplit i4 ∈
      Set.Icc (entry.fifthRoot.lower : ℝ)
        (entry.fifthRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid fifthIndex
    simpa [r, i4, fifthIndex,
      DegreeSevenStageSixEntry.rootIntervals] using hmem
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
    norm_num [hqdegree, qi1, i1] at hsign
    exact hsign
  have hthirdSign :
      q.eval (voightSortedRoot r hrsplit i2) ≤ 0 := by
    have hsign :=
      eval_sign_at_derivativeSortedRoot_of_leadingCoeff_pos
        hqsplit hqlead hqseparable qi2
    rw [hrootEq2] at hsign
    norm_num [hqdegree, qi2, i2] at hsign
    linarith
  have hfourthSign :
      0 ≤ q.eval (voightSortedRoot r hrsplit i3) := by
    have hsign :=
      eval_sign_at_derivativeSortedRoot_of_leadingCoeff_pos
        hqsplit hqlead hqseparable qi3
    rw [hrootEq3] at hsign
    norm_num [hqdegree, qi3, i3] at hsign
    exact hsign
  have hfifthSign :
      q.eval (voightSortedRoot r hrsplit i4) ≤ 0 := by
    have hsign :=
      eval_sign_at_derivativeSortedRoot_of_leadingCoeff_pos
        hqsplit hqlead hqseparable qi4
    rw [hrootEq4] at hsign
    norm_num [hqdegree, qi4, i4] at hsign
    linarith
  have hleftSign : 0 ≤ q.eval (entry.leftEndpoint : ℝ) := by
    have hsign :=
      eval_sign_left_of_all_roots_of_leadingCoeff_pos
        hqsplit hqlead (entry.leftEndpoint : ℝ) (by
          intro y hy
          exact (hqbounds y hy).1.le)
    norm_num [hqdegree] at hsign
    exact hsign
  have hrightSign : 0 ≤ q.eval (entry.rightEndpoint : ℝ) :=
    eval_nonneg_right_of_all_roots_of_leadingCoeff_pos
      hqsplit hqlead (entry.rightEndpoint : ℝ) (by
        intro y hy
        exact (hqbounds y hy).2.le)
  apply mem_sexticTranslationCandidates_of_signs
    entry.baseCoefficients entry.leftEndpoint entry.rightEndpoint
    entry.firstRoot entry.secondRoot entry.thirdRoot entry.fourthRoot
    entry.fifthRoot
    (by
      have hforall := (List.forall_iff_forall_mem.mp
        hvalid.2.2.2.2.1) entry.firstRoot
        (by simp [DegreeSevenStageSixEntry.rootIntervals])
      exact hforall.1.le)
    (by
      have hforall := (List.forall_iff_forall_mem.mp
        hvalid.2.2.2.2.1) entry.secondRoot
        (by simp [DegreeSevenStageSixEntry.rootIntervals])
      exact hforall.1.le)
    (by
      have hforall := (List.forall_iff_forall_mem.mp
        hvalid.2.2.2.2.1) entry.thirdRoot
        (by simp [DegreeSevenStageSixEntry.rootIntervals])
      exact hforall.1.le)
    (by
      have hforall := (List.forall_iff_forall_mem.mp
        hvalid.2.2.2.2.1) entry.fourthRoot
        (by simp [DegreeSevenStageSixEntry.rootIntervals])
      exact hforall.1.le)
    (by
      have hforall := (List.forall_iff_forall_mem.mp
        hvalid.2.2.2.2.1) entry.fifthRoot
        (by simp [DegreeSevenStageSixEntry.rootIntervals])
      exact hforall.1.le)
    (voightSortedRoot r hrsplit i0)
    (voightSortedRoot r hrsplit i1)
    (voightSortedRoot r hrsplit i2)
    (voightSortedRoot r hrsplit i3)
    (voightSortedRoot r hrsplit i4)
    hfirstMem hsecondMem hthirdMem hfourthMem hfifthMem (f.coeff 1)
  · simpa [q, DegreeSevenStageSixEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hleftSign
  · simpa [q, DegreeSevenStageSixEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hfirstSign
  · simpa [q, DegreeSevenStageSixEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hsecondSign
  · simpa [q, DegreeSevenStageSixEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hthirdSign
  · simpa [q, DegreeSevenStageSixEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hfourthSign
  · simpa [q, DegreeSevenStageSixEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hfifthSign
  · simpa [q, DegreeSevenStageSixEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hrightSign

namespace DegreeSevenStageFiveEntry

/-- A coarse interval for the first root of the quintic second-derivative
stage, obtained from the outer root bound and the first quartic critical
interval. -/
def firstInterlacingInterval (entry : DegreeSevenStageFiveEntry) :
    RationalRootInterval :=
  ⟨entry.leftEndpoint, entry.firstRoot.upper⟩

def secondInterlacingInterval (entry : DegreeSevenStageFiveEntry) :
    RationalRootInterval :=
  ⟨entry.firstRoot.lower, entry.secondRoot.upper⟩

def thirdInterlacingInterval (entry : DegreeSevenStageFiveEntry) :
    RationalRootInterval :=
  ⟨entry.secondRoot.lower, entry.thirdRoot.upper⟩

def fourthInterlacingInterval (entry : DegreeSevenStageFiveEntry) :
    RationalRootInterval :=
  ⟨entry.thirdRoot.lower, entry.fourthRoot.upper⟩

def fifthInterlacingInterval (entry : DegreeSevenStageFiveEntry) :
    RationalRootInterval :=
  ⟨entry.fourthRoot.lower, entry.rightEndpoint⟩

def stageSixBaseCoefficients (entry : DegreeSevenStageFiveEntry)
    (a2 : ℤ) : List ℤ :=
  [0, 2 * a2, 3 * entry.a3, 4 * entry.a4,
    5 * entry.a5, 6 * entry.a6, 7]

/-- The exact `a1` set obtained without materializing a separate certificate
for every `a2` prefix.  Rolle interlacing places the five quintic roots in the
five coarse intervals above. -/
def a1InterlacingCandidates (entry : DegreeSevenStageFiveEntry)
    (a2 : ℤ) : Finset ℤ :=
  sexticTranslationCandidates (entry.stageSixBaseCoefficients a2)
    entry.leftEndpoint entry.rightEndpoint entry.firstInterlacingInterval
      entry.secondInterlacingInterval entry.thirdInterlacingInterval
      entry.fourthInterlacingInterval entry.fifthInterlacingInterval

end DegreeSevenStageFiveEntry

/-- The Stage Five quartic certificate already contains enough order data to
bound all five roots of the quintic second-derivative stage.  Consequently the
actual `a1` belongs to a finite exact set without generating one five-root
certificate for each `a2` prefix. -/
theorem degreeSeven_minimumHunterCandidate_a1_mem_of_stageFive_valid
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (entry : DegreeSevenStageFiveEntry)
    (hvalid : entry.Valid)
    (ha6 : entry.a6 = f.coeff 6)
    (ha5 : entry.a5 = f.coeff 5)
    (ha4 : entry.a4 = f.coeff 4)
    (ha3 : entry.a3 = f.coeff 3) :
    f.coeff 1 ∈ entry.a1InterlacingCandidates (f.coeff 2) := by
  let p : ℝ[X] := f.map (algebraMap ℤ ℝ)
  let q : ℝ[X] := integerPolynomialReal
    [f.coeff 1, 2 * f.coeff 2, 3 * entry.a3, 4 * entry.a4,
      5 * entry.a5, 6 * entry.a6, 7]
  let r : ℝ[X] := integerPolynomialReal
    [f.coeff 2, 3 * entry.a3, 6 * entry.a4,
      10 * entry.a5, 15 * entry.a6, 21]
  let s : ℝ[X] := integerPolynomialReal entry.derivativeCoefficients
  have hpdegree : p.natDegree = 7 := by
    dsimp [p]
    rw [Polynomial.natDegree_map_eq_of_injective
      (Int.cast_injective : Function.Injective (algebraMap ℤ ℝ)),
      h.2.2.1]
  have hpseparable : p.Separable := by
    simpa [p] using hunterPolynomialCandidate_separable_real_general h
  have hqEq : q = voightDerivativeStage p 1 := by
    symm
    simpa [p, q, ha6, ha5, ha4, ha3] using
      degreeSeven_firstDerivativeStage_eq h.1 h.2.2.1
  have hrEq : r = voightDerivativeStage p 2 := by
    symm
    simpa [p, r, ha6, ha5, ha4, ha3] using
      degreeSeven_secondDerivativeStage_eq h.1 h.2.2.1
  have hqsplit : q.Splits := by
    rw [hqEq]
    exact voightDerivativeStage_splits h.2.2.2.1 1
  have hqseparable : q.Separable := by
    rw [hqEq]
    exact voightDerivativeStage_separable h.2.2.2.1 hpseparable
      (by rw [hpdegree]; norm_num)
  have hrsplit : r.Splits := by
    rw [hrEq]
    exact voightDerivativeStage_splits h.2.2.2.1 2
  have hrseparable : r.Separable := by
    rw [hrEq]
    exact voightDerivativeStage_separable h.2.2.2.1 hpseparable
      (by rw [hpdegree]; norm_num)
  have hssplit : s.Splits :=
    integerPolynomial_splits_of_generalRootIntervals hvalid
  have hqdegree : q.natDegree = 6 := by
    apply integerPolynomial_natDegree_of_generalRootIntervals
    · norm_num
    · norm_num
  have hrdegree : r.natDegree = 5 := by
    apply integerPolynomial_natDegree_of_generalRootIntervals
    · norm_num
    · norm_num
  have hsdegree : s.natDegree = 4 :=
    integerPolynomial_natDegree_of_generalRootIntervals
      hvalid.2.1 hvalid.2.2.1
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
  have hrbounds : ∀ z ∈ r.roots,
      (entry.leftEndpoint : ℝ) < z ∧
        z < (entry.rightEndpoint : ℝ) := by
    rw [hrEq]
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
  have hqderivEq : q.derivative = C 2 * r := by
    simpa [q, r] using
      degreeSeven_sextic_derivative_eq
        (f.coeff 1) (f.coeff 2) entry.a3 entry.a4 entry.a5 entry.a6
  have hrderivEq : r.derivative = C 3 * s := by
    simpa [r, s, DegreeSevenStageFiveEntry.derivativeCoefficients] using
      degreeSeven_quintic_derivative_eq
        (f.coeff 2) entry.a3 entry.a4 entry.a5 entry.a6
  let i0 : Fin r.natDegree := ⟨0, by rw [hrdegree]; norm_num⟩
  let i1 : Fin r.natDegree := ⟨1, by rw [hrdegree]; norm_num⟩
  let i2 : Fin r.natDegree := ⟨2, by rw [hrdegree]; norm_num⟩
  let i3 : Fin r.natDegree := ⟨3, by rw [hrdegree]; norm_num⟩
  let i4 : Fin r.natDegree := ⟨4, by rw [hrdegree]; norm_num⟩
  let j0 : Fin s.natDegree := ⟨0, by rw [hsdegree]; norm_num⟩
  let j1 : Fin s.natDegree := ⟨1, by rw [hsdegree]; norm_num⟩
  let j2 : Fin s.natDegree := ⟨2, by rw [hsdegree]; norm_num⟩
  let j3 : Fin s.natDegree := ⟨3, by rw [hsdegree]; norm_num⟩
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
  let qi3 : Fin q.derivative.natDegree :=
    ⟨i3, by
      rw [hqderivEq, Polynomial.natDegree_C_mul
        (by norm_num : (2 : ℝ) ≠ 0)]
      exact i3.isLt⟩
  let qi4 : Fin q.derivative.natDegree :=
    ⟨i4, by
      rw [hqderivEq, Polynomial.natDegree_C_mul
        (by norm_num : (2 : ℝ) ≠ 0)]
      exact i4.isLt⟩
  let rj0 : Fin r.derivative.natDegree :=
    ⟨j0, by
      rw [hrderivEq, Polynomial.natDegree_C_mul
        (by norm_num : (3 : ℝ) ≠ 0)]
      exact j0.isLt⟩
  let rj1 : Fin r.derivative.natDegree :=
    ⟨j1, by
      rw [hrderivEq, Polynomial.natDegree_C_mul
        (by norm_num : (3 : ℝ) ≠ 0)]
      exact j1.isLt⟩
  let rj2 : Fin r.derivative.natDegree :=
    ⟨j2, by
      rw [hrderivEq, Polynomial.natDegree_C_mul
        (by norm_num : (3 : ℝ) ≠ 0)]
      exact j2.isLt⟩
  let rj3 : Fin r.derivative.natDegree :=
    ⟨j3, by
      rw [hrderivEq, Polynomial.natDegree_C_mul
        (by norm_num : (3 : ℝ) ≠ 0)]
      exact j3.isLt⟩
  have hqrootEq0 :
      voightSortedRoot q.derivative
          (splits_derivative_of_splits_real hqsplit) qi0 =
        voightSortedRoot r hrsplit i0 := by
    simpa [qi0] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (2 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hqsplit)
        hrsplit hqderivEq i0
  have hqrootEq1 :
      voightSortedRoot q.derivative
          (splits_derivative_of_splits_real hqsplit) qi1 =
        voightSortedRoot r hrsplit i1 := by
    simpa [qi1] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (2 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hqsplit)
        hrsplit hqderivEq i1
  have hqrootEq2 :
      voightSortedRoot q.derivative
          (splits_derivative_of_splits_real hqsplit) qi2 =
        voightSortedRoot r hrsplit i2 := by
    simpa [qi2] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (2 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hqsplit)
        hrsplit hqderivEq i2
  have hqrootEq3 :
      voightSortedRoot q.derivative
          (splits_derivative_of_splits_real hqsplit) qi3 =
        voightSortedRoot r hrsplit i3 := by
    simpa [qi3] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (2 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hqsplit)
        hrsplit hqderivEq i3
  have hqrootEq4 :
      voightSortedRoot q.derivative
          (splits_derivative_of_splits_real hqsplit) qi4 =
        voightSortedRoot r hrsplit i4 := by
    simpa [qi4] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (2 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hqsplit)
        hrsplit hqderivEq i4
  have hcritEq0 :
      voightSortedRoot r.derivative
          (splits_derivative_of_splits_real hrsplit) rj0 =
        voightSortedRoot s hssplit j0 := by
    simpa [rj0] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (3 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hrsplit)
        hssplit hrderivEq j0
  have hcritEq1 :
      voightSortedRoot r.derivative
          (splits_derivative_of_splits_real hrsplit) rj1 =
        voightSortedRoot s hssplit j1 := by
    simpa [rj1] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (3 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hrsplit)
        hssplit hrderivEq j1
  have hcritEq2 :
      voightSortedRoot r.derivative
          (splits_derivative_of_splits_real hrsplit) rj2 =
        voightSortedRoot s hssplit j2 := by
    simpa [rj2] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (3 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hrsplit)
        hssplit hrderivEq j2
  have hcritEq3 :
      voightSortedRoot r.derivative
          (splits_derivative_of_splits_real hrsplit) rj3 =
        voightSortedRoot s hssplit j3 := by
    simpa [rj3] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (3 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hrsplit)
        hssplit hrderivEq j3
  let c0Index : Fin entry.rootIntervals.length :=
    ⟨0, by simp [DegreeSevenStageFiveEntry.rootIntervals]⟩
  let c1Index : Fin entry.rootIntervals.length :=
    ⟨1, by simp [DegreeSevenStageFiveEntry.rootIntervals]⟩
  let c2Index : Fin entry.rootIntervals.length :=
    ⟨2, by simp [DegreeSevenStageFiveEntry.rootIntervals]⟩
  let c3Index : Fin entry.rootIntervals.length :=
    ⟨3, by simp [DegreeSevenStageFiveEntry.rootIntervals]⟩
  have hc0Mem : voightSortedRoot s hssplit j0 ∈
      Set.Icc (entry.firstRoot.lower : ℝ)
        (entry.firstRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid c0Index
    simpa [s, j0, c0Index,
      DegreeSevenStageFiveEntry.rootIntervals] using hmem
  have hc1Mem : voightSortedRoot s hssplit j1 ∈
      Set.Icc (entry.secondRoot.lower : ℝ)
        (entry.secondRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid c1Index
    simpa [s, j1, c1Index,
      DegreeSevenStageFiveEntry.rootIntervals] using hmem
  have hc2Mem : voightSortedRoot s hssplit j2 ∈
      Set.Icc (entry.thirdRoot.lower : ℝ)
        (entry.thirdRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid c2Index
    simpa [s, j2, c2Index,
      DegreeSevenStageFiveEntry.rootIntervals] using hmem
  have hc3Mem : voightSortedRoot s hssplit j3 ∈
      Set.Icc (entry.fourthRoot.lower : ℝ)
        (entry.fourthRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid c3Index
    simpa [s, j3, c3Index,
      DegreeSevenStageFiveEntry.rootIntervals] using hmem
  have hinterlace0 :=
    derivativeSortedRoot_between_sortedRoots r hrsplit hrseparable rj0
  have hinterlace1 :=
    derivativeSortedRoot_between_sortedRoots r hrsplit hrseparable rj1
  have hinterlace2 :=
    derivativeSortedRoot_between_sortedRoots r hrsplit hrseparable rj2
  have hinterlace3 :=
    derivativeSortedRoot_between_sortedRoots r hrsplit hrseparable rj3
  rw [hcritEq0] at hinterlace0
  rw [hcritEq1] at hinterlace1
  rw [hcritEq2] at hinterlace2
  rw [hcritEq3] at hinterlace3
  have hbetween0 :
      voightSortedRoot r hrsplit i0 <
          voightSortedRoot s hssplit j0 ∧
        voightSortedRoot s hssplit j0 <
          voightSortedRoot r hrsplit i1 := by
    simpa [i0, i1, j0, rj0] using hinterlace0
  have hbetween1 :
      voightSortedRoot r hrsplit i1 <
          voightSortedRoot s hssplit j1 ∧
        voightSortedRoot s hssplit j1 <
          voightSortedRoot r hrsplit i2 := by
    simpa [i1, i2, j1, rj1] using hinterlace1
  have hbetween2 :
      voightSortedRoot r hrsplit i2 <
          voightSortedRoot s hssplit j2 ∧
        voightSortedRoot s hssplit j2 <
          voightSortedRoot r hrsplit i3 := by
    simpa [i2, i3, j2, rj2] using hinterlace2
  have hbetween3 :
      voightSortedRoot r hrsplit i3 <
          voightSortedRoot s hssplit j3 ∧
        voightSortedRoot s hssplit j3 <
          voightSortedRoot r hrsplit i4 := by
    simpa [i3, i4, j3, rj3] using hinterlace3
  have hi0Bounds := hrbounds (voightSortedRoot r hrsplit i0)
    (voightSortedRoot_mem_roots hrsplit i0)
  have hi4Bounds := hrbounds (voightSortedRoot r hrsplit i4)
    (voightSortedRoot_mem_roots hrsplit i4)
  have hfirstMem : voightSortedRoot r hrsplit i0 ∈
      Set.Icc
        (entry.firstInterlacingInterval.lower : ℝ)
        (entry.firstInterlacingInterval.upper : ℝ) := by
    constructor
    · simpa [DegreeSevenStageFiveEntry.firstInterlacingInterval] using
        hi0Bounds.1.le
    · change voightSortedRoot r hrsplit i0 ≤
        (entry.firstRoot.upper : ℝ)
      exact hbetween0.1.le.trans hc0Mem.2
  have hsecondMem : voightSortedRoot r hrsplit i1 ∈
      Set.Icc
        (entry.secondInterlacingInterval.lower : ℝ)
        (entry.secondInterlacingInterval.upper : ℝ) := by
    constructor
    · change (entry.firstRoot.lower : ℝ) ≤
        voightSortedRoot r hrsplit i1
      exact hc0Mem.1.trans hbetween0.2.le
    · change voightSortedRoot r hrsplit i1 ≤
        (entry.secondRoot.upper : ℝ)
      exact hbetween1.1.le.trans hc1Mem.2
  have hthirdMem : voightSortedRoot r hrsplit i2 ∈
      Set.Icc
        (entry.thirdInterlacingInterval.lower : ℝ)
        (entry.thirdInterlacingInterval.upper : ℝ) := by
    constructor
    · change (entry.secondRoot.lower : ℝ) ≤
        voightSortedRoot r hrsplit i2
      exact hc1Mem.1.trans hbetween1.2.le
    · change voightSortedRoot r hrsplit i2 ≤
        (entry.thirdRoot.upper : ℝ)
      exact hbetween2.1.le.trans hc2Mem.2
  have hfourthMem : voightSortedRoot r hrsplit i3 ∈
      Set.Icc
        (entry.fourthInterlacingInterval.lower : ℝ)
        (entry.fourthInterlacingInterval.upper : ℝ) := by
    constructor
    · change (entry.thirdRoot.lower : ℝ) ≤
        voightSortedRoot r hrsplit i3
      exact hc2Mem.1.trans hbetween2.2.le
    · change voightSortedRoot r hrsplit i3 ≤
        (entry.fourthRoot.upper : ℝ)
      exact hbetween3.1.le.trans hc3Mem.2
  have hfifthMem : voightSortedRoot r hrsplit i4 ∈
      Set.Icc
        (entry.fifthInterlacingInterval.lower : ℝ)
        (entry.fifthInterlacingInterval.upper : ℝ) := by
    constructor
    · change (entry.fourthRoot.lower : ℝ) ≤
        voightSortedRoot r hrsplit i4
      exact hc3Mem.1.trans hbetween3.2.le
    · simpa [DegreeSevenStageFiveEntry.fifthInterlacingInterval] using
        hi4Bounds.2.le
  have hfirstOrdered :
      entry.firstInterlacingInterval.lower ≤
        entry.firstInterlacingInterval.upper := by
    exact_mod_cast hfirstMem.1.trans hfirstMem.2
  have hsecondOrdered :
      entry.secondInterlacingInterval.lower ≤
        entry.secondInterlacingInterval.upper := by
    exact_mod_cast hsecondMem.1.trans hsecondMem.2
  have hthirdOrdered :
      entry.thirdInterlacingInterval.lower ≤
        entry.thirdInterlacingInterval.upper := by
    exact_mod_cast hthirdMem.1.trans hthirdMem.2
  have hfourthOrdered :
      entry.fourthInterlacingInterval.lower ≤
        entry.fourthInterlacingInterval.upper := by
    exact_mod_cast hfourthMem.1.trans hfourthMem.2
  have hfifthOrdered :
      entry.fifthInterlacingInterval.lower ≤
        entry.fifthInterlacingInterval.upper := by
    exact_mod_cast hfifthMem.1.trans hfifthMem.2
  have hfirstSign :
      q.eval (voightSortedRoot r hrsplit i0) ≤ 0 := by
    have hsign :=
      eval_sign_at_derivativeSortedRoot_of_leadingCoeff_pos
        hqsplit hqlead hqseparable qi0
    rw [hqrootEq0] at hsign
    norm_num [hqdegree, qi0, i0] at hsign
    linarith
  have hsecondSign :
      0 ≤ q.eval (voightSortedRoot r hrsplit i1) := by
    have hsign :=
      eval_sign_at_derivativeSortedRoot_of_leadingCoeff_pos
        hqsplit hqlead hqseparable qi1
    rw [hqrootEq1] at hsign
    norm_num [hqdegree, qi1, i1] at hsign
    exact hsign
  have hthirdSign :
      q.eval (voightSortedRoot r hrsplit i2) ≤ 0 := by
    have hsign :=
      eval_sign_at_derivativeSortedRoot_of_leadingCoeff_pos
        hqsplit hqlead hqseparable qi2
    rw [hqrootEq2] at hsign
    norm_num [hqdegree, qi2, i2] at hsign
    linarith
  have hfourthSign :
      0 ≤ q.eval (voightSortedRoot r hrsplit i3) := by
    have hsign :=
      eval_sign_at_derivativeSortedRoot_of_leadingCoeff_pos
        hqsplit hqlead hqseparable qi3
    rw [hqrootEq3] at hsign
    norm_num [hqdegree, qi3, i3] at hsign
    exact hsign
  have hfifthSign :
      q.eval (voightSortedRoot r hrsplit i4) ≤ 0 := by
    have hsign :=
      eval_sign_at_derivativeSortedRoot_of_leadingCoeff_pos
        hqsplit hqlead hqseparable qi4
    rw [hqrootEq4] at hsign
    norm_num [hqdegree, qi4, i4] at hsign
    linarith
  have hleftSign : 0 ≤ q.eval (entry.leftEndpoint : ℝ) := by
    have hsign :=
      eval_sign_left_of_all_roots_of_leadingCoeff_pos
        hqsplit hqlead (entry.leftEndpoint : ℝ) (by
          intro y hy
          exact (hqbounds y hy).1.le)
    norm_num [hqdegree] at hsign
    exact hsign
  have hrightSign : 0 ≤ q.eval (entry.rightEndpoint : ℝ) :=
    eval_nonneg_right_of_all_roots_of_leadingCoeff_pos
      hqsplit hqlead (entry.rightEndpoint : ℝ) (by
        intro y hy
        exact (hqbounds y hy).2.le)
  apply mem_sexticTranslationCandidates_of_signs
    (entry.stageSixBaseCoefficients (f.coeff 2))
    entry.leftEndpoint entry.rightEndpoint
    entry.firstInterlacingInterval entry.secondInterlacingInterval
    entry.thirdInterlacingInterval entry.fourthInterlacingInterval
    entry.fifthInterlacingInterval
    hfirstOrdered hsecondOrdered hthirdOrdered hfourthOrdered hfifthOrdered
    (voightSortedRoot r hrsplit i0)
    (voightSortedRoot r hrsplit i1)
    (voightSortedRoot r hrsplit i2)
    (voightSortedRoot r hrsplit i3)
    (voightSortedRoot r hrsplit i4)
    hfirstMem hsecondMem hthirdMem hfourthMem hfifthMem (f.coeff 1)
  · simpa [q, DegreeSevenStageFiveEntry.stageSixBaseCoefficients,
      DegreeSevenStageFiveEntry.a1InterlacingCandidates,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hleftSign
  · simpa [q, DegreeSevenStageFiveEntry.stageSixBaseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hfirstSign
  · simpa [q, DegreeSevenStageFiveEntry.stageSixBaseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hsecondSign
  · simpa [q, DegreeSevenStageFiveEntry.stageSixBaseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hthirdSign
  · simpa [q, DegreeSevenStageFiveEntry.stageSixBaseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hfourthSign
  · simpa [q, DegreeSevenStageFiveEntry.stageSixBaseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hfifthSign
  · simpa [q, DegreeSevenStageFiveEntry.stageSixBaseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hrightSign

/-- Complete compressed sixth-stage recursion statement: the fifth-stage row,
the actual `a2`, and the exact interlacing `a1` set are all obtained inside
Lean without a million-row generated table. -/
theorem degreeSeven_minimumHunterCandidate_a1_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f) :
    ∃ entry ∈ degreeSevenStageFiveEntries,
      entry.a6 = f.coeff 6 ∧
      entry.a5 = f.coeff 5 ∧
      entry.a4 = f.coeff 4 ∧
      entry.a3 = f.coeff 3 ∧
      f.coeff 2 ∈ entry.a2Candidates ∧
      f.coeff 1 ∈
        entry.toEntry.a1InterlacingCandidates (f.coeff 2) := by
  obtain ⟨entry, hentry, ha6, ha5, ha4, ha3, ha2⟩ :=
    degreeSeven_minimumHunterCandidate_a2_mem h
  have hvalid : entry.toEntry.Valid :=
    (List.forall_iff_forall_mem.mp
      degreeSevenStageFiveEntries_valid) entry hentry
  exact ⟨entry, hentry, ha6, ha5, ha4, ha3, ha2,
    degreeSeven_minimumHunterCandidate_a1_mem_of_stageFive_valid
      h entry.toEntry hvalid
        (by simpa [DegreeSevenStageFiveDyadicEntry.toEntry] using ha6)
        (by simpa [DegreeSevenStageFiveDyadicEntry.toEntry] using ha5)
        (by simpa [DegreeSevenStageFiveDyadicEntry.toEntry] using ha4)
        (by simpa [DegreeSevenStageFiveDyadicEntry.toEntry] using ha3)⟩

namespace DegreeSevenStageFiveEntry

/-- One common rational interval containing every root at every remaining
Rolle stage.  It gives a compact final fallback for the constant coefficient. -/
def globalRootInterval (entry : DegreeSevenStageFiveEntry) :
    RationalRootInterval :=
  ⟨entry.leftEndpoint, entry.rightEndpoint⟩

def stageSevenBaseCoefficients (entry : DegreeSevenStageFiveEntry)
    (a2 a1 : ℤ) : List ℤ :=
  [0, a1, a2, entry.a3, entry.a4, entry.a5, entry.a6, 1]

/-- A finite constant-coefficient set using the common global interval for all
six roots of the first derivative. -/
def a0GlobalCandidates (entry : DegreeSevenStageFiveEntry)
    (a2 a1 : ℤ) : Finset ℤ :=
  septicTranslationCandidates
    (entry.stageSevenBaseCoefficients a2 a1)
    entry.leftEndpoint entry.rightEndpoint
    entry.globalRootInterval entry.globalRootInterval
    entry.globalRootInterval entry.globalRootInterval
    entry.globalRootInterval entry.globalRootInterval

end DegreeSevenStageFiveEntry

/-- A monic septic is exactly its eight-term dense coefficient expansion after
mapping to the reals. -/
theorem degreeSeven_realPolynomial_eq_dense
    {f : ℤ[X]} (hmonic : f.Monic) (hdegree : f.natDegree = 7) :
    f.map (algebraMap ℤ ℝ) =
      integerPolynomialReal
        [f.coeff 0, f.coeff 1, f.coeff 2, f.coeff 3,
          f.coeff 4, f.coeff 5, f.coeff 6, 1] := by
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
    norm_num
  by_cases hm6 : m = 6
  · subst m
    norm_num
  by_cases hm7 : m = 7
  · subst m
    have hcoeff : f.coeff 7 = 1 := by
      rw [← hdegree]
      exact hmonic.coeff_natDegree
    norm_num [hcoeff]
  have hm8 : 8 ≤ m := by omega
  have hright :
      [f.coeff 0, f.coeff 1, f.coeff 2, f.coeff 3,
        f.coeff 4, f.coeff 5, f.coeff 6, 1].getD m 0 = 0 := by
    rw [List.getD_eq_default]
    simp
    omega
  rw [hright, map_zero]
  have hcoeff : f.coeff m = 0 := by
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    rw [hdegree]
    omega
  rw [hcoeff, map_zero]

/-- The outer Lagrange interval alone gives a finite final set for `a0` once
the higher coefficients are fixed. -/
theorem degreeSeven_minimumHunterCandidate_a0_mem_of_stageFive
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (entry : DegreeSevenStageFiveEntry)
    (ha6 : entry.a6 = f.coeff 6)
    (ha5 : entry.a5 = f.coeff 5)
    (ha4 : entry.a4 = f.coeff 4)
    (ha3 : entry.a3 = f.coeff 3) :
    f.coeff 0 ∈
      entry.a0GlobalCandidates (f.coeff 2) (f.coeff 1) := by
  let p : ℝ[X] := integerPolynomialReal
    [f.coeff 0, f.coeff 1, f.coeff 2, f.coeff 3,
      f.coeff 4, f.coeff 5, f.coeff 6, 1]
  let q : ℝ[X] := integerPolynomialReal
    [f.coeff 1, 2 * f.coeff 2, 3 * entry.a3, 4 * entry.a4,
      5 * entry.a5, 6 * entry.a6, 7]
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
    simpa [q, ha6, ha5, ha4, ha3] using
      degreeSeven_firstDerivativeStage_eq h.1 h.2.2.1
  have hqsplit : q.Splits := by
    rw [hqStage]
    exact voightDerivativeStage_splits h.2.2.2.1 1
  have hqdegree : q.natDegree = 6 := by
    apply integerPolynomial_natDegree_of_generalRootIntervals
    · norm_num
    · norm_num
  have hqbounds : ∀ z ∈ q.roots,
      (entry.leftEndpoint : ℝ) < z ∧
        z < (entry.rightEndpoint : ℝ) := by
    rw [hqStage]
    apply voightDerivativeStage_roots_strict_bounds
      h.2.2.2.1
      (hunterPolynomialCandidate_separable_real_general h)
    · intro z hz
      have hbound :=
        degreeSeven_minimumHunterCandidate_root_lagrange_strict_bounds
          h z hz
      simpa [DegreeSevenStageFiveEntry.leftEndpoint,
        DegreeSevenStageFiveEntry.rightEndpoint, ha6] using hbound
    · rw [Polynomial.natDegree_map_eq_of_injective
        (Int.cast_injective : Function.Injective (algebraMap ℤ ℝ)),
        h.2.2.1]
      norm_num
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
  have hmem0 : voightSortedRoot q hqsplit i0 ∈
      Set.Icc (entry.globalRootInterval.lower : ℝ)
        (entry.globalRootInterval.upper : ℝ) := by
    have hb := hqbounds _ (voightSortedRoot_mem_roots hqsplit i0)
    simpa [DegreeSevenStageFiveEntry.globalRootInterval] using
      ⟨hb.1.le, hb.2.le⟩
  have hmem1 : voightSortedRoot q hqsplit i1 ∈
      Set.Icc (entry.globalRootInterval.lower : ℝ)
        (entry.globalRootInterval.upper : ℝ) := by
    have hb := hqbounds _ (voightSortedRoot_mem_roots hqsplit i1)
    simpa [DegreeSevenStageFiveEntry.globalRootInterval] using
      ⟨hb.1.le, hb.2.le⟩
  have hmem2 : voightSortedRoot q hqsplit i2 ∈
      Set.Icc (entry.globalRootInterval.lower : ℝ)
        (entry.globalRootInterval.upper : ℝ) := by
    have hb := hqbounds _ (voightSortedRoot_mem_roots hqsplit i2)
    simpa [DegreeSevenStageFiveEntry.globalRootInterval] using
      ⟨hb.1.le, hb.2.le⟩
  have hmem3 : voightSortedRoot q hqsplit i3 ∈
      Set.Icc (entry.globalRootInterval.lower : ℝ)
        (entry.globalRootInterval.upper : ℝ) := by
    have hb := hqbounds _ (voightSortedRoot_mem_roots hqsplit i3)
    simpa [DegreeSevenStageFiveEntry.globalRootInterval] using
      ⟨hb.1.le, hb.2.le⟩
  have hmem4 : voightSortedRoot q hqsplit i4 ∈
      Set.Icc (entry.globalRootInterval.lower : ℝ)
        (entry.globalRootInterval.upper : ℝ) := by
    have hb := hqbounds _ (voightSortedRoot_mem_roots hqsplit i4)
    simpa [DegreeSevenStageFiveEntry.globalRootInterval] using
      ⟨hb.1.le, hb.2.le⟩
  have hmem5 : voightSortedRoot q hqsplit i5 ∈
      Set.Icc (entry.globalRootInterval.lower : ℝ)
        (entry.globalRootInterval.upper : ℝ) := by
    have hb := hqbounds _ (voightSortedRoot_mem_roots hqsplit i5)
    simpa [DegreeSevenStageFiveEntry.globalRootInterval] using
      ⟨hb.1.le, hb.2.le⟩
  have hintervalOrdered :
      entry.globalRootInterval.lower ≤
        entry.globalRootInterval.upper := by
    exact_mod_cast hmem0.1.trans hmem0.2
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
        simpa [DegreeSevenStageFiveEntry.leftEndpoint, ha6] using hb)
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
    simpa [DegreeSevenStageFiveEntry.rightEndpoint, ha6] using hb
  rw [DegreeSevenStageFiveEntry.a0GlobalCandidates]
  apply mem_septicTranslationCandidates_of_signs
    (entry.stageSevenBaseCoefficients (f.coeff 2) (f.coeff 1))
    entry.leftEndpoint entry.rightEndpoint
    entry.globalRootInterval entry.globalRootInterval
    entry.globalRootInterval entry.globalRootInterval
    entry.globalRootInterval entry.globalRootInterval
    hintervalOrdered hintervalOrdered hintervalOrdered
    hintervalOrdered hintervalOrdered hintervalOrdered
    (voightSortedRoot q hqsplit i0)
    (voightSortedRoot q hqsplit i1)
    (voightSortedRoot q hqsplit i2)
    (voightSortedRoot q hqsplit i3)
    (voightSortedRoot q hqsplit i4)
    (voightSortedRoot q hqsplit i5)
    hmem0 hmem1 hmem2 hmem3 hmem4 hmem5 (f.coeff 0)
  all_goals
    simp only [DegreeSevenStageFiveEntry.stageSevenBaseCoefficients]
  · simpa [p, integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval,
      ha6, ha5, ha4, ha3, add_comm] using hleftSign
  · simpa [p, integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval,
      ha6, ha5, ha4, ha3, add_comm] using hsign0
  · simpa [p, integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval,
      ha6, ha5, ha4, ha3, add_comm] using hsign1
  · simpa [p, integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval,
      ha6, ha5, ha4, ha3, add_comm] using hsign2
  · simpa [p, integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval,
      ha6, ha5, ha4, ha3, add_comm] using hsign3
  · simpa [p, integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval,
      ha6, ha5, ha4, ha3, add_comm] using hsign4
  · simpa [p, integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval,
      ha6, ha5, ha4, ha3, add_comm] using hsign5
  · simpa [p, integerPolynomialReal,
      DensePolynomial.eval_toPolynomial, DensePolynomial.eval,
      ha6, ha5, ha4, ha3, add_comm] using hrightSign

/-- Complete compressed coefficient recursion: every sharpened septic Hunter
candidate lies in the nested finite sets for `a2`, `a1`, and `a0`. -/
theorem degreeSeven_minimumHunterCandidate_allCoefficients_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f) :
    ∃ entry ∈ degreeSevenStageFiveEntries,
      entry.a6 = f.coeff 6 ∧
      entry.a5 = f.coeff 5 ∧
      entry.a4 = f.coeff 4 ∧
      entry.a3 = f.coeff 3 ∧
      f.coeff 2 ∈ entry.a2Candidates ∧
      f.coeff 1 ∈
        entry.toEntry.a1InterlacingCandidates (f.coeff 2) ∧
      f.coeff 0 ∈
        entry.toEntry.a0GlobalCandidates (f.coeff 2) (f.coeff 1) := by
  obtain ⟨entry, hentry, ha6, ha5, ha4, ha3, ha2, ha1⟩ :=
    degreeSeven_minimumHunterCandidate_a1_mem h
  have ha0 := degreeSeven_minimumHunterCandidate_a0_mem_of_stageFive
    h entry.toEntry
      (by simpa [DegreeSevenStageFiveDyadicEntry.toEntry] using ha6)
      (by simpa [DegreeSevenStageFiveDyadicEntry.toEntry] using ha5)
      (by simpa [DegreeSevenStageFiveDyadicEntry.toEntry] using ha4)
      (by simpa [DegreeSevenStageFiveDyadicEntry.toEntry] using ha3)
  exact ⟨entry, hentry, ha6, ha5, ha4, ha3, ha2, ha1, ha0⟩

end

end TraceEuclidean
