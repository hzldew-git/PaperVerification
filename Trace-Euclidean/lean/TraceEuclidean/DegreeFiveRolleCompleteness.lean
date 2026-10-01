import TraceEuclidean.DegreeFiveRolleStageThree
import TraceEuclidean.DegreeFiveVoightReduction

/-!
# Completeness of the first degree-five Rolle stage

This module connects the generated twenty-row certificate to every quintic
Hunter candidate below discriminant `14641`.  It proves that the normalized
third derivative is a split separable quadratic and hence that its two top
coefficients occur in the generated table.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

/-- An irreducible integral Hunter polynomial remains separable after mapping
to the reals. -/
theorem hunterPolynomialCandidate_separable_real
    {f : ℤ[X]} (h : HunterPolynomialCandidate 5 67 f) :
    (f.map (algebraMap ℤ ℝ)).Separable := by
  have hqirreducible : Irreducible (f.map (algebraMap ℤ ℚ)) :=
    (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map h.1).mp
      h.2.1
  have hqseparable : (f.map (algebraMap ℤ ℚ)).Separable :=
    hqirreducible.separable
  have hrseparable := hqseparable.map (f := algebraMap ℚ ℝ)
  convert hrseparable using 1
  ext z
  simp

/-- The normalized third derivative of a monic quintic has the dense
coefficient list used by the generated quadratic certificates. -/
theorem degreeFive_thirdDerivativeStage_eq
    {f : ℤ[X]} (hmonic : f.Monic) (hdegree : f.natDegree = 5) :
    voightDerivativeStage (f.map (algebraMap ℤ ℝ)) 3 =
      integerPolynomialReal
        [f.coeff 3, 4 * f.coeff 4, 10] := by
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
    have hcoeff : f.coeff 5 = 1 := by
      rw [← hdegree]
      exact hmonic.coeff_natDegree
    norm_num [hcoeff]
  have hm3 : 3 ≤ m := by omega
  have hright :
      [f.coeff 3, 4 * f.coeff 4, 10].getD m 0 = 0 := by
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

/-- The normalized second derivative of a monic quintic is the cubic used at
the next coefficient-pruning step. -/
theorem degreeFive_secondDerivativeStage_eq
    {f : ℤ[X]} (hmonic : f.Monic) (hdegree : f.natDegree = 5) :
    voightDerivativeStage (f.map (algebraMap ℤ ℝ)) 2 =
      integerPolynomialReal
        [f.coeff 2, 3 * f.coeff 3, 6 * f.coeff 4, 10] := by
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
    have hcoeff : f.coeff 5 = 1 := by
      rw [← hdegree]
      exact hmonic.coeff_natDegree
    norm_num [hcoeff]
  have hm4 : 4 ≤ m := by omega
  have hright :
      [f.coeff 2, 3 * f.coeff 3, 6 * f.coeff 4, 10].getD m 0 = 0 := by
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

/-- The derivative of the cubic stage is three times the quadratic stage, so
the two stages have the same critical roots. -/
theorem degreeFive_cubic_derivative_eq
    (a2 a3 a4 : ℤ) :
    (integerPolynomialReal
      [a2, 3 * a3, 6 * a4, 10]).derivative =
      C 3 * integerPolynomialReal [a3, 4 * a4, 10] := by
  rw [integerPolynomialReal_derivative]
  ext n
  rw [integerPolynomialReal, Polynomial.coeff_map,
    DensePolynomial.coeff_toPolynomial]
  rw [Polynomial.coeff_C_mul,
    integerPolynomialReal, Polynomial.coeff_map,
    DensePolynomial.coeff_toPolynomial]
  by_cases hn : n ≤ 3
  · interval_cases n <;>
      norm_num [DensePolynomial.derivative,
        DensePolynomial.add] <;> ring
  · have hn' : 4 ≤ n := by omega
    rw [List.getD_eq_default, List.getD_eq_default]
    all_goals norm_num [DensePolynomial.derivative,
      DensePolynomial.add] at *
    all_goals omega

/-- The only Hunter-compatible top pair whose quadratic has negative
discriminant does not split over the reals. -/
theorem degreeFive_badTopPair_not_splits :
    ¬(integerPolynomialReal [2, -8, 10]).Splits := by
  intro hsplits
  let p := integerPolynomialReal [2, -8, 10]
  have hp0 : p ≠ 0 := by
    intro hp
    have hcoeff := congrArg (fun q : ℝ[X] => q.coeff 2) hp
    norm_num [p, integerPolynomialReal,
      DensePolynomial.coeff_toPolynomial] at hcoeff
  have hcard : p.roots.card = p.natDegree :=
    Polynomial.splits_iff_card_roots.mp hsplits
  have hdegree : p.natDegree = 2 := by
    apply integerPolynomial_natDegree_of_generalRootIntervals
    · norm_num
    · norm_num
  have hroots : p.roots ≠ 0 := by
    intro hz
    rw [hz] at hcard
    simp [hdegree] at hcard
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hroots
  have heval : p.eval x = 0 := (Polynomial.mem_roots hp0).mp hx
  have hsquare : 0 ≤ (5 * x - 2) ^ 2 := sq_nonneg _
  norm_num [p, integerPolynomialReal,
    DensePolynomial.eval_toPolynomial,
    DensePolynomial.eval] at heval
  nlinarith

/-- The remaining excluded top pair is a double-root quadratic and therefore
is not separable. -/
theorem degreeFive_badTopPair_not_separable :
    ¬(integerPolynomialReal [0, 0, 10]).Separable := by
  intro hseparable
  have hnodup := Polynomial.nodup_roots hseparable
  have heq : integerPolynomialReal [0, 0, 10] =
      C (10 : ℝ) * X ^ 2 := by
    rw [integerPolynomialReal]
    norm_num [DensePolynomial.toPolynomial]
    have hten : (10 : ℝ[X]) = C (10 : ℝ) :=
      (Polynomial.C_ofNat 10).symm
    rw [hten]
    ring
  rw [heq, Polynomial.roots_C_mul _ (by norm_num),
    Polynomial.roots_X_pow] at hnodup
  rw [Multiset.nodup_iff_count_le_one] at hnodup
  have hcount := hnodup 0
  rw [Multiset.count_nsmul] at hcount
  norm_num at hcount

/-- Exact finite completeness of the generated top-coefficient table. -/
theorem degreeFiveStageThree_exists_entry_of_bounds
    {a4 a3 : ℤ}
    (ha4Lower : -2 ≤ a4) (ha4Upper : a4 ≤ 0)
    (ha3Lower : -6 ≤ a3) (ha3Upper : a3 ≤ 2)
    (hsum : 2 * a3 ≤ (-a4) ^ 2)
    (hspread : 4 * (-a4) ^ 2 - 10 * a3 < 67)
    (hsplits :
      (integerPolynomialReal [a3, 4 * a4, 10]).Splits)
    (hseparable :
      (integerPolynomialReal [a3, 4 * a4, 10]).Separable) :
    ∃ entry ∈ degreeFiveStageThreeEntries,
      entry.a4 = a4 ∧ entry.a3 = a3 := by
  interval_cases a4 <;> interval_cases a3 <;>
    norm_num [degreeFiveStageThreeEntries] at * <;> try omega
  all_goals
    first
    | exact (degreeFive_badTopPair_not_splits hsplits).elim
    | exact (degreeFive_badTopPair_not_separable hseparable).elim

/-- Every sharpened quintic Hunter candidate occurs in one of the twenty
generated third-derivative rows. -/
theorem degreeFive_minimumHunterCandidate_stageThree_complete
    {f : ℤ[X]} (h : HunterPolynomialCandidate 5 67 f) :
    ∃ entry ∈ degreeFiveStageThreeEntries,
      entry.a4 = f.coeff 4 ∧ entry.a3 = f.coeff 3 := by
  have hbounds := degreeFive_minimumHunter_topCoefficient_bounds h
  let s1 : ℤ := -f.coeff 4
  let s2 : ℤ := f.coeff 3
  have hsum := hunter_roots_sum_sq_eq_coefficients
    5 (by norm_num) f h.1 h.2.2.1 h.2.2.2.1
  change ((((f.map (algebraMap ℤ ℝ)).roots).map
    fun x => x ^ 2).sum) = (s1 : ℝ) ^ 2 - 2 * (s2 : ℝ) at hsum
  have hsumNonneg :
      0 ≤ (((f.map (algebraMap ℤ ℝ)).roots).map
        fun x => x ^ 2).sum := by
    apply Multiset.sum_nonneg
    intro y hy
    obtain ⟨x, _, rfl⟩ := Multiset.mem_map.mp hy
    exact sq_nonneg x
  rw [hsum] at hsumNonneg
  have htwiceReal : (2 : ℝ) * (s2 : ℝ) ≤ (s1 : ℝ) ^ 2 := by
    linarith
  have htwice : 2 * s2 ≤ s1 ^ 2 := by
    exact_mod_cast htwiceReal
  have hspreadReal := h.2.2.2.2.2.2
  change (((generalSpread 5 s1 s2 : ℤ) : ℝ)) < 67 at hspreadReal
  have hspread : 4 * s1 ^ 2 - 10 * s2 < (67 : ℤ) := by
    have hinterval : generalSpread 5 s1 s2 < (67 : ℤ) := by
      exact_mod_cast hspreadReal
    simp only [generalSpread] at hinterval
    norm_num at hinterval
    have heq :
        (5 : ℤ) * (s1 ^ 2 - 2 * s2) - s1 ^ 2 =
          4 * s1 ^ 2 - 10 * s2 := by
      ring
    rwa [heq] at hinterval
  let p : ℝ[X] := f.map (algebraMap ℤ ℝ)
  have hpdegree : p.natDegree = 5 := by
    dsimp [p]
    rw [Polynomial.natDegree_map_eq_of_injective
      (Int.cast_injective : Function.Injective (algebraMap ℤ ℝ)),
      h.2.2.1]
  have hstageEq : voightDerivativeStage p 3 =
      integerPolynomialReal
        [f.coeff 3, 4 * f.coeff 4, 10] := by
    simpa [p] using
      degreeFive_thirdDerivativeStage_eq h.1 h.2.2.1
  have hstageSplits :
      (integerPolynomialReal
        [f.coeff 3, 4 * f.coeff 4, 10]).Splits := by
    rw [← hstageEq]
    exact voightDerivativeStage_splits h.2.2.2.1 3
  have hpseparable : p.Separable := by
    simpa [p] using hunterPolynomialCandidate_separable_real h
  have hstageSeparable :
      (integerPolynomialReal
        [f.coeff 3, 4 * f.coeff 4, 10]).Separable := by
    rw [← hstageEq]
    exact voightDerivativeStage_separable h.2.2.2.1 hpseparable
      (by rw [hpdegree]; norm_num)
  apply degreeFiveStageThree_exists_entry_of_bounds
    hbounds.1 hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2
  · simpa [s1, s2] using htwice
  · simpa [s1, s2] using hspread
  · exact hstageSplits
  · exact hstageSeparable

/-- Once the top pair is identified, the next coefficient belongs to the
exact finite interval recorded for that row. -/
theorem degreeFive_minimumHunterCandidate_a2_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 5 67 f)
    (entry : DegreeFiveStageThreeEntry)
    (hentry : entry ∈ degreeFiveStageThreeEntries)
    (ha4 : entry.a4 = f.coeff 4)
    (ha3 : entry.a3 = f.coeff 3) :
    f.coeff 2 ∈ entry.a2Candidates := by
  have hvalid : entry.Valid :=
    (List.forall_iff_forall_mem.mp
      degreeFiveStageThreeEntries_valid) entry hentry
  let p : ℝ[X] := f.map (algebraMap ℤ ℝ)
  let q : ℝ[X] := integerPolynomialReal
    [f.coeff 2, 3 * entry.a3, 6 * entry.a4, 10]
  let r : ℝ[X] := integerPolynomialReal entry.derivativeCoefficients
  have hpdegree : p.natDegree = 5 := by
    dsimp [p]
    rw [Polynomial.natDegree_map_eq_of_injective
      (Int.cast_injective : Function.Injective (algebraMap ℤ ℝ)),
      h.2.2.1]
  have hpseparable : p.Separable := by
    simpa [p] using hunterPolynomialCandidate_separable_real h
  have hqEq : q = voightDerivativeStage p 2 := by
    symm
    simpa [p, q, ha4, ha3] using
      degreeFive_secondDerivativeStage_eq h.1 h.2.2.1
  have hqsplit : q.Splits := by
    rw [hqEq]
    exact voightDerivativeStage_splits h.2.2.2.1 2
  have hqseparable : q.Separable := by
    rw [hqEq]
    exact voightDerivativeStage_separable h.2.2.2.1 hpseparable
      (by rw [hpdegree]; norm_num)
  have hqdegree : q.natDegree = 3 := by
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
  have hrdegree : r.natDegree = 2 :=
    integerPolynomial_natDegree_of_generalRootIntervals
      hvalid.2.1 hvalid.2.2.1
  have hqderivEq : q.derivative = C 3 * r := by
    simpa [q, r,
      DegreeFiveStageThreeEntry.derivativeCoefficients] using
      degreeFive_cubic_derivative_eq
        (f.coeff 2) entry.a3 entry.a4
  let i0 : Fin r.natDegree := ⟨0, by rw [hrdegree]; norm_num⟩
  let i1 : Fin r.natDegree := ⟨1, by rw [hrdegree]; norm_num⟩
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
  let firstIndex : Fin entry.rootIntervals.length :=
    ⟨0, by simp [DegreeFiveStageThreeEntry.rootIntervals]⟩
  let secondIndex : Fin entry.rootIntervals.length :=
    ⟨1, by simp [DegreeFiveStageThreeEntry.rootIntervals]⟩
  have hfirstMem : voightSortedRoot r hrsplit i0 ∈
      Set.Icc (entry.firstRoot.lower : ℝ)
        (entry.firstRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid firstIndex
    simpa [r, i0, firstIndex,
      DegreeFiveStageThreeEntry.rootIntervals] using hmem
  have hsecondMem : voightSortedRoot r hrsplit i1 ∈
      Set.Icc (entry.secondRoot.lower : ℝ)
        (entry.secondRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid secondIndex
    simpa [r, i1, secondIndex,
      DegreeFiveStageThreeEntry.rootIntervals] using hmem
  have hfirstSign :
      0 ≤ q.eval (voightSortedRoot r hrsplit i0) := by
    have hsign :=
      eval_sign_at_derivativeSortedRoot_of_leadingCoeff_pos
        hqsplit hqlead hqseparable qi0
    rw [hrootEq0] at hsign
    simpa [hqdegree, qi0, i0] using hsign
  have hsecondSign :
      q.eval (voightSortedRoot r hrsplit i1) ≤ 0 := by
    have hsign :=
      eval_sign_at_derivativeSortedRoot_of_leadingCoeff_pos
        hqsplit hqlead hqseparable qi1
    rw [hrootEq1] at hsign
    norm_num [hqdegree, qi1, i1] at hsign
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
  apply mem_cubicTranslationCandidates_of_signs
    entry.baseCoefficients (-10) 10 entry.firstRoot entry.secondRoot
    (by
      have hforall := (List.forall_iff_forall_mem.mp
        hvalid.2.2.2.2.1) entry.firstRoot
        (by simp [DegreeFiveStageThreeEntry.rootIntervals])
      exact hforall.1.le)
    (by
      have hforall := (List.forall_iff_forall_mem.mp
        hvalid.2.2.2.2.1) entry.secondRoot
        (by simp [DegreeFiveStageThreeEntry.rootIntervals])
      exact hforall.1.le)
    (voightSortedRoot r hrsplit i0)
    (voightSortedRoot r hrsplit i1)
    hfirstMem hsecondMem (f.coeff 2)
  · simpa [q, DegreeFiveStageThreeEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval] using hleftSign
  · simpa [q, DegreeFiveStageThreeEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hfirstSign
  · simpa [q, DegreeFiveStageThreeEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hsecondSign
  · simpa [q, DegreeFiveStageThreeEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hrightSign

/-- Complete first recursion frontier: every sharpened Hunter quintic has a
generated top row and its actual `a2` is one of that row's certified values. -/
theorem degreeFive_minimumHunterCandidate_stageThree_frontier_complete
    {f : ℤ[X]} (h : HunterPolynomialCandidate 5 67 f) :
    ∃ entry ∈ degreeFiveStageThreeEntries,
      entry.a4 = f.coeff 4 ∧ entry.a3 = f.coeff 3 ∧
        f.coeff 2 ∈ entry.a2Candidates := by
  obtain ⟨entry, hentry, ha4, ha3⟩ :=
    degreeFive_minimumHunterCandidate_stageThree_complete h
  exact ⟨entry, hentry, ha4, ha3,
    degreeFive_minimumHunterCandidate_a2_mem
      h entry hentry ha4 ha3⟩

end

end TraceEuclidean
