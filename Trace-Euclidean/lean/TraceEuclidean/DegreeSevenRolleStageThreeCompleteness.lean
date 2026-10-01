import TraceEuclidean.DegreeSevenRolleStageThree
import TraceEuclidean.DegreeSevenMinimumReduction

/-!
# Completeness of the first degree-seven Rolle stage

This module connects the generated fifty-four-row certificate to every
degree-seven Hunter candidate below discriminant `20134393`.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

/-- An irreducible integral Hunter polynomial remains separable after mapping
to the reals, in every degree and at every spread bound. -/
theorem hunterPolynomialCandidate_separable_real_general
    {d : ℕ} {B : ℝ} {f : ℤ[X]}
    (h : HunterPolynomialCandidate d B f) :
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

/-- The degree-seven Hunter radius is strictly inside the integral endpoints
used by the Rolle certificates. -/
theorem degreeSevenMinimum_hunterRootBound_lt :
    hunterRootBound 7 194 < 16 := by
  rw [hunterRootBound]
  norm_num [max_eq_left]
  have hsqrtNonneg : 0 ≤ Real.sqrt (243 : ℝ) :=
    Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt (243 : ℝ)) ^ 2 = 243 := by
    rw [Real.sq_sqrt]
    norm_num
  nlinarith

/-- Every root of a sharpened septic Hunter candidate lies strictly between
the integral endpoints used by the generated Rolle certificates. -/
theorem degreeSeven_minimumHunterCandidate_root_bounds
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f) :
    ∀ z ∈ (f.map (algebraMap ℤ ℝ)).roots,
      (-16 : ℝ) < z ∧ z < 16 := by
  intro z hz
  have hnorm := hunterPolynomialCandidate_root_bound
    (d := 7) (B := 194) (by norm_num) h z hz
  have hnorm' : ‖z‖ < (16 : ℝ) :=
    hnorm.trans_lt degreeSevenMinimum_hunterRootBound_lt
  simpa [Real.norm_eq_abs, abs_lt] using hnorm'

/-- The normalized fifth derivative of a monic septic has the dense
quadratic coefficient list used by the generated certificates. -/
theorem degreeSeven_fifthDerivativeStage_eq
    {f : ℤ[X]} (hmonic : f.Monic) (hdegree : f.natDegree = 7) :
    voightDerivativeStage (f.map (algebraMap ℤ ℝ)) 5 =
      integerPolynomialReal
        [f.coeff 5, 6 * f.coeff 6, 21] := by
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
    have hcoeff : f.coeff 7 = 1 := by
      rw [← hdegree]
      exact hmonic.coeff_natDegree
    norm_num [hcoeff]
  have hm3 : 3 ≤ m := by omega
  have hright :
      [f.coeff 5, 6 * f.coeff 6, 21].getD m 0 = 0 := by
    rw [List.getD_eq_default]
    simp
    omega
  rw [hright, map_zero]
  have hcoeff : f.coeff (m + 5) = 0 := by
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    rw [hdegree]
    omega
  rw [hcoeff, map_zero]
  ring

/-- The normalized fourth derivative is the cubic used to bound `a4`. -/
theorem degreeSeven_fourthDerivativeStage_eq
    {f : ℤ[X]} (hmonic : f.Monic) (hdegree : f.natDegree = 7) :
    voightDerivativeStage (f.map (algebraMap ℤ ℝ)) 4 =
      integerPolynomialReal
        [f.coeff 4, 5 * f.coeff 5, 15 * f.coeff 6, 35] := by
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
    have hcoeff : f.coeff 7 = 1 := by
      rw [← hdegree]
      exact hmonic.coeff_natDegree
    norm_num [hcoeff]
  have hm4 : 4 ≤ m := by omega
  have hright :
      [f.coeff 4, 5 * f.coeff 5, 15 * f.coeff 6, 35].getD m 0 = 0 := by
    rw [List.getD_eq_default]
    simp
    omega
  rw [hright, map_zero]
  have hcoeff : f.coeff (m + 4) = 0 := by
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    rw [hdegree]
    omega
  rw [hcoeff, map_zero]
  ring

/-- The derivative of the cubic stage is five times the quadratic stage. -/
theorem degreeSeven_cubic_derivative_eq
    (a4 a5 a6 : ℤ) :
    (integerPolynomialReal
      [a4, 5 * a5, 15 * a6, 35]).derivative =
      C 5 * integerPolynomialReal [a5, 6 * a6, 21] := by
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

/-- A quadratic with negative discriminant cannot split over the reals. -/
private theorem degreeSeven_negativeDiscriminant_not_splits
    (b c : ℤ) (hdisc : (b : ℝ) ^ 2 < 84 * (c : ℝ)) :
    ¬(integerPolynomialReal [c, b, 21]).Splits := by
  intro hsplits
  let p := integerPolynomialReal [c, b, 21]
  have hdegree : p.natDegree = 2 := by
    apply integerPolynomial_natDegree_of_generalRootIntervals
    · norm_num
    · norm_num
  have hp0 : p ≠ 0 := by
    intro hp
    rw [hp] at hdegree
    norm_num at hdegree
  have hcard : p.roots.card = p.natDegree :=
    Polynomial.splits_iff_card_roots.mp hsplits
  have hroots : p.roots ≠ 0 := by
    intro hz
    rw [hz] at hcard
    simp [hdegree] at hcard
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hroots
  have heval : p.eval x = 0 := (Polynomial.mem_roots hp0).mp hx
  have hsquare : 0 ≤ (42 * x + (b : ℝ)) ^ 2 := sq_nonneg _
  norm_num [p, integerPolynomialReal,
    DensePolynomial.eval_toPolynomial,
    DensePolynomial.eval] at heval
  nlinarith

private theorem degreeSeven_badTopPair_one_not_splits :
    ¬(integerPolynomialReal [4, -18, 21]).Splits := by
  apply degreeSeven_negativeDiscriminant_not_splits
  norm_num

private theorem degreeSeven_badTopPair_two_not_splits :
    ¬(integerPolynomialReal [2, -12, 21]).Splits := by
  apply degreeSeven_negativeDiscriminant_not_splits
  norm_num

private theorem degreeSeven_badTopPair_not_separable :
    ¬(integerPolynomialReal [0, 0, 21]).Separable := by
  intro hseparable
  have hnodup := Polynomial.nodup_roots hseparable
  have heq : integerPolynomialReal [0, 0, 21] =
      C (21 : ℝ) * X ^ 2 := by
    rw [integerPolynomialReal]
    norm_num [DensePolynomial.toPolynomial]
    have htwentyOne : (21 : ℝ[X]) = C (21 : ℝ) :=
      (Polynomial.C_ofNat 21).symm
    rw [htwentyOne]
    ring
  rw [heq, Polynomial.roots_C_mul _ (by norm_num),
    Polynomial.roots_X_pow] at hnodup
  rw [Multiset.nodup_iff_count_le_one] at hnodup
  have hcount := hnodup 0
  rw [Multiset.count_nsmul] at hcount
  norm_num at hcount

/- Exact finite completeness of the generated septic top-coefficient table. -/
set_option maxHeartbeats 0 in
theorem degreeSevenStageThree_exists_entry_of_bounds
    {a6 a5 : ℤ}
    (ha6Lower : -3 ≤ a6) (ha6Upper : a6 ≤ 0)
    (ha5Lower : -13 ≤ a5) (ha5Upper : a5 ≤ 4)
    (hsum : 2 * a5 ≤ (-a6) ^ 2)
    (hspread : 6 * (-a6) ^ 2 - 14 * a5 < 194)
    (hsplits :
      (integerPolynomialReal [a5, 6 * a6, 21]).Splits)
    (hseparable :
      (integerPolynomialReal [a5, 6 * a6, 21]).Separable) :
    ∃ entry ∈ degreeSevenStageThreeEntries,
      entry.a6 = a6 ∧ entry.a5 = a5 := by
  interval_cases a6 <;> interval_cases a5 <;>
    norm_num [degreeSevenStageThreeEntries] at * <;> try omega
  all_goals
    first
    | exact (degreeSeven_badTopPair_one_not_splits hsplits).elim
    | exact (degreeSeven_badTopPair_two_not_splits hsplits).elim
    | exact (degreeSeven_badTopPair_not_separable hseparable).elim

/-- Every sharpened septic Hunter candidate occurs in one generated
quadratic derivative row. -/
theorem degreeSeven_minimumHunterCandidate_stageThree_complete
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f) :
    ∃ entry ∈ degreeSevenStageThreeEntries,
      entry.a6 = f.coeff 6 ∧ entry.a5 = f.coeff 5 := by
  have ha6 := degreeSevenMinimum_traceCoefficient_bounds h
  have ha5 := degreeSevenMinimum_secondCoefficient_bounds h
  let s1 : ℤ := -f.coeff 6
  let s2 : ℤ := f.coeff 5
  have hsum := hunter_roots_sum_sq_eq_coefficients
    7 (by norm_num) f h.1 h.2.2.1 h.2.2.2.1
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
  change (((generalSpread 7 s1 s2 : ℤ) : ℝ)) < 194 at hspreadReal
  have hspreadInt : generalSpread 7 s1 s2 < (194 : ℤ) := by
    exact_mod_cast hspreadReal
  have hspread : 6 * s1 ^ 2 - 14 * s2 < (194 : ℤ) := by
    calc
      6 * s1 ^ 2 - 14 * s2 = generalSpread 7 s1 s2 := by
        simp [generalSpread]
        ring
      _ < 194 := hspreadInt
  let p : ℝ[X] := f.map (algebraMap ℤ ℝ)
  have hpdegree : p.natDegree = 7 := by
    dsimp [p]
    rw [Polynomial.natDegree_map_eq_of_injective
      (Int.cast_injective : Function.Injective (algebraMap ℤ ℝ)),
      h.2.2.1]
  have hstageEq : voightDerivativeStage p 5 =
      integerPolynomialReal
        [f.coeff 5, 6 * f.coeff 6, 21] := by
    simpa [p] using
      degreeSeven_fifthDerivativeStage_eq h.1 h.2.2.1
  have hstageSplits :
      (integerPolynomialReal
        [f.coeff 5, 6 * f.coeff 6, 21]).Splits := by
    rw [← hstageEq]
    exact voightDerivativeStage_splits h.2.2.2.1 5
  have hpseparable : p.Separable := by
    simpa [p] using hunterPolynomialCandidate_separable_real_general h
  have hstageSeparable :
      (integerPolynomialReal
        [f.coeff 5, 6 * f.coeff 6, 21]).Separable := by
    rw [← hstageEq]
    exact voightDerivativeStage_separable h.2.2.2.1 hpseparable
      (by rw [hpdegree]; norm_num)
  apply degreeSevenStageThree_exists_entry_of_bounds
    ha6.1 ha6.2 ha5.1 ha5.2
  · simpa [s1, s2] using htwice
  · simpa [s1, s2] using hspread
  · exact hstageSplits
  · exact hstageSeparable

/-- Once the top pair is identified, the next coefficient belongs to the
exact finite interval recorded for that row. -/
theorem degreeSeven_minimumHunterCandidate_a4_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (entry : DegreeSevenStageThreeEntry)
    (hentry : entry ∈ degreeSevenStageThreeEntries)
    (ha6 : entry.a6 = f.coeff 6)
    (ha5 : entry.a5 = f.coeff 5) :
    f.coeff 4 ∈ entry.a4Candidates := by
  have hvalid : entry.Valid :=
    (List.forall_iff_forall_mem.mp
      degreeSevenStageThreeEntries_valid) entry hentry
  let p : ℝ[X] := f.map (algebraMap ℤ ℝ)
  let q : ℝ[X] := integerPolynomialReal
    [f.coeff 4, 5 * entry.a5, 15 * entry.a6, 35]
  let r : ℝ[X] := integerPolynomialReal entry.derivativeCoefficients
  have hpdegree : p.natDegree = 7 := by
    dsimp [p]
    rw [Polynomial.natDegree_map_eq_of_injective
      (Int.cast_injective : Function.Injective (algebraMap ℤ ℝ)),
      h.2.2.1]
  have hpseparable : p.Separable := by
    simpa [p] using hunterPolynomialCandidate_separable_real_general h
  have hqEq : q = voightDerivativeStage p 4 := by
    symm
    simpa [p, q, ha6, ha5] using
      degreeSeven_fourthDerivativeStage_eq h.1 h.2.2.1
  have hqsplit : q.Splits := by
    rw [hqEq]
    exact voightDerivativeStage_splits h.2.2.2.1 4
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
  have hrdegree : r.natDegree = 2 :=
    integerPolynomial_natDegree_of_generalRootIntervals
      hvalid.2.1 hvalid.2.2.1
  have hqderivEq : q.derivative = C 5 * r := by
    simpa [q, r,
      DegreeSevenStageThreeEntry.derivativeCoefficients] using
      degreeSeven_cubic_derivative_eq
        (f.coeff 4) entry.a5 entry.a6
  let i0 : Fin r.natDegree := ⟨0, by rw [hrdegree]; norm_num⟩
  let i1 : Fin r.natDegree := ⟨1, by rw [hrdegree]; norm_num⟩
  let qi0 : Fin q.derivative.natDegree :=
    ⟨i0, by
      rw [hqderivEq, Polynomial.natDegree_C_mul
        (by norm_num : (5 : ℝ) ≠ 0)]
      exact i0.isLt⟩
  let qi1 : Fin q.derivative.natDegree :=
    ⟨i1, by
      rw [hqderivEq, Polynomial.natDegree_C_mul
        (by norm_num : (5 : ℝ) ≠ 0)]
      exact i1.isLt⟩
  have hrootEq0 :
      voightSortedRoot q.derivative
          (splits_derivative_of_splits_real hqsplit) qi0 =
        voightSortedRoot r hrsplit i0 := by
    simpa [qi0] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (5 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hqsplit)
        hrsplit hqderivEq i0
  have hrootEq1 :
      voightSortedRoot q.derivative
          (splits_derivative_of_splits_real hqsplit) qi1 =
        voightSortedRoot r hrsplit i1 := by
    simpa [qi1] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (5 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hqsplit)
        hrsplit hqderivEq i1
  let firstIndex : Fin entry.rootIntervals.length :=
    ⟨0, by simp [DegreeSevenStageThreeEntry.rootIntervals]⟩
  let secondIndex : Fin entry.rootIntervals.length :=
    ⟨1, by simp [DegreeSevenStageThreeEntry.rootIntervals]⟩
  have hfirstMem : voightSortedRoot r hrsplit i0 ∈
      Set.Icc (entry.firstRoot.lower : ℝ)
        (entry.firstRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid firstIndex
    simpa [r, i0, firstIndex,
      DegreeSevenStageThreeEntry.rootIntervals] using hmem
  have hsecondMem : voightSortedRoot r hrsplit i1 ∈
      Set.Icc (entry.secondRoot.lower : ℝ)
        (entry.secondRoot.upper : ℝ) := by
    have hmem := sortedRoot_mem_interval_of_generalRootIntervals
      hvalid secondIndex
    simpa [r, i1, secondIndex,
      DegreeSevenStageThreeEntry.rootIntervals] using hmem
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
  have hleftSign : q.eval (-16) ≤ 0 := by
    have hsign :=
      eval_sign_left_of_all_roots_of_leadingCoeff_pos
        hqsplit hqlead (-16) (by
          intro y hy
          exact (hqbounds y hy).1.le)
    norm_num [hqdegree] at hsign
    linarith
  have hrightSign : 0 ≤ q.eval 16 :=
    eval_nonneg_right_of_all_roots_of_leadingCoeff_pos
      hqsplit hqlead 16 (by
        intro y hy
        exact (hqbounds y hy).2.le)
  apply mem_cubicTranslationCandidates_of_signs
    entry.baseCoefficients (-16) 16 entry.firstRoot entry.secondRoot
    (by
      have hforall := (List.forall_iff_forall_mem.mp
        hvalid.2.2.2.2.1) entry.firstRoot
        (by simp [DegreeSevenStageThreeEntry.rootIntervals])
      exact hforall.1.le)
    (by
      have hforall := (List.forall_iff_forall_mem.mp
        hvalid.2.2.2.2.1) entry.secondRoot
        (by simp [DegreeSevenStageThreeEntry.rootIntervals])
      exact hforall.1.le)
    (voightSortedRoot r hrsplit i0)
    (voightSortedRoot r hrsplit i1)
    hfirstMem hsecondMem (f.coeff 4)
  · simpa [q, DegreeSevenStageThreeEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval] using hleftSign
  · simpa [q, DegreeSevenStageThreeEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hfirstSign
  · simpa [q, DegreeSevenStageThreeEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hsecondSign
  · simpa [q, DegreeSevenStageThreeEntry.baseCoefficients,
      integerPolynomialReal, DensePolynomial.eval_toPolynomial,
      DensePolynomial.eval, add_comm] using hrightSign

/-- Complete first recursion frontier: every sharpened Hunter septic has a
generated top row and its actual `a4` is one of that row's certified values. -/
theorem degreeSeven_minimumHunterCandidate_stageThree_frontier_complete
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f) :
    ∃ entry ∈ degreeSevenStageThreeEntries,
      entry.a6 = f.coeff 6 ∧ entry.a5 = f.coeff 5 ∧
        f.coeff 4 ∈ entry.a4Candidates := by
  obtain ⟨entry, hentry, ha6, ha5⟩ :=
    degreeSeven_minimumHunterCandidate_stageThree_complete h
  exact ⟨entry, hentry, ha6, ha5,
    degreeSeven_minimumHunterCandidate_a4_mem
      h entry hentry ha6 ha5⟩

end

end TraceEuclidean
