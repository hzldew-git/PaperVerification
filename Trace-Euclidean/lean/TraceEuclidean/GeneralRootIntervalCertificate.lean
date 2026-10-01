import TraceEuclidean.RealRootIntervalCertificate
import TraceEuclidean.VoightRollePruning

/-!
# General rational root-interval certificates

The archived Voight rows are monic, but the derivative stages used by the
recursive enumeration generally are not.  This module checks exact rational
sign changes for an arbitrary dense integer polynomial with nonzero leading
coefficient.  A valid certificate locates every real root in a pairwise
disjoint rational interval, proves real splitting and separability, and
identifies each interval with the corresponding sorted root.

All executable checks use ordinary `decide`, so generated certificates reduce
inside Lean's kernel.
-/

namespace TraceEuclidean

open Polynomial

/-- The real polynomial represented by a dense list of integer coefficients
in increasing exponent order. -/
noncomputable def integerPolynomialReal (coefficients : List ℤ) : ℝ[X] :=
  (DensePolynomial.toPolynomial coefficients).map (Int.castRingHom ℝ)

/-- Exact rational evaluation of a dense integer polynomial. -/
def integerPolynomialRationalEval (coefficients : List ℤ) (x : ℚ) : ℚ :=
  DensePolynomial.eval (coefficients.map (Int.castRingHom ℚ)) x

/-- A complete family of ordered, pairwise disjoint sign-changing intervals
for an arbitrary dense integer polynomial. -/
def GeneralRationalRootIntervalCertificate.Valid (degree : ℕ) (coefficients : List ℤ)
    (intervals : List RationalRootInterval) : Prop :=
  0 < degree ∧
  coefficients.length = degree + 1 ∧
  coefficients.getLast?.getD 0 ≠ 0 ∧
  intervals.length = degree ∧
  intervals.Forall (fun interval =>
    interval.lower < interval.upper ∧
      integerPolynomialRationalEval coefficients interval.lower *
        integerPolynomialRationalEval coefficients interval.upper < 0) ∧
  intervals.Pairwise (fun left right => left.upper < right.lower)

instance (degree : ℕ) (coefficients : List ℤ)
    (intervals : List RationalRootInterval) :
    Decidable (GeneralRationalRootIntervalCertificate.Valid
      degree coefficients intervals) := by
  unfold GeneralRationalRootIntervalCertificate.Valid
  infer_instance

/-- Executable kernel check for a general rational root-interval certificate. -/
def GeneralRationalRootIntervalCertificate.check
    (degree : ℕ) (coefficients : List ℤ)
    (intervals : List RationalRootInterval) : Bool :=
  decide (GeneralRationalRootIntervalCertificate.Valid
    degree coefficients intervals)

/-- A successful executable check supplies the corresponding proposition. -/
theorem GeneralRationalRootIntervalCertificate.valid_of_check_eq_true
    {degree : ℕ} {coefficients : List ℤ}
    {intervals : List RationalRootInterval}
    (hcheck : GeneralRationalRootIntervalCertificate.check
      degree coefficients intervals = true) :
    GeneralRationalRootIntervalCertificate.Valid
      degree coefficients intervals := by
  exact of_decide_eq_true hcheck

private theorem integerPolynomial_eval_ratCast (coefficients : List ℤ) (x : ℚ) :
    (integerPolynomialReal coefficients).eval (x : ℝ) =
      (integerPolynomialRationalEval coefficients x : ℝ) := by
  rw [integerPolynomialReal, ← DensePolynomial.toPolynomial_map]
  rw [DensePolynomial.eval_toPolynomial]
  change DensePolynomial.eval
    (coefficients.map (Int.castRingHom ℝ)) (x : ℝ) = _
  rw [show coefficients.map (Int.castRingHom ℝ) =
      (coefficients.map (Int.castRingHom ℚ)).map
        (algebraMap ℚ ℝ) by simp]
  change DensePolynomial.eval
      ((coefficients.map (Int.castRingHom ℚ)).map
        (algebraMap ℚ ℝ)) (algebraMap ℚ ℝ x) =
    algebraMap ℚ ℝ (integerPolynomialRationalEval coefficients x)
  unfold integerPolynomialRationalEval
  exact DensePolynomial.eval_map (algebraMap ℚ ℝ)
    (coefficients.map (Int.castRingHom ℚ)) x

/-- The degree recorded by a valid general interval certificate is the actual
degree of its real polynomial. -/
theorem integerPolynomial_natDegree_of_generalRootIntervals
    {degree : ℕ} {coefficients : List ℤ}
    (hlength : coefficients.length = degree + 1)
    (hlast : coefficients.getLast?.getD 0 ≠ 0) :
    (integerPolynomialReal coefficients).natDegree = degree := by
  let q := DensePolynomial.toPolynomial coefficients
  have hqle : q.natDegree ≤ degree := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro exponent hexponent
    rw [DensePolynomial.coeff_toPolynomial,
      List.getD_eq_default coefficients 0]
    omega
  have hlast' := hlast
  rw [List.getLast?_eq_getElem?, hlength] at hlast'
  simp only [Nat.add_sub_cancel] at hlast'
  have hqcoeff : q.coeff degree ≠ 0 := by
    rw [DensePolynomial.coeff_toPolynomial,
      List.getD_eq_getElem?_getD]
    exact hlast'
  have hqdeg : q.natDegree = degree :=
    le_antisymm hqle (Polynomial.le_natDegree_of_ne_zero hqcoeff)
  rw [integerPolynomialReal, Polynomial.natDegree_map_eq_of_injective
    (Int.cast_injective : Function.Injective (Int.castRingHom ℝ))]
  exact hqdeg

private theorem exists_integerPolynomial_root_in_interval (coefficients : List ℤ)
    (interval : RationalRootInterval)
    (hinterval : interval.lower < interval.upper)
    (hsign : integerPolynomialRationalEval coefficients interval.lower *
      integerPolynomialRationalEval coefficients interval.upper < 0) :
    ∃ root : ℝ,
      root ∈ Set.Icc (interval.lower : ℝ) (interval.upper : ℝ) ∧
      (integerPolynomialReal coefficients).eval root = 0 := by
  have hlowerUpper : (interval.lower : ℝ) ≤ interval.upper := by
    exact_mod_cast hinterval.le
  have hsignReal :
      (integerPolynomialReal coefficients).eval (interval.lower : ℝ) *
        (integerPolynomialReal coefficients).eval (interval.upper : ℝ) < 0 := by
    rw [integerPolynomial_eval_ratCast, integerPolynomial_eval_ratCast]
    exact_mod_cast hsign
  have hzeroBetween :
      (0 : ℝ) ∈ Set.uIcc
        ((integerPolynomialReal coefficients).eval (interval.lower : ℝ))
        ((integerPolynomialReal coefficients).eval (interval.upper : ℝ)) := by
    rw [Set.mem_uIcc]
    rcases (mul_neg_iff.mp hsignReal) with h | h
    · exact Or.inr ⟨h.2.le, h.1.le⟩
    · exact Or.inl ⟨h.1.le, h.2.le⟩
  obtain ⟨root, hrootInterval, hroot⟩ :=
    (intermediate_value_uIcc
      (integerPolynomialReal coefficients).continuous.continuousOn hzeroBetween)
  rw [Set.uIcc_of_le hlowerUpper] at hrootInterval
  exact ⟨root, hrootInterval, hroot⟩

noncomputable def generalIntervalRoot {degree : ℕ}
    {coefficients : List ℤ}
    {intervals : List RationalRootInterval}
    (hvalid : GeneralRationalRootIntervalCertificate.Valid degree coefficients intervals)
    (i : Fin intervals.length) : ℝ :=
  Classical.choose (exists_integerPolynomial_root_in_interval coefficients (intervals.get i)
    ((List.forall_iff_forall_mem.mp hvalid.2.2.2.2.1) _
      (List.get_mem intervals i)).1
    ((List.forall_iff_forall_mem.mp hvalid.2.2.2.2.1) _
      (List.get_mem intervals i)).2)

theorem generalIntervalRoot_spec {degree : ℕ}
    {coefficients : List ℤ}
    {intervals : List RationalRootInterval}
    (hvalid : GeneralRationalRootIntervalCertificate.Valid degree coefficients intervals)
    (i : Fin intervals.length) :
    generalIntervalRoot hvalid i ∈
      Set.Icc ((intervals.get i).lower : ℝ)
        ((intervals.get i).upper : ℝ) ∧
    (integerPolynomialReal coefficients).eval
      (generalIntervalRoot hvalid i) = 0 := by
  exact Classical.choose_spec (exists_integerPolynomial_root_in_interval
    coefficients (intervals.get i)
    ((List.forall_iff_forall_mem.mp hvalid.2.2.2.2.1) _
      (List.get_mem intervals i)).1
    ((List.forall_iff_forall_mem.mp hvalid.2.2.2.2.1) _
      (List.get_mem intervals i)).2)

theorem generalIntervalRoot_strictMono {degree : ℕ}
    {coefficients : List ℤ}
    {intervals : List RationalRootInterval}
    (hvalid : GeneralRationalRootIntervalCertificate.Valid degree coefficients intervals) :
    StrictMono (generalIntervalRoot hvalid) := by
  intro i j hij
  have hsep := hvalid.2.2.2.2.2.rel_get_of_lt hij
  have hsepReal : ((intervals.get i).upper : ℝ) <
      (intervals.get j).lower := by exact_mod_cast hsep
  exact lt_of_le_of_lt (generalIntervalRoot_spec hvalid i).1.2
    (lt_of_lt_of_le hsepReal (generalIntervalRoot_spec hvalid j).1.1)

noncomputable def generalIntervalRoots {degree : ℕ}
    {coefficients : List ℤ}
    {intervals : List RationalRootInterval}
    (hvalid : GeneralRationalRootIntervalCertificate.Valid
      degree coefficients intervals) : List ℝ :=
  List.ofFn (generalIntervalRoot hvalid)

theorem generalIntervalRoots_coe_eq {degree : ℕ}
    {coefficients : List ℤ}
    {intervals : List RationalRootInterval}
    (hvalid : GeneralRationalRootIntervalCertificate.Valid degree coefficients intervals) :
    (↑(generalIntervalRoots hvalid) : Multiset ℝ) =
      (integerPolynomialReal coefficients).roots := by
  have hstrict := generalIntervalRoot_strictMono hvalid
  have hnodup : (↑(generalIntervalRoots hvalid) : Multiset ℝ).Nodup := by
    rw [Multiset.coe_nodup]
    exact List.nodup_ofFn_ofInjective hstrict.injective
  have hdegree := integerPolynomial_natDegree_of_generalRootIntervals
    hvalid.2.1 hvalid.2.2.1
  have hp0 : integerPolynomialReal coefficients ≠ 0 := by
    exact Polynomial.ne_zero_of_natDegree_gt (n := 0)
      (by rw [hdegree]; exact hvalid.1)
  have hle : (↑(generalIntervalRoots hvalid) : Multiset ℝ) ≤
      (integerPolynomialReal coefficients).roots := by
    rw [Multiset.le_iff_subset hnodup]
    intro z hz
    rw [Multiset.mem_coe] at hz
    rw [generalIntervalRoots, List.mem_iff_get] at hz
    obtain ⟨i, hiEq⟩ := hz
    have hiBound : i.val < intervals.length := by
      simpa [generalIntervalRoots] using i.isLt
    let i' : Fin intervals.length := ⟨i.val, hiBound⟩
    have hzEq : z = generalIntervalRoot hvalid i' := by
      simpa [generalIntervalRoots, i'] using hiEq.symm
    rw [hzEq, Polynomial.mem_roots hp0]
    exact (generalIntervalRoot_spec hvalid i').2
  apply Multiset.eq_of_le_of_card_le hle
  calc
    (integerPolynomialReal coefficients).roots.card ≤
        (integerPolynomialReal coefficients).natDegree :=
      Polynomial.card_roots' _
    _ = degree := hdegree
    _ = intervals.length := hvalid.2.2.2.1.symm
    _ = (↑(generalIntervalRoots hvalid) : Multiset ℝ).card := by
      simp [generalIntervalRoots]

/-- A complete general interval certificate proves real splitting. -/
theorem integerPolynomial_splits_of_generalRootIntervals
    {degree : ℕ} {coefficients : List ℤ}
    {intervals : List RationalRootInterval}
    (hvalid : GeneralRationalRootIntervalCertificate.Valid degree coefficients intervals) :
    (integerPolynomialReal coefficients).Splits := by
  rw [Polynomial.splits_iff_card_roots]
  rw [← generalIntervalRoots_coe_eq hvalid]
  simp [generalIntervalRoots,
    integerPolynomial_natDegree_of_generalRootIntervals
      hvalid.2.1 hvalid.2.2.1,
    hvalid.2.2.2.1]

/-- Pairwise disjoint sign-changing intervals also prove separability. -/
theorem integerPolynomial_separable_of_generalRootIntervals
    {degree : ℕ} {coefficients : List ℤ}
    {intervals : List RationalRootInterval}
    (hvalid : GeneralRationalRootIntervalCertificate.Valid
      degree coefficients intervals) :
    (integerPolynomialReal coefficients).Separable := by
  have hdegree := integerPolynomial_natDegree_of_generalRootIntervals
    hvalid.2.1 hvalid.2.2.1
  have hp0 : integerPolynomialReal coefficients ≠ 0 := by
    exact Polynomial.ne_zero_of_natDegree_gt (n := 0)
      (by rw [hdegree]; exact hvalid.1)
  apply (Polynomial.nodup_roots_iff_of_splits hp0
    (integerPolynomial_splits_of_generalRootIntervals hvalid)).mp
  rw [← generalIntervalRoots_coe_eq hvalid, Multiset.coe_nodup]
  exact List.nodup_ofFn_ofInjective
    (generalIntervalRoot_strictMono hvalid).injective

theorem generalIntervalRoots_eq_sorted {degree : ℕ}
    {coefficients : List ℤ}
    {intervals : List RationalRootInterval}
    (hvalid : GeneralRationalRootIntervalCertificate.Valid degree coefficients intervals) :
    generalIntervalRoots hvalid =
      voightSortedRoots (integerPolynomialReal coefficients) := by
  have hperm : (generalIntervalRoots hvalid).Perm
      (voightSortedRoots (integerPolynomialReal coefficients)) := by
    rw [← Multiset.coe_eq_coe]
    rw [generalIntervalRoots_coe_eq hvalid]
    exact Multiset.sort_eq (integerPolynomialReal coefficients).roots
      (fun x y : ℝ => x ≤ y) |>.symm
  apply hperm.eq_of_sortedLE
  · exact (List.sortedLT_ofFn_iff.mpr
      (generalIntervalRoot_strictMono hvalid)).sortedLE
  · rw [List.sortedLE_iff_pairwise]
    exact Multiset.pairwise_sort
      (integerPolynomialReal coefficients).roots (· ≤ ·)

/-- The `i`-th interval in a valid certificate contains the `i`-th sorted
root of the represented real polynomial. -/
theorem sortedRoot_mem_interval_of_generalRootIntervals
    {degree : ℕ} {coefficients : List ℤ}
    {intervals : List RationalRootInterval}
    (hvalid : GeneralRationalRootIntervalCertificate.Valid degree coefficients intervals)
    (i : Fin intervals.length) :
    let hp := integerPolynomial_splits_of_generalRootIntervals hvalid
    let ip : Fin (integerPolynomialReal coefficients).natDegree := ⟨i, by
      have hi := i.isLt
      have hdegree :=
        integerPolynomial_natDegree_of_generalRootIntervals
          hvalid.2.1 hvalid.2.2.1
      have hlength := hvalid.2.2.2.1
      omega⟩
    voightSortedRoot (integerPolynomialReal coefficients) hp ip ∈
      Set.Icc ((intervals.get i).lower : ℝ)
        ((intervals.get i).upper : ℝ) := by
  dsimp only
  have hlist := generalIntervalRoots_eq_sorted hvalid
  rw [voightSortedRoot]
  have hget :
      (voightSortedRoots (integerPolynomialReal coefficients)).get
          ⟨i, by
            have hi := i.isLt
            have hrootLength := voightSortedRoots_length
              (integerPolynomial_splits_of_generalRootIntervals hvalid)
            have hdegree :=
              integerPolynomial_natDegree_of_generalRootIntervals
              hvalid.2.1 hvalid.2.2.1
            have hlength := hvalid.2.2.2.1
            omega⟩ = generalIntervalRoot hvalid i := by
    have hchosenBound : i.val < (generalIntervalRoots hvalid).length := by
      simp only [generalIntervalRoots, List.length_ofFn]
      exact i.isLt
    have hsortedBound :
        i.val <
          (voightSortedRoots
            (integerPolynomialReal coefficients)).length := by
      rw [voightSortedRoots_length
        (integerPolynomial_splits_of_generalRootIntervals hvalid)]
      rw [integerPolynomial_natDegree_of_generalRootIntervals
        hvalid.2.1 hvalid.2.2.1]
      simpa [hvalid.2.2.2.1] using i.isLt
    have hgetD :=
      congrArg (fun roots : List ℝ => roots.getD i.val 0) hlist
    rw [List.getD_eq_getElem (generalIntervalRoots hvalid) 0 hchosenBound,
      List.getD_eq_getElem
        (voightSortedRoots (integerPolynomialReal coefficients))
        0 hsortedBound] at hgetD
    simpa [generalIntervalRoots] using hgetD.symm
  rw [hget]
  exact (generalIntervalRoot_spec hvalid i).1

end TraceEuclidean
