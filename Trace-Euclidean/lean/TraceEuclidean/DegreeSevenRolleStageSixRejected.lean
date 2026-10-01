import TraceEuclidean.DegreeSevenRolleStageSixFamilyCompact

/-!
# Rejected prefixes at the sixth degree-seven Rolle stage

A boundary value of `a2` can make the quintic second-derivative stage have a
multiple root.  The finite data layer records that common root exactly over
the rationals.  Such a row cannot occur for a Hunter polynomial because every
nonconstant derivative stage of a split separable real polynomial is again
separable.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

/-- An exact rational common-root witness for a rejected quintic prefix. -/
structure DegreeSevenStageSixMultipleRootWitness where
  a6 : ℤ
  a5 : ℤ
  a4 : ℤ
  a3 : ℤ
  a2 : ℤ
  commonRoot : ℚ
deriving DecidableEq, Repr

namespace DegreeSevenStageSixMultipleRootWitness

def coefficients (witness : DegreeSevenStageSixMultipleRootWitness) :
    List ℤ :=
  [witness.a2, 3 * witness.a3, 6 * witness.a4, 10 * witness.a5,
    15 * witness.a6, 21]

/-- Both the quintic and its formal derivative vanish at the recorded root. -/
def Valid (witness : DegreeSevenStageSixMultipleRootWitness) : Prop :=
  integerPolynomialRationalEval witness.coefficients witness.commonRoot = 0 ∧
    integerPolynomialRationalEval
      (DensePolynomial.derivative witness.coefficients) witness.commonRoot = 0

instance (witness : DegreeSevenStageSixMultipleRootWitness) :
    Decidable witness.Valid := by
  unfold Valid coefficients integerPolynomialRationalEval
  infer_instance

private theorem real_eval_ratCast (coefficients : List ℤ) (x : ℚ) :
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

/-- A valid common-root witness proves that its quintic is not separable. -/
theorem not_separable (witness : DegreeSevenStageSixMultipleRootWitness)
    (hvalid : witness.Valid) :
    ¬(integerPolynomialReal witness.coefficients).Separable := by
  intro hseparable
  have hroot :
      (integerPolynomialReal witness.coefficients).eval
          (witness.commonRoot : ℝ) = 0 := by
    rw [real_eval_ratCast]
    exact_mod_cast hvalid.1
  have hderivative :
      (integerPolynomialReal witness.coefficients).derivative.eval
          (witness.commonRoot : ℝ) = 0 := by
    rw [integerPolynomialReal_derivative, real_eval_ratCast]
    exact_mod_cast hvalid.2
  have hnonzero := hseparable.eval₂_derivative_ne_zero
    (RingHom.id ℝ) (x := (witness.commonRoot : ℝ))
  apply hnonzero
  · simpa using hroot
  · simpa using hderivative

end DegreeSevenStageSixMultipleRootWitness

/-- The normalized second derivative of a Hunter septic is separable. -/
theorem degreeSeven_secondDerivativeStage_separable
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f) :
    (integerPolynomialReal
      [f.coeff 2, 3 * f.coeff 3, 6 * f.coeff 4,
        10 * f.coeff 5, 15 * f.coeff 6, 21]).Separable := by
  let p : ℝ[X] := f.map (algebraMap ℤ ℝ)
  have hpdegree : p.natDegree = 7 := by
    dsimp [p]
    rw [Polynomial.natDegree_map_eq_of_injective
      (Int.cast_injective : Function.Injective (algebraMap ℤ ℝ)),
      h.2.2.1]
  have hpseparable : p.Separable := by
    simpa [p] using hunterPolynomialCandidate_separable_real_general h
  rw [← degreeSeven_secondDerivativeStage_eq h.1 h.2.2.1]
  exact voightDerivativeStage_separable h.2.2.2.1 hpseparable
    (by rw [hpdegree]; norm_num)

/-- The normalized second derivative of a Hunter septic splits over `ℝ`. -/
theorem degreeSeven_secondDerivativeStage_splits
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f) :
    (integerPolynomialReal
      [f.coeff 2, 3 * f.coeff 3, 6 * f.coeff 4,
        10 * f.coeff 5, 15 * f.coeff 6, 21]).Splits := by
  rw [← degreeSeven_secondDerivativeStage_eq h.1 h.2.2.1]
  exact voightDerivativeStage_splits h.2.2.2.1 2

/-- A valid multiple-root record cannot match the top coefficients of a
Hunter septic. -/
theorem degreeSeven_multipleRootWitness_not_hunter
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (witness : DegreeSevenStageSixMultipleRootWitness)
    (hvalid : witness.Valid)
    (ha6 : witness.a6 = f.coeff 6)
    (ha5 : witness.a5 = f.coeff 5)
    (ha4 : witness.a4 = f.coeff 4)
    (ha3 : witness.a3 = f.coeff 3)
    (ha2 : witness.a2 = f.coeff 2) : False := by
  apply witness.not_separable hvalid
  simpa [DegreeSevenStageSixMultipleRootWitness.coefficients,
    ha6, ha5, ha4, ha3, ha2] using
    degreeSeven_secondDerivativeStage_separable h

/-- The four ordered critical points of a quintic Stage Six prefix. -/
inductive DegreeSevenStageSixCriticalPoint where
  | first
  | second
  | third
  | fourth
deriving DecidableEq, Repr

namespace DegreeSevenStageSixCriticalPoint

def index : DegreeSevenStageSixCriticalPoint → Fin 4
  | first => ⟨0, by norm_num⟩
  | second => ⟨1, by norm_num⟩
  | third => ⟨2, by norm_num⟩
  | fourth => ⟨3, by norm_num⟩

def interval (point : DegreeSevenStageSixCriticalPoint)
    (parent : DegreeSevenStageFiveEntry) : RationalRootInterval :=
  match point with
  | first => parent.firstRoot
  | second => parent.secondRoot
  | third => parent.thirdRoot
  | fourth => parent.fourthRoot

end DegreeSevenStageSixCriticalPoint

/-- A certified critical-point sign contradiction for one rejected `a2`. -/
structure DegreeSevenStageSixCriticalSignWitness where
  parent : DegreeSevenStageFiveEntry
  a2 : ℤ
  point : DegreeSevenStageSixCriticalPoint
deriving DecidableEq, Repr

namespace DegreeSevenStageSixCriticalSignWitness

def coefficients (witness : DegreeSevenStageSixCriticalSignWitness) :
    List ℤ :=
  [witness.a2, 3 * witness.parent.a3, 6 * witness.parent.a4,
    10 * witness.parent.a5, 15 * witness.parent.a6, 21]

def criticalValueRange
    (witness : DegreeSevenStageSixCriticalSignWitness) :
    LeanCert.Core.IntervalRat :=
  integerPolynomialRootIntervalEval witness.coefficients
    (witness.point.interval witness.parent)

/-- The half-line of constant coefficients ruled out by a strict critical
sign.  The first and third critical points exclude smaller constants; the
second and fourth exclude larger constants. -/
def Excludes (witness : DegreeSevenStageSixCriticalSignWitness)
    (a2 : ℤ) : Prop :=
  match witness.point with
  | .first => a2 ≤ witness.a2
  | .second => witness.a2 ≤ a2
  | .third => a2 ≤ witness.a2
  | .fourth => witness.a2 ≤ a2

instance (witness : DegreeSevenStageSixCriticalSignWitness)
    (a2 : ℤ) : Decidable (witness.Excludes a2) := by
  unfold Excludes
  cases witness.point <;> infer_instance

/-- The parent isolates the derivative roots, and the selected interval has
the strict sign opposite to the one forced by five simple real roots. -/
def Valid (witness : DegreeSevenStageSixCriticalSignWitness) : Prop :=
  witness.parent.Valid ∧
    match witness.point with
    | .first => witness.criticalValueRange.hi < 0
    | .second => 0 < witness.criticalValueRange.lo
    | .third => witness.criticalValueRange.hi < 0
    | .fourth => 0 < witness.criticalValueRange.lo

instance (witness : DegreeSevenStageSixCriticalSignWitness) :
    Decidable witness.Valid := by
  unfold Valid DegreeSevenStageFiveEntry.Valid
  cases witness.point <;> infer_instance

/-- A valid critical-sign record rules out a split separable quintic. -/
theorem not_splits_and_separable
    (witness : DegreeSevenStageSixCriticalSignWitness)
    (hvalid : witness.Valid) :
    ¬((integerPolynomialReal witness.coefficients).Splits ∧
      (integerPolynomialReal witness.coefficients).Separable) := by
  rintro ⟨hqsplit, hqseparable⟩
  let q : ℝ[X] := integerPolynomialReal witness.coefficients
  let r : ℝ[X] :=
    integerPolynomialReal witness.parent.derivativeCoefficients
  have hparentValid : witness.parent.Valid := hvalid.1
  have hrsplit : r.Splits :=
    integerPolynomial_splits_of_generalRootIntervals hparentValid
  have hrdegree : r.natDegree = 4 :=
    integerPolynomial_natDegree_of_generalRootIntervals
      hparentValid.2.1 hparentValid.2.2.1
  have hqdegree : q.natDegree = 5 := by
    apply integerPolynomial_natDegree_of_generalRootIntervals
    · simp [coefficients]
    · norm_num [coefficients]
  have hqlead : 0 < q.leadingCoeff := by
    rw [Polynomial.leadingCoeff, hqdegree]
    change 0 < (integerPolynomialReal witness.coefficients).coeff 5
    rw [integerPolynomialReal, Polynomial.coeff_map,
      DensePolynomial.coeff_toPolynomial]
    norm_num [coefficients]
  have hqderivEq : q.derivative = C 3 * r := by
    simpa [q, r, coefficients,
      DegreeSevenStageFiveEntry.derivativeCoefficients] using
      degreeSeven_quintic_derivative_eq witness.a2
        witness.parent.a3 witness.parent.a4 witness.parent.a5 witness.parent.a6
  let ri : Fin r.natDegree :=
    ⟨witness.point.index, by rw [hrdegree]; exact witness.point.index.isLt⟩
  let qi : Fin q.derivative.natDegree :=
    ⟨ri, by
      rw [hqderivEq, Polynomial.natDegree_C_mul
        (by norm_num : (3 : ℝ) ≠ 0)]
      exact ri.isLt⟩
  have hrootEq :
      voightSortedRoot q.derivative
          (splits_derivative_of_splits_real hqsplit) qi =
        voightSortedRoot r hrsplit ri := by
    simpa [qi] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (3 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hqsplit)
        hrsplit hqderivEq ri
  let parentIndex : Fin witness.parent.rootIntervals.length :=
    ⟨witness.point.index, by
      cases witness.point <;>
        simp [DegreeSevenStageSixCriticalPoint.index,
          DegreeSevenStageFiveEntry.rootIntervals]⟩
  have hrootMemRaw :=
    sortedRoot_mem_interval_of_generalRootIntervals
      hparentValid parentIndex
  have hrootMem : voightSortedRoot r hrsplit ri ∈
      Set.Icc
        ((witness.point.interval witness.parent).lower : ℝ)
        ((witness.point.interval witness.parent).upper : ℝ) := by
    cases hpoint : witness.point <;>
      simpa [r, ri, parentIndex,
        DegreeSevenStageSixCriticalPoint.index,
        DegreeSevenStageSixCriticalPoint.interval,
        DegreeSevenStageFiveEntry.rootIntervals, hpoint] using hrootMemRaw
  have hordered :
      (witness.point.interval witness.parent).lower ≤
        (witness.point.interval witness.parent).upper := by
    have hintervals := List.forall_iff_forall_mem.mp
      hparentValid.2.2.2.2.1
    cases witness.point
    · exact (hintervals witness.parent.firstRoot
        (by simp [DegreeSevenStageFiveEntry.rootIntervals])).1.le
    · exact (hintervals witness.parent.secondRoot
        (by simp [DegreeSevenStageFiveEntry.rootIntervals])).1.le
    · exact (hintervals witness.parent.thirdRoot
        (by simp [DegreeSevenStageFiveEntry.rootIntervals])).1.le
    · exact (hintervals witness.parent.fourthRoot
        (by simp [DegreeSevenStageFiveEntry.rootIntervals])).1.le
  have hvalue : q.eval (voightSortedRoot r hrsplit ri) ∈
      witness.criticalValueRange := by
    exact integerPolynomial_eval_mem_rootInterval
      witness.coefficients (witness.point.interval witness.parent)
      hordered hrootMem
  have hsign :=
    eval_sign_at_derivativeSortedRoot_of_leadingCoeff_pos
      hqsplit hqlead hqseparable qi
  rw [hrootEq] at hsign
  have hqdegree' :
      (integerPolynomialReal witness.coefficients).natDegree = 5 := by
    simpa [q] using hqdegree
  rw [hqdegree'] at hsign
  simp only [LeanCert.Core.IntervalRat.mem_def] at hvalue
  cases hpoint : witness.point
  · have hwrongRat := hvalid.2
    simp only [hpoint] at hwrongRat
    have hwrong : (witness.criticalValueRange.hi : ℝ) < 0 := by
      exact_mod_cast hwrongRat
    norm_num [qi, ri, DegreeSevenStageSixCriticalPoint.index,
      hpoint] at hsign
    have hsign' : 0 ≤ q.eval (voightSortedRoot r hrsplit ri) := by
      simpa [q, ri, DegreeSevenStageSixCriticalPoint.index,
        hpoint] using hsign
    linarith
  · have hwrongRat := hvalid.2
    simp only [hpoint] at hwrongRat
    have hwrong : (0 : ℝ) < witness.criticalValueRange.lo := by
      exact_mod_cast hwrongRat
    norm_num [qi, ri, DegreeSevenStageSixCriticalPoint.index,
      hpoint] at hsign
    have hsign' : q.eval (voightSortedRoot r hrsplit ri) ≤ 0 := by
      simpa [q, ri, DegreeSevenStageSixCriticalPoint.index,
        hpoint] using hsign
    linarith
  · have hwrongRat := hvalid.2
    simp only [hpoint] at hwrongRat
    have hwrong : (witness.criticalValueRange.hi : ℝ) < 0 := by
      exact_mod_cast hwrongRat
    norm_num [qi, ri, DegreeSevenStageSixCriticalPoint.index,
      hpoint] at hsign
    have hsign' : 0 ≤ q.eval (voightSortedRoot r hrsplit ri) := by
      simpa [q, ri, DegreeSevenStageSixCriticalPoint.index,
        hpoint] using hsign
    linarith
  · have hwrongRat := hvalid.2
    simp only [hpoint] at hwrongRat
    have hwrong : (0 : ℝ) < witness.criticalValueRange.lo := by
      exact_mod_cast hwrongRat
    norm_num [qi, ri, DegreeSevenStageSixCriticalPoint.index,
      hpoint] at hsign
    have hsign' : q.eval (voightSortedRoot r hrsplit ri) ≤ 0 := by
      simpa [q, ri, DegreeSevenStageSixCriticalPoint.index,
        hpoint] using hsign
    linarith

private theorem criticalValueRange_lo_change
    (witness : DegreeSevenStageSixCriticalSignWitness) (a2 : ℤ) :
    ({ witness with a2 := a2 }).criticalValueRange.lo =
      witness.criticalValueRange.lo + ((a2 - witness.a2 : ℤ) : ℚ) := by
  simp [criticalValueRange, coefficients,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add]
  ring

private theorem criticalValueRange_hi_change
    (witness : DegreeSevenStageSixCriticalSignWitness) (a2 : ℤ) :
    ({ witness with a2 := a2 }).criticalValueRange.hi =
      witness.criticalValueRange.hi + ((a2 - witness.a2 : ℤ) : ℚ) := by
  simp [criticalValueRange, coefficients,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add]
  ring

/-- A strict critical-sign witness excludes an entire half-line of constant
coefficients, not only the value at which it was generated. -/
theorem not_splits_and_separable_of_excludes
    (witness : DegreeSevenStageSixCriticalSignWitness)
    (hvalid : witness.Valid) {a2 : ℤ} (hexcludes : witness.Excludes a2) :
    ¬((integerPolynomialReal
        [a2, 3 * witness.parent.a3, 6 * witness.parent.a4,
          10 * witness.parent.a5, 15 * witness.parent.a6, 21]).Splits ∧
      (integerPolynomialReal
        [a2, 3 * witness.parent.a3, 6 * witness.parent.a4,
          10 * witness.parent.a5, 15 * witness.parent.a6, 21]).Separable) := by
  let target : DegreeSevenStageSixCriticalSignWitness :=
    { witness with a2 := a2 }
  have htarget : target.Valid := by
    refine ⟨hvalid.1, ?_⟩
    cases hpoint : witness.point
    · have hle : a2 ≤ witness.a2 := by
        simpa [Excludes, hpoint] using hexcludes
      have hshift : ((a2 - witness.a2 : ℤ) : ℚ) ≤ 0 := by
        exact_mod_cast sub_nonpos.mpr hle
      have hrange : target.criticalValueRange.hi =
          witness.criticalValueRange.hi + ((a2 - witness.a2 : ℤ) : ℚ) := by
        simpa [target] using criticalValueRange_hi_change witness a2
      have hwrong : witness.criticalValueRange.hi < 0 := by
        simpa [Valid, hpoint] using hvalid.2
      change target.criticalValueRange.hi < 0
      linarith
    · have hle : witness.a2 ≤ a2 := by
        simpa [Excludes, hpoint] using hexcludes
      have hshift : (0 : ℚ) ≤ (a2 - witness.a2 : ℤ) := by
        exact_mod_cast sub_nonneg.mpr hle
      have hrange : target.criticalValueRange.lo =
          witness.criticalValueRange.lo + ((a2 - witness.a2 : ℤ) : ℚ) := by
        simpa [target] using criticalValueRange_lo_change witness a2
      have hwrong : (0 : ℚ) < witness.criticalValueRange.lo := by
        simpa [Valid, hpoint] using hvalid.2
      change 0 < target.criticalValueRange.lo
      linarith
    · have hle : a2 ≤ witness.a2 := by
        simpa [Excludes, hpoint] using hexcludes
      have hshift : ((a2 - witness.a2 : ℤ) : ℚ) ≤ 0 := by
        exact_mod_cast sub_nonpos.mpr hle
      have hrange : target.criticalValueRange.hi =
          witness.criticalValueRange.hi + ((a2 - witness.a2 : ℤ) : ℚ) := by
        simpa [target] using criticalValueRange_hi_change witness a2
      have hwrong : witness.criticalValueRange.hi < 0 := by
        simpa [Valid, hpoint] using hvalid.2
      change target.criticalValueRange.hi < 0
      linarith
    · have hle : witness.a2 ≤ a2 := by
        simpa [Excludes, hpoint] using hexcludes
      have hshift : (0 : ℚ) ≤ (a2 - witness.a2 : ℤ) := by
        exact_mod_cast sub_nonneg.mpr hle
      have hrange : target.criticalValueRange.lo =
          witness.criticalValueRange.lo + ((a2 - witness.a2 : ℤ) : ℚ) := by
        simpa [target] using criticalValueRange_lo_change witness a2
      have hwrong : (0 : ℚ) < witness.criticalValueRange.lo := by
        simpa [Valid, hpoint] using hvalid.2
      change 0 < target.criticalValueRange.lo
      linarith
  simpa [target, coefficients] using target.not_splits_and_separable htarget

end DegreeSevenStageSixCriticalSignWitness

/-- A valid critical-sign record cannot match the top coefficients of a Hunter
septic. -/
theorem degreeSeven_criticalSignWitness_not_hunter
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (witness : DegreeSevenStageSixCriticalSignWitness)
    (hvalid : witness.Valid)
    (ha6 : witness.parent.a6 = f.coeff 6)
    (ha5 : witness.parent.a5 = f.coeff 5)
    (ha4 : witness.parent.a4 = f.coeff 4)
    (ha3 : witness.parent.a3 = f.coeff 3)
    (ha2 : witness.a2 = f.coeff 2) : False := by
  apply witness.not_splits_and_separable hvalid
  constructor
  · simpa [DegreeSevenStageSixCriticalSignWitness.coefficients,
      ha6, ha5, ha4, ha3, ha2] using
      degreeSeven_secondDerivativeStage_splits h
  · simpa [DegreeSevenStageSixCriticalSignWitness.coefficients,
      ha6, ha5, ha4, ha3, ha2] using
      degreeSeven_secondDerivativeStage_separable h

/-- The half-line excluded by a valid critical-sign record contains no Hunter
septic with the same top coefficients. -/
theorem degreeSeven_criticalSignWitness_excludes_hunter
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (witness : DegreeSevenStageSixCriticalSignWitness)
    (hvalid : witness.Valid)
    (ha6 : witness.parent.a6 = f.coeff 6)
    (ha5 : witness.parent.a5 = f.coeff 5)
    (ha4 : witness.parent.a4 = f.coeff 4)
    (ha3 : witness.parent.a3 = f.coeff 3)
    (hexcludes : witness.Excludes (f.coeff 2)) : False := by
  apply witness.not_splits_and_separable_of_excludes hvalid hexcludes
  constructor
  · simpa [ha6, ha5, ha4, ha3] using
      degreeSeven_secondDerivativeStage_splits h
  · simpa [ha6, ha5, ha4, ha3] using
      degreeSeven_secondDerivativeStage_separable h

end

end TraceEuclidean
