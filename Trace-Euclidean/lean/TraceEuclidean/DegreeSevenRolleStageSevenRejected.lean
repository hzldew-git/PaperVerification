import TraceEuclidean.DegreeSevenRolleStageSevenCompleteness

/-!
# Rejected prefixes at the final degree-seven Rolle stage

The first derivative of a split separable septic is itself split and
separable.  An exact rational common root of that sextic and its derivative
therefore rules out the corresponding coefficient prefix.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

/-- An exact rational common-root witness for a rejected sextic prefix. -/
structure DegreeSevenStageSevenMultipleRootWitness where
  a6 : ℤ
  a5 : ℤ
  a4 : ℤ
  a3 : ℤ
  a2 : ℤ
  a1 : ℤ
  commonRoot : ℚ
deriving DecidableEq, Repr

namespace DegreeSevenStageSevenMultipleRootWitness

def coefficients (witness : DegreeSevenStageSevenMultipleRootWitness) :
    List ℤ :=
  [witness.a1, 2 * witness.a2, 3 * witness.a3, 4 * witness.a4,
    5 * witness.a5, 6 * witness.a6, 7]

/-- Both the sextic and its formal derivative vanish at the recorded root. -/
def Valid (witness : DegreeSevenStageSevenMultipleRootWitness) : Prop :=
  integerPolynomialRationalEval witness.coefficients witness.commonRoot = 0 ∧
    integerPolynomialRationalEval
      (DensePolynomial.derivative witness.coefficients)
        witness.commonRoot = 0

instance (witness : DegreeSevenStageSevenMultipleRootWitness) :
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

/-- A valid common-root witness proves that its sextic is not separable. -/
theorem not_separable
    (witness : DegreeSevenStageSevenMultipleRootWitness)
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

end DegreeSevenStageSevenMultipleRootWitness

/-- The normalized first derivative of a Hunter septic is separable. -/
theorem degreeSeven_firstDerivativeStage_separable
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f) :
    (integerPolynomialReal
      [f.coeff 1, 2 * f.coeff 2, 3 * f.coeff 3, 4 * f.coeff 4,
        5 * f.coeff 5, 6 * f.coeff 6, 7]).Separable := by
  let p : ℝ[X] := f.map (algebraMap ℤ ℝ)
  have hpdegree : p.natDegree = 7 := by
    dsimp [p]
    rw [Polynomial.natDegree_map_eq_of_injective
      (Int.cast_injective : Function.Injective (algebraMap ℤ ℝ)),
      h.2.2.1]
  have hpseparable : p.Separable := by
    simpa [p] using hunterPolynomialCandidate_separable_real_general h
  rw [← degreeSeven_firstDerivativeStage_eq h.1 h.2.2.1]
  exact voightDerivativeStage_separable h.2.2.2.1 hpseparable
    (by rw [hpdegree]; norm_num)

/-- The normalized first derivative of a Hunter septic splits over `ℝ`. -/
theorem degreeSeven_firstDerivativeStage_splits
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f) :
    (integerPolynomialReal
      [f.coeff 1, 2 * f.coeff 2, 3 * f.coeff 3, 4 * f.coeff 4,
        5 * f.coeff 5, 6 * f.coeff 6, 7]).Splits := by
  rw [← degreeSeven_firstDerivativeStage_eq h.1 h.2.2.1]
  exact voightDerivativeStage_splits h.2.2.2.1 1

/-- A valid multiple-root record cannot match the coefficients above `a0` of
a Hunter septic. -/
theorem degreeSeven_stageSevenMultipleRootWitness_not_hunter
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (witness : DegreeSevenStageSevenMultipleRootWitness)
    (hvalid : witness.Valid)
    (ha6 : witness.a6 = f.coeff 6)
    (ha5 : witness.a5 = f.coeff 5)
    (ha4 : witness.a4 = f.coeff 4)
    (ha3 : witness.a3 = f.coeff 3)
    (ha2 : witness.a2 = f.coeff 2)
    (ha1 : witness.a1 = f.coeff 1) : False := by
  apply witness.not_separable hvalid
  simpa [DegreeSevenStageSevenMultipleRootWitness.coefficients,
    ha6, ha5, ha4, ha3, ha2, ha1] using
    degreeSeven_firstDerivativeStage_separable h

/-- The five ordered critical points of a sextic Stage Seven prefix. -/
inductive DegreeSevenStageSevenCriticalPoint where
  | first
  | second
  | third
  | fourth
  | fifth
deriving DecidableEq, Repr

namespace DegreeSevenStageSevenCriticalPoint

def index : DegreeSevenStageSevenCriticalPoint → Fin 5
  | first => ⟨0, by norm_num⟩
  | second => ⟨1, by norm_num⟩
  | third => ⟨2, by norm_num⟩
  | fourth => ⟨3, by norm_num⟩
  | fifth => ⟨4, by norm_num⟩

def interval (point : DegreeSevenStageSevenCriticalPoint)
    (parent : DegreeSevenStageSixEntry) : RationalRootInterval :=
  match point with
  | first => parent.firstRoot
  | second => parent.secondRoot
  | third => parent.thirdRoot
  | fourth => parent.fourthRoot
  | fifth => parent.fifthRoot

end DegreeSevenStageSevenCriticalPoint

/-- A certified critical-point sign contradiction for one rejected `a1`. -/
structure DegreeSevenStageSevenCriticalSignWitness where
  parent : DegreeSevenStageSixEntry
  a1 : ℤ
  point : DegreeSevenStageSevenCriticalPoint
deriving DecidableEq, Repr

namespace DegreeSevenStageSevenCriticalSignWitness

def coefficients (witness : DegreeSevenStageSevenCriticalSignWitness) :
    List ℤ :=
  [witness.a1, 2 * witness.parent.a2, 3 * witness.parent.a3,
    4 * witness.parent.a4, 5 * witness.parent.a5,
    6 * witness.parent.a6, 7]

def criticalValueRange
    (witness : DegreeSevenStageSevenCriticalSignWitness) :
    LeanCert.Core.IntervalRat :=
  integerPolynomialRootIntervalEval witness.coefficients
    (witness.point.interval witness.parent)

/-- The parent isolates all derivative roots, while the chosen interval has
the strict sign opposite to the sign forced by six simple real roots. -/
def Valid (witness : DegreeSevenStageSevenCriticalSignWitness) : Prop :=
  witness.parent.Valid ∧
    match witness.point with
    | .first => 0 < witness.criticalValueRange.lo
    | .second => witness.criticalValueRange.hi < 0
    | .third => 0 < witness.criticalValueRange.lo
    | .fourth => witness.criticalValueRange.hi < 0
    | .fifth => 0 < witness.criticalValueRange.lo

instance (witness : DegreeSevenStageSevenCriticalSignWitness) :
    Decidable witness.Valid := by
  unfold Valid DegreeSevenStageSixEntry.Valid
  cases witness.point <;> infer_instance

/-- A valid critical-sign record rules out a split separable sextic. -/
theorem not_splits_and_separable
    (witness : DegreeSevenStageSevenCriticalSignWitness)
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
  have hrdegree : r.natDegree = 5 :=
    integerPolynomial_natDegree_of_generalRootIntervals
      hparentValid.2.1 hparentValid.2.2.1
  have hqdegree : q.natDegree = 6 := by
    apply integerPolynomial_natDegree_of_generalRootIntervals
    · simp [coefficients]
    · norm_num [coefficients]
  have hqlead : 0 < q.leadingCoeff := by
    rw [Polynomial.leadingCoeff, hqdegree]
    change 0 < (integerPolynomialReal witness.coefficients).coeff 6
    rw [integerPolynomialReal, Polynomial.coeff_map,
      DensePolynomial.coeff_toPolynomial]
    norm_num [coefficients]
  have hqderivEq : q.derivative = C 2 * r := by
    simpa [q, r, coefficients,
      DegreeSevenStageSixEntry.derivativeCoefficients] using
      degreeSeven_sextic_derivative_eq witness.a1 witness.parent.a2
        witness.parent.a3 witness.parent.a4 witness.parent.a5
        witness.parent.a6
  let ri : Fin r.natDegree :=
    ⟨witness.point.index, by
      rw [hrdegree]
      exact witness.point.index.isLt⟩
  let qi : Fin q.derivative.natDegree :=
    ⟨ri, by
      rw [hqderivEq, Polynomial.natDegree_C_mul
        (by norm_num : (2 : ℝ) ≠ 0)]
      exact ri.isLt⟩
  have hrootEq :
      voightSortedRoot q.derivative
          (splits_derivative_of_splits_real hqsplit) qi =
        voightSortedRoot r hrsplit ri := by
    simpa [qi] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (2 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hqsplit)
        hrsplit hqderivEq ri
  let parentIndex : Fin witness.parent.rootIntervals.length :=
    ⟨witness.point.index, by
      cases witness.point <;>
        simp [DegreeSevenStageSevenCriticalPoint.index,
          DegreeSevenStageSixEntry.rootIntervals]⟩
  have hrootMemRaw :=
    sortedRoot_mem_interval_of_generalRootIntervals
      hparentValid parentIndex
  have hrootMem : voightSortedRoot r hrsplit ri ∈
      Set.Icc
        ((witness.point.interval witness.parent).lower : ℝ)
        ((witness.point.interval witness.parent).upper : ℝ) := by
    cases hpoint : witness.point <;>
      simpa [r, ri, parentIndex,
        DegreeSevenStageSevenCriticalPoint.index,
        DegreeSevenStageSevenCriticalPoint.interval,
        DegreeSevenStageSixEntry.rootIntervals, hpoint] using hrootMemRaw
  have hordered :
      (witness.point.interval witness.parent).lower ≤
        (witness.point.interval witness.parent).upper := by
    have hintervals := List.forall_iff_forall_mem.mp
      hparentValid.2.2.2.2.1
    cases witness.point
    · exact (hintervals witness.parent.firstRoot
        (by simp [DegreeSevenStageSixEntry.rootIntervals])).1.le
    · exact (hintervals witness.parent.secondRoot
        (by simp [DegreeSevenStageSixEntry.rootIntervals])).1.le
    · exact (hintervals witness.parent.thirdRoot
        (by simp [DegreeSevenStageSixEntry.rootIntervals])).1.le
    · exact (hintervals witness.parent.fourthRoot
        (by simp [DegreeSevenStageSixEntry.rootIntervals])).1.le
    · exact (hintervals witness.parent.fifthRoot
        (by simp [DegreeSevenStageSixEntry.rootIntervals])).1.le
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
      (integerPolynomialReal witness.coefficients).natDegree = 6 := by
    simpa [q] using hqdegree
  rw [hqdegree'] at hsign
  simp only [LeanCert.Core.IntervalRat.mem_def] at hvalue
  cases hpoint : witness.point
  · have hwrongRat := hvalid.2
    simp only [hpoint] at hwrongRat
    have hwrong : (0 : ℝ) < witness.criticalValueRange.lo := by
      exact_mod_cast hwrongRat
    norm_num [qi, ri, DegreeSevenStageSevenCriticalPoint.index,
      hpoint] at hsign
    have hsign' : q.eval (voightSortedRoot r hrsplit ri) ≤ 0 := by
      simpa [q, ri, DegreeSevenStageSevenCriticalPoint.index,
        hpoint] using hsign
    linarith
  · have hwrongRat := hvalid.2
    simp only [hpoint] at hwrongRat
    have hwrong : (witness.criticalValueRange.hi : ℝ) < 0 := by
      exact_mod_cast hwrongRat
    norm_num [qi, ri, DegreeSevenStageSevenCriticalPoint.index,
      hpoint] at hsign
    have hsign' : 0 ≤ q.eval (voightSortedRoot r hrsplit ri) := by
      simpa [q, ri, DegreeSevenStageSevenCriticalPoint.index,
        hpoint] using hsign
    linarith
  · have hwrongRat := hvalid.2
    simp only [hpoint] at hwrongRat
    have hwrong : (0 : ℝ) < witness.criticalValueRange.lo := by
      exact_mod_cast hwrongRat
    norm_num [qi, ri, DegreeSevenStageSevenCriticalPoint.index,
      hpoint] at hsign
    have hsign' : q.eval (voightSortedRoot r hrsplit ri) ≤ 0 := by
      simpa [q, ri, DegreeSevenStageSevenCriticalPoint.index,
        hpoint] using hsign
    linarith
  · have hwrongRat := hvalid.2
    simp only [hpoint] at hwrongRat
    have hwrong : (witness.criticalValueRange.hi : ℝ) < 0 := by
      exact_mod_cast hwrongRat
    norm_num [qi, ri, DegreeSevenStageSevenCriticalPoint.index,
      hpoint] at hsign
    have hsign' : 0 ≤ q.eval (voightSortedRoot r hrsplit ri) := by
      simpa [q, ri, DegreeSevenStageSevenCriticalPoint.index,
        hpoint] using hsign
    linarith
  · have hwrongRat := hvalid.2
    simp only [hpoint] at hwrongRat
    have hwrong : (0 : ℝ) < witness.criticalValueRange.lo := by
      exact_mod_cast hwrongRat
    norm_num [qi, ri, DegreeSevenStageSevenCriticalPoint.index,
      hpoint] at hsign
    have hsign' : q.eval (voightSortedRoot r hrsplit ri) ≤ 0 := by
      simpa [q, ri, DegreeSevenStageSevenCriticalPoint.index,
        hpoint] using hsign
    linarith

end DegreeSevenStageSevenCriticalSignWitness

/-- A valid final-stage critical-sign record cannot match the coefficients
above `a0` of a Hunter septic. -/
theorem degreeSeven_stageSevenCriticalSignWitness_not_hunter
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (witness : DegreeSevenStageSevenCriticalSignWitness)
    (hvalid : witness.Valid)
    (ha6 : witness.parent.a6 = f.coeff 6)
    (ha5 : witness.parent.a5 = f.coeff 5)
    (ha4 : witness.parent.a4 = f.coeff 4)
    (ha3 : witness.parent.a3 = f.coeff 3)
    (ha2 : witness.parent.a2 = f.coeff 2)
    (ha1 : witness.a1 = f.coeff 1) : False := by
  apply witness.not_splits_and_separable hvalid
  constructor
  · simpa [DegreeSevenStageSevenCriticalSignWitness.coefficients,
      ha6, ha5, ha4, ha3, ha2, ha1] using
      degreeSeven_firstDerivativeStage_splits h
  · simpa [DegreeSevenStageSevenCriticalSignWitness.coefficients,
      ha6, ha5, ha4, ha3, ha2, ha1] using
      degreeSeven_firstDerivativeStage_separable h

end

end TraceEuclidean
