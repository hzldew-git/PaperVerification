import TraceEuclidean.DegreeSevenRolleStageSixBridge

/-!
# Parametric root certificates for the sixth degree-seven Rolle stage

For fixed coefficients `a6`, ..., `a3`, the quintic at the sixth Rolle stage
depends on `a2` only through its constant coefficient.  This module packages
one set of five rational root intervals for a whole integer interval of `a2`
values.  Alternating endpoint signs are checked only at the two extreme
values of `a2`; monotonicity in the constant coefficient then supplies an
ordinary Stage Six certificate for every integer in the interval.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

/-- One common five-root certificate for a closed interval of `a2` values. -/
structure DegreeSevenStageSixFamily where
  a6 : ℤ
  a5 : ℤ
  a4 : ℤ
  a3 : ℤ
  a2Lower : ℤ
  a2Upper : ℤ
  firstRoot : RationalRootInterval
  secondRoot : RationalRootInterval
  thirdRoot : RationalRootInterval
  fourthRoot : RationalRootInterval
  fifthRoot : RationalRootInterval
deriving DecidableEq, Repr

namespace DegreeSevenStageSixFamily

/-- The quintic coefficient list at a chosen constant coefficient. -/
def derivativeCoefficients (family : DegreeSevenStageSixFamily)
    (a2 : ℤ) : List ℤ :=
  [a2, 3 * family.a3, 6 * family.a4, 10 * family.a5,
    15 * family.a6, 21]

/-- The five intervals shared by the family. -/
def rootIntervals (family : DegreeSevenStageSixFamily) :
    List RationalRootInterval :=
  [family.firstRoot, family.secondRoot, family.thirdRoot,
    family.fourthRoot, family.fifthRoot]

/-- Expand a family at one value of `a2` into the ordinary Stage Six entry. -/
def toEntry (family : DegreeSevenStageSixFamily)
    (a2 : ℤ) : DegreeSevenStageSixEntry where
  a6 := family.a6
  a5 := family.a5
  a4 := family.a4
  a3 := family.a3
  a2 := a2
  firstRoot := family.firstRoot
  secondRoot := family.secondRoot
  thirdRoot := family.thirdRoot
  fourthRoot := family.fourthRoot
  fifthRoot := family.fifthRoot

/-- Exact evaluation of the family quintic. -/
def eval (family : DegreeSevenStageSixFamily)
    (a2 : ℤ) (x : ℚ) : ℚ :=
  integerPolynomialRationalEval (family.derivativeCoefficients a2) x

/-- A sign pattern that is negative at the left endpoint and positive at the
right endpoint uniformly over the whole `a2` interval. -/
def NegativePositive (family : DegreeSevenStageSixFamily)
    (interval : RationalRootInterval) : Prop :=
  family.eval family.a2Upper interval.lower < 0 ∧
    0 < family.eval family.a2Lower interval.upper

/-- A sign pattern that is positive at the left endpoint and negative at the
right endpoint uniformly over the whole `a2` interval. -/
def PositiveNegative (family : DegreeSevenStageSixFamily)
    (interval : RationalRootInterval) : Prop :=
  0 < family.eval family.a2Lower interval.lower ∧
    family.eval family.a2Upper interval.upper < 0

/-- Kernel-checkable validity of a parametric Stage Six certificate. -/
def Valid (family : DegreeSevenStageSixFamily) : Prop :=
  family.a2Lower ≤ family.a2Upper ∧
    family.firstRoot.lower < family.firstRoot.upper ∧
    family.secondRoot.lower < family.secondRoot.upper ∧
    family.thirdRoot.lower < family.thirdRoot.upper ∧
    family.fourthRoot.lower < family.fourthRoot.upper ∧
    family.fifthRoot.lower < family.fifthRoot.upper ∧
    family.NegativePositive family.firstRoot ∧
    family.PositiveNegative family.secondRoot ∧
    family.NegativePositive family.thirdRoot ∧
    family.PositiveNegative family.fourthRoot ∧
    family.NegativePositive family.fifthRoot ∧
    family.firstRoot.upper < family.secondRoot.lower ∧
    family.secondRoot.upper < family.thirdRoot.lower ∧
    family.thirdRoot.upper < family.fourthRoot.lower ∧
    family.fourthRoot.upper < family.fifthRoot.lower

instance (family : DegreeSevenStageSixFamily) :
    Decidable family.Valid := by
  unfold Valid NegativePositive PositiveNegative eval derivativeCoefficients
  infer_instance

/-- The finite interval of `a2` values represented by a family. -/
def a2Candidates (family : DegreeSevenStageSixFamily) : Finset ℤ :=
  integerIcc family.a2Lower family.a2Upper

theorem eval_eq_constant_add (family : DegreeSevenStageSixFamily)
    (a2 : ℤ) (x : ℚ) :
    family.eval a2 x =
      (a2 : ℚ) + family.eval 0 x := by
  simp [eval, derivativeCoefficients, integerPolynomialRationalEval,
    DensePolynomial.eval]

theorem eval_mono (family : DegreeSevenStageSixFamily)
    {a2 b2 : ℤ} (h : a2 ≤ b2) (x : ℚ) :
    family.eval a2 x ≤ family.eval b2 x := by
  calc
    family.eval a2 x = (a2 : ℚ) + family.eval 0 x :=
      family.eval_eq_constant_add a2 x
    _ ≤ (b2 : ℚ) + family.eval 0 x :=
      by
        simpa [add_comm] using
          (add_le_add_right (by exact_mod_cast h : (a2 : ℚ) ≤ b2)
            (family.eval 0 x))
    _ = family.eval b2 x := (family.eval_eq_constant_add b2 x).symm

private theorem interval_valid_of_negativePositive
    (family : DegreeSevenStageSixFamily)
    (interval : RationalRootInterval)
    {a2 : ℤ} (hlower : family.a2Lower ≤ a2)
    (hupper : a2 ≤ family.a2Upper)
    (hinterval : interval.lower < interval.upper)
    (hsign : family.NegativePositive interval) :
    interval.lower < interval.upper ∧
      family.eval a2 interval.lower * family.eval a2 interval.upper < 0 := by
  refine ⟨hinterval, mul_neg_of_neg_of_pos ?_ ?_⟩
  · exact (family.eval_mono hupper interval.lower).trans_lt hsign.1
  · exact hsign.2.trans_le (family.eval_mono hlower interval.upper)

private theorem interval_valid_of_positiveNegative
    (family : DegreeSevenStageSixFamily)
    (interval : RationalRootInterval)
    {a2 : ℤ} (hlower : family.a2Lower ≤ a2)
    (hupper : a2 ≤ family.a2Upper)
    (hinterval : interval.lower < interval.upper)
    (hsign : family.PositiveNegative interval) :
    interval.lower < interval.upper ∧
      family.eval a2 interval.lower * family.eval a2 interval.upper < 0 := by
  refine ⟨hinterval, mul_neg_of_pos_of_neg ?_ ?_⟩
  · exact hsign.1.trans_le (family.eval_mono hlower interval.lower)
  · exact (family.eval_mono hupper interval.upper).trans_lt hsign.2

/-- A valid family supplies an ordinary valid Stage Six certificate at every
integer in its recorded interval. -/
theorem toEntry_valid (family : DegreeSevenStageSixFamily)
    (hvalid : family.Valid) {a2 : ℤ}
    (hlower : family.a2Lower ≤ a2) (hupper : a2 ≤ family.a2Upper) :
    (family.toEntry a2).Valid := by
  rcases hvalid with
    ⟨_, hfirstInterval, hsecondInterval, hthirdInterval, hfourthInterval,
      hfifthInterval, hfirstSign, hsecondSign, hthirdSign, hfourthSign,
      hfifthSign, h12, h23, h34, h45⟩
  unfold DegreeSevenStageSixEntry.Valid
  unfold GeneralRationalRootIntervalCertificate.Valid
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [toEntry, DegreeSevenStageSixEntry.derivativeCoefficients]
  · norm_num [toEntry, DegreeSevenStageSixEntry.derivativeCoefficients]
  · norm_num [toEntry, DegreeSevenStageSixEntry.rootIntervals]
  · simp only [toEntry, DegreeSevenStageSixEntry.rootIntervals,
      List.forall_cons]
    exact ⟨interval_valid_of_negativePositive family family.firstRoot
        hlower hupper hfirstInterval hfirstSign,
      interval_valid_of_positiveNegative family family.secondRoot
        hlower hupper hsecondInterval hsecondSign,
      interval_valid_of_negativePositive family family.thirdRoot
        hlower hupper hthirdInterval hthirdSign,
      interval_valid_of_positiveNegative family family.fourthRoot
        hlower hupper hfourthInterval hfourthSign,
      interval_valid_of_negativePositive family family.fifthRoot
        hlower hupper hfifthInterval hfifthSign, trivial⟩
  · simp only [toEntry, DegreeSevenStageSixEntry.rootIntervals,
      List.pairwise_cons, List.mem_cons, forall_eq_or_imp]
    simp
    exact
      ⟨⟨h12,
          h12.trans (hsecondInterval.trans h23),
          h12.trans (hsecondInterval.trans
            (h23.trans (hthirdInterval.trans h34))),
          h12.trans (hsecondInterval.trans
            (h23.trans (hthirdInterval.trans
              (h34.trans (hfourthInterval.trans h45)))))⟩,
        ⟨h23,
          h23.trans (hthirdInterval.trans h34),
          h23.trans (hthirdInterval.trans
            (h34.trans (hfourthInterval.trans h45)))⟩,
        ⟨h34, h34.trans (hfourthInterval.trans h45)⟩,
        h45⟩

/-- Finset membership is the convenient generated-data interface for the
closed integer interval stored by a family. -/
theorem toEntry_valid_of_mem (family : DegreeSevenStageSixFamily)
    (hvalid : family.Valid) {a2 : ℤ} (ha2 : a2 ∈ family.a2Candidates) :
    (family.toEntry a2).Valid := by
  rw [a2Candidates, integerIcc, Finset.mem_Icc] at ha2
  exact family.toEntry_valid hvalid ha2.1 ha2.2

/-- The parametric certificate yields the sharpened `a1` candidate set for
the actual septic coefficient. -/
theorem degreeSeven_minimumHunterCandidate_a1_mem_of_family
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (family : DegreeSevenStageSixFamily) (hvalid : family.Valid)
    (ha6 : family.a6 = f.coeff 6)
    (ha5 : family.a5 = f.coeff 5)
    (ha4 : family.a4 = f.coeff 4)
    (ha3 : family.a3 = f.coeff 3)
    (ha2 : f.coeff 2 ∈ family.a2Candidates) :
    f.coeff 1 ∈ (family.toEntry (f.coeff 2)).a1Candidates := by
  apply degreeSeven_minimumHunterCandidate_a1_mem_of_valid h
    (family.toEntry (f.coeff 2)) (family.toEntry_valid_of_mem hvalid ha2)
  · simpa [toEntry] using ha6
  · simpa [toEntry] using ha5
  · simpa [toEntry] using ha4
  · simpa [toEntry] using ha3
  · rfl

end DegreeSevenStageSixFamily

end

end TraceEuclidean
