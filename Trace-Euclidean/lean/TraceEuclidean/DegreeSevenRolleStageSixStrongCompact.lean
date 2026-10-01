import TraceEuclidean.DegreeSevenRolleStageSixCoverage
import TraceEuclidean.DegreeSevenRolleStageSixStrongCoverage
import TraceEuclidean.ScaledIntegerPolynomialInterval
import TraceEuclidean.DegreeSevenRolleStageSixRefinedCritical

/-!
# Compact half-line coverage for the sixth degree-seven Rolle stage

The Stage Five root intervals already isolate the four critical points.  Most
boundary signs can therefore reuse those intervals, storing only an integer
constant coefficient and one of four point labels.  If the immediately
adjacent value needs a narrower interval (or has a multiple root), one exact
rejection record fills that single gap.  This avoids duplicating four refined
rational intervals in every generated half-line certificate.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

namespace DegreeSevenStageSixCriticalSignWitness

/-- Build the relative witness directly from a compact Stage Five row. -/
def ofDyadicParent (parent : DegreeSevenStageFiveDyadicEntry)
    (a2 : ℤ) (point : DegreeSevenStageSixCriticalPoint) :
    DegreeSevenStageSixCriticalSignWitness :=
  ⟨parent.toEntry, a2, point⟩

/-- Only the strict sign part of a critical-point certificate. -/
def SignValid (witness : DegreeSevenStageSixCriticalSignWitness) : Prop :=
  match witness.point with
  | .first => witness.criticalValueRange.hi < 0
  | .second => 0 < witness.criticalValueRange.lo
  | .third => witness.criticalValueRange.hi < 0
  | .fourth => 0 < witness.criticalValueRange.lo

instance (witness : DegreeSevenStageSixCriticalSignWitness) :
    Decidable witness.SignValid := by
  unfold SignValid
  cases witness.point <;> infer_instance

/-- A relative witness reuses exactly the compact Stage Five parent's four
root intervals. -/
def RelativeValid (witness : DegreeSevenStageSixCriticalSignWitness)
    (parent : DegreeSevenStageFiveDyadicEntry) : Prop :=
  witness.parent = parent.toEntry ∧ witness.SignValid

/-- The stored dyadic cell containing one of the four critical points. -/
def dyadicCell (point : DegreeSevenStageSixCriticalPoint)
    (parent : DegreeSevenStageFiveDyadicEntry) : ℤ :=
  match point with
  | .first => parent.firstCell
  | .second => parent.secondCell
  | .third => parent.thirdCell
  | .fourth => parent.fourthCell

/-- Cleared-denominator interval numerators for the quintic at the selected
Stage Five root interval. -/
def scaledCriticalRange
    (witness : DegreeSevenStageSixCriticalSignWitness)
    (parent : DegreeSevenStageFiveDyadicEntry) : ℤ × ℤ :=
  let cell := dyadicCell witness.point parent
  scaledIntegerPolynomialIntervalEval 4096 cell (cell + 2)
    witness.coefficients

/-- Efficient integer version of relative critical-sign validity. -/
def RelativeArithmeticValid
    (witness : DegreeSevenStageSixCriticalSignWitness)
    (parent : DegreeSevenStageFiveDyadicEntry) : Prop :=
  witness.parent = parent.toEntry ∧
    match witness.point with
    | .first => (witness.scaledCriticalRange parent).2 < 0
    | .second => 0 < (witness.scaledCriticalRange parent).1
    | .third => (witness.scaledCriticalRange parent).2 < 0
    | .fourth => 0 < (witness.scaledCriticalRange parent).1

instance (witness : DegreeSevenStageSixCriticalSignWitness)
    (parent : DegreeSevenStageFiveDyadicEntry) :
    Decidable (witness.RelativeValid parent) := by
  unfold RelativeValid
  infer_instance

instance (witness : DegreeSevenStageSixCriticalSignWitness)
    (parent : DegreeSevenStageFiveDyadicEntry) :
    Decidable (witness.RelativeArithmeticValid parent) := by
  unfold RelativeArithmeticValid
  cases witness.point <;> infer_instance

private theorem criticalValueRange_eq_scaled
    (witness : DegreeSevenStageSixCriticalSignWitness)
    (parent : DegreeSevenStageFiveDyadicEntry)
    (hparentEq : witness.parent = parent.toEntry) :
    witness.criticalValueRange.lo =
        ((witness.scaledCriticalRange parent).1 : ℚ) / 4096 ^ 6 ∧
      witness.criticalValueRange.hi =
        ((witness.scaledCriticalRange parent).2 : ℚ) / 4096 ^ 6 := by
  let cell := dyadicCell witness.point parent
  have hcorrect := scaledIntegerPolynomialIntervalEval_correct
    witness.coefficients 4096 cell (cell + 2) (by norm_num) (by omega)
  have hordered (x : ℤ) :
      ((x : ℚ) / 4096) ≤ (((x : ℚ) + 2) / 4096) := by
    rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℚ) < 4096)]
    norm_num
  dsimp only at hcorrect
  cases hpoint : witness.point <;>
    simpa [criticalValueRange, coefficients, scaledCriticalRange, cell,
      dyadicCell, DegreeSevenStageSixCriticalPoint.interval,
      DegreeSevenStageFiveDyadicEntry.toEntry,
      degreeSevenStageFiveDyadicInterval,
      degreeSevenStageFiveDyadicDenominator,
      integerPolynomialRootIntervalEval,
      integerPolynomialIntervalEval,
      RationalRootInterval.toIntervalRat, hparentEq, hpoint, hordered] using hcorrect

theorem relativeValid_of_relativeArithmeticValid
    (witness : DegreeSevenStageSixCriticalSignWitness)
    (parent : DegreeSevenStageFiveDyadicEntry)
    (h : witness.RelativeArithmeticValid parent) :
    witness.RelativeValid parent := by
  rcases h with ⟨hparentEq, hsign⟩
  refine ⟨hparentEq, ?_⟩
  have hrange := criticalValueRange_eq_scaled witness parent hparentEq
  have hdenominator : (0 : ℚ) < 4096 ^ 6 := by positivity
  cases hpoint : witness.point
  · have hsign' : (witness.scaledCriticalRange parent).2 < 0 := by
      simpa [RelativeArithmeticValid, hpoint] using hsign
    unfold SignValid
    rw [hpoint, hrange.2]
    exact div_neg_of_neg_of_pos (by exact_mod_cast hsign') hdenominator
  · have hsign' : 0 < (witness.scaledCriticalRange parent).1 := by
      simpa [RelativeArithmeticValid, hpoint] using hsign
    unfold SignValid
    rw [hpoint, hrange.1]
    exact div_pos (by exact_mod_cast hsign') hdenominator
  · have hsign' : (witness.scaledCriticalRange parent).2 < 0 := by
      simpa [RelativeArithmeticValid, hpoint] using hsign
    unfold SignValid
    rw [hpoint, hrange.2]
    exact div_neg_of_neg_of_pos (by exact_mod_cast hsign') hdenominator
  · have hsign' : 0 < (witness.scaledCriticalRange parent).1 := by
      simpa [RelativeArithmeticValid, hpoint] using hsign
    unfold SignValid
    rw [hpoint, hrange.1]
    exact div_pos (by exact_mod_cast hsign') hdenominator

theorem valid_of_relativeValid
    (witness : DegreeSevenStageSixCriticalSignWitness)
    (parent : DegreeSevenStageFiveDyadicEntry)
    (hparent : parent.Valid) (hrelative : witness.RelativeValid parent) :
    witness.Valid := by
  rcases hrelative with ⟨hparentEq, hsign⟩
  unfold Valid
  constructor
  · rw [hparentEq]
    exact hparent
  · cases hpoint : witness.point <;>
      simpa [SignValid, hpoint] using hsign

theorem sameTop_of_relativeValid
    (witness : DegreeSevenStageSixCriticalSignWitness)
    (parent : DegreeSevenStageFiveDyadicEntry)
    (hrelative : witness.RelativeValid parent) : witness.SameTop parent := by
  rcases hrelative with ⟨hparentEq, _⟩
  unfold SameTop
  rw [hparentEq]
  simp [DegreeSevenStageFiveDyadicEntry.toEntry]

end DegreeSevenStageSixCriticalSignWitness

namespace DegreeSevenStageSixRejection

/-- Either exact rejection type contradicts a matching Hunter septic. -/
theorem not_hunter_of_eq
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (rejection : DegreeSevenStageSixRejection)
    (parent : DegreeSevenStageFiveDyadicEntry)
    (hvalid : rejection.Valid)
    (htop : rejection.SameTop parent)
    (ha6 : parent.a6 = f.coeff 6) (ha5 : parent.a5 = f.coeff 5)
    (ha4 : parent.a4 = f.coeff 4) (ha3 : parent.a3 = f.coeff 3)
    (ha2 : rejection.a2 = f.coeff 2) : False := by
  cases rejection with
  | multipleRoot witness =>
      exact degreeSeven_multipleRootWitness_not_hunter h witness hvalid
        (htop.1.trans ha6) (htop.2.1.trans ha5)
        (htop.2.2.1.trans ha4) (htop.2.2.2.trans ha3) ha2
  | criticalSign witness =>
      exact degreeSeven_criticalSignWitness_not_hunter h witness hvalid
        (htop.1.trans ha6) (htop.2.1.trans ha5)
        (htop.2.2.1.trans ha4) (htop.2.2.2.trans ha3) ha2

end DegreeSevenStageSixRejection

/-- A critical half-line certificate relative to one compact Stage Five row.
Only the integer constant coefficient and the selected point are stored. -/
structure DegreeSevenStageSixCompactCriticalSign where
  a2 : ℤ
  point : DegreeSevenStageSixCriticalPoint
deriving DecidableEq, Repr

namespace DegreeSevenStageSixCompactCriticalSign

def toWitness (critical : DegreeSevenStageSixCompactCriticalSign)
    (parent : DegreeSevenStageFiveDyadicEntry) :
    DegreeSevenStageSixCriticalSignWitness :=
  DegreeSevenStageSixCriticalSignWitness.ofDyadicParent
    parent critical.a2 critical.point

def IsLower (critical : DegreeSevenStageSixCompactCriticalSign) : Prop :=
  critical.point = .first ∨ critical.point = .third

def IsUpper (critical : DegreeSevenStageSixCompactCriticalSign) : Prop :=
  critical.point = .second ∨ critical.point = .fourth

instance (critical : DegreeSevenStageSixCompactCriticalSign) :
    Decidable critical.IsLower := by
  unfold IsLower
  infer_instance

instance (critical : DegreeSevenStageSixCompactCriticalSign) :
    Decidable critical.IsUpper := by
  unfold IsUpper
  infer_instance

def Valid (critical : DegreeSevenStageSixCompactCriticalSign)
    (parent : DegreeSevenStageFiveDyadicEntry) : Prop :=
  (critical.toWitness parent).SignValid

def ArithmeticValid (critical : DegreeSevenStageSixCompactCriticalSign)
    (parent : DegreeSevenStageFiveDyadicEntry) : Prop :=
  match critical.point with
  | .first => ((critical.toWitness parent).scaledCriticalRange parent).2 < 0
  | .second => 0 < ((critical.toWitness parent).scaledCriticalRange parent).1
  | .third => ((critical.toWitness parent).scaledCriticalRange parent).2 < 0
  | .fourth => 0 < ((critical.toWitness parent).scaledCriticalRange parent).1

instance (critical : DegreeSevenStageSixCompactCriticalSign)
    (parent : DegreeSevenStageFiveDyadicEntry) :
    Decidable (critical.Valid parent) := by
  unfold Valid toWitness
    DegreeSevenStageSixCriticalSignWitness.ofDyadicParent
    DegreeSevenStageSixCriticalSignWitness.SignValid
  cases critical.point <;> infer_instance

instance (critical : DegreeSevenStageSixCompactCriticalSign)
    (parent : DegreeSevenStageFiveDyadicEntry) :
    Decidable (critical.ArithmeticValid parent) := by
  unfold ArithmeticValid
  cases critical.point <;> infer_instance

theorem valid_of_arithmeticValid
    (critical : DegreeSevenStageSixCompactCriticalSign)
    (parent : DegreeSevenStageFiveDyadicEntry)
    (h : critical.ArithmeticValid parent) : critical.Valid parent := by
  have hrelative :
      (critical.toWitness parent).RelativeArithmeticValid parent := by
    refine ⟨rfl, ?_⟩
    cases hpoint : critical.point <;>
      simpa [ArithmeticValid, toWitness,
        DegreeSevenStageSixCriticalSignWitness.ofDyadicParent,
        DegreeSevenStageSixCriticalSignWitness.RelativeArithmeticValid,
        hpoint] using h
  exact ((critical.toWitness parent).relativeValid_of_relativeArithmeticValid
    parent hrelative).2

theorem sameTop
    (critical : DegreeSevenStageSixCompactCriticalSign)
    (parent : DegreeSevenStageFiveDyadicEntry) :
    (critical.toWitness parent).SameTop parent := by
  unfold DegreeSevenStageSixCriticalSignWitness.SameTop
  simp [toWitness, DegreeSevenStageSixCriticalSignWitness.ofDyadicParent,
    DegreeSevenStageFiveDyadicEntry.toEntry]

theorem excludes_of_isLower
    (critical : DegreeSevenStageSixCompactCriticalSign)
    (parent : DegreeSevenStageFiveDyadicEntry)
    (hlower : critical.IsLower) {a2 : ℤ} (ha2 : a2 ≤ critical.a2) :
    (critical.toWitness parent).Excludes a2 := by
  rcases hlower with hpoint | hpoint
  · simp [toWitness, IsLower,
      DegreeSevenStageSixCriticalSignWitness.ofDyadicParent,
      DegreeSevenStageSixCriticalSignWitness.Excludes, hpoint, ha2]
  · simp [toWitness, IsLower,
      DegreeSevenStageSixCriticalSignWitness.ofDyadicParent,
      DegreeSevenStageSixCriticalSignWitness.Excludes, hpoint, ha2]

theorem excludes_of_isUpper
    (critical : DegreeSevenStageSixCompactCriticalSign)
    (parent : DegreeSevenStageFiveDyadicEntry)
    (hupper : critical.IsUpper) {a2 : ℤ} (ha2 : critical.a2 ≤ a2) :
    (critical.toWitness parent).Excludes a2 := by
  rcases hupper with hpoint | hpoint
  · simp [toWitness, IsUpper,
      DegreeSevenStageSixCriticalSignWitness.ofDyadicParent,
      DegreeSevenStageSixCriticalSignWitness.Excludes, hpoint, ha2]
  · simp [toWitness, IsUpper,
      DegreeSevenStageSixCriticalSignWitness.ofDyadicParent,
      DegreeSevenStageSixCriticalSignWitness.Excludes, hpoint, ha2]

end DegreeSevenStageSixCompactCriticalSign

/-- Compact exceptional boundary data.  Refined critical-sign rejections reuse
the Stage Five parent intervals and therefore store only `a2` and the selected
critical point.  Multiple-root rejections retain their exact rational root. -/
inductive DegreeSevenStageSixCompactRejection where
  | multipleRoot (witness : DegreeSevenStageSixMultipleRootWitness)
  | criticalSign (critical : DegreeSevenStageSixRefinedCriticalSign)
deriving DecidableEq, Repr

namespace DegreeSevenStageSixCompactRejection

def a2 : DegreeSevenStageSixCompactRejection → ℤ
  | .multipleRoot witness => witness.a2
  | .criticalSign critical => critical.a2

def toRejection (rejection : DegreeSevenStageSixCompactRejection)
    (parent : DegreeSevenStageFiveDyadicEntry) :
    DegreeSevenStageSixRejection :=
  match rejection with
  | .multipleRoot witness => .multipleRoot witness
  | .criticalSign critical => .criticalSign (critical.toWitness parent)

def Valid (rejection : DegreeSevenStageSixCompactRejection)
    (parent : DegreeSevenStageFiveDyadicEntry) : Prop :=
  match rejection with
  | .multipleRoot witness => witness.Valid ∧ witness.SameTop parent
  | .criticalSign critical => critical.Valid parent

def ArithmeticValid (rejection : DegreeSevenStageSixCompactRejection)
    (parent : DegreeSevenStageFiveDyadicEntry) : Prop :=
  match rejection with
  | .multipleRoot witness => witness.Valid ∧ witness.SameTop parent
  | .criticalSign critical => critical.ArithmeticValid parent

/-- The inexpensive part of a compact rejection.  Critical-sign validity is
entirely integral; only a multiple root is deferred to an exact witness list. -/
def SkeletonValid (rejection : DegreeSevenStageSixCompactRejection)
    (parent : DegreeSevenStageFiveDyadicEntry) : Prop :=
  match rejection with
  | .multipleRoot witness => witness.SameTop parent
  | .criticalSign critical => critical.ArithmeticValid parent

def exactWitnesses (rejection : DegreeSevenStageSixCompactRejection) :
    List DegreeSevenStageSixMultipleRootWitness :=
  match rejection with
  | .multipleRoot witness => [witness]
  | .criticalSign _ => []

instance (rejection : DegreeSevenStageSixCompactRejection)
    (parent : DegreeSevenStageFiveDyadicEntry) :
    Decidable (rejection.Valid parent) := by
  cases rejection <;> simp only [Valid] <;> infer_instance

instance (rejection : DegreeSevenStageSixCompactRejection)
    (parent : DegreeSevenStageFiveDyadicEntry) :
    Decidable (rejection.ArithmeticValid parent) := by
  cases rejection <;> simp only [ArithmeticValid] <;> infer_instance

instance (rejection : DegreeSevenStageSixCompactRejection)
    (parent : DegreeSevenStageFiveDyadicEntry) :
    Decidable (rejection.SkeletonValid parent) := by
  cases rejection <;> simp only [SkeletonValid] <;> infer_instance

theorem arithmeticValid_of_skeleton_and_exact
    (rejection : DegreeSevenStageSixCompactRejection)
    (parent : DegreeSevenStageFiveDyadicEntry)
    (hskeleton : rejection.SkeletonValid parent)
    (hexact : rejection.exactWitnesses.Forall
      DegreeSevenStageSixMultipleRootWitness.Valid) :
    rejection.ArithmeticValid parent := by
  cases rejection with
  | multipleRoot witness =>
      simpa [SkeletonValid, exactWitnesses, ArithmeticValid] using
        And.intro hexact hskeleton
  | criticalSign critical =>
      simpa [SkeletonValid, exactWitnesses, ArithmeticValid] using hskeleton

theorem valid_of_arithmeticValid
    (rejection : DegreeSevenStageSixCompactRejection)
    (parent : DegreeSevenStageFiveDyadicEntry)
    (h : rejection.ArithmeticValid parent) : rejection.Valid parent := by
  cases rejection with
  | multipleRoot witness => simpa [ArithmeticValid, Valid] using h
  | criticalSign critical =>
      simpa [ArithmeticValid, Valid] using
        critical.valid_of_arithmeticValid parent h

theorem toRejection_valid
    (rejection : DegreeSevenStageSixCompactRejection)
    (parent : DegreeSevenStageFiveDyadicEntry)
    (hparent : parent.Valid)
    (h : rejection.Valid parent) : (rejection.toRejection parent).Valid := by
  cases rejection with
  | multipleRoot witness =>
      change witness.Valid
      exact h.1
  | criticalSign critical =>
      change (critical.toWitness parent).Valid
      exact h

theorem toRejection_sameTop
    (rejection : DegreeSevenStageSixCompactRejection)
    (parent : DegreeSevenStageFiveDyadicEntry)
    (h : rejection.Valid parent) :
    (rejection.toRejection parent).SameTop parent := by
  cases rejection with
  | multipleRoot witness =>
      change witness.SameTop parent
      exact h.2
  | criticalSign critical =>
      change (critical.toWitness parent).SameTop parent
      exact critical.sameTop parent

theorem not_hunter_of_eq
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (rejection : DegreeSevenStageSixCompactRejection)
    (parent : DegreeSevenStageFiveDyadicEntry)
    (hparent : parent.Valid)
    (hvalid : rejection.Valid parent)
    (ha6 : parent.a6 = f.coeff 6) (ha5 : parent.a5 = f.coeff 5)
    (ha4 : parent.a4 = f.coeff 4) (ha3 : parent.a3 = f.coeff 3)
    (ha2 : rejection.a2 = f.coeff 2) : False := by
  apply (rejection.toRejection parent).not_hunter_of_eq h parent
    (rejection.toRejection_valid parent hparent hvalid)
    (rejection.toRejection_sameTop parent hvalid) ha6 ha5 ha4 ha3
  cases rejection with
  | multipleRoot witness =>
      change witness.a2 = f.coeff 2
      exact ha2
  | criticalSign critical =>
      change critical.a2 = f.coeff 2
      exact ha2

end DegreeSevenStageSixCompactRejection

/-- A compact lower half-line boundary.  The optional exact rejection fills
the sole integer between the strict half-line and the surviving family. -/
structure DegreeSevenStageSixCompactLowerBoundary where
  bound : ℤ
  critical : DegreeSevenStageSixCompactCriticalSign
  edge : Option DegreeSevenStageSixCompactRejection
deriving DecidableEq, Repr

namespace DegreeSevenStageSixCompactLowerBoundary

def Valid (boundary : DegreeSevenStageSixCompactLowerBoundary)
    (parent : DegreeSevenStageFiveDyadicEntry) : Prop :=
  boundary.critical.Valid parent ∧ boundary.critical.IsLower ∧
    match boundary.edge with
    | none => boundary.bound = boundary.critical.a2 + 1
    | some rejection =>
        rejection.Valid parent ∧
          rejection.a2 = boundary.critical.a2 + 1 ∧
          boundary.bound = rejection.a2 + 1

def ArithmeticValid (boundary : DegreeSevenStageSixCompactLowerBoundary)
    (parent : DegreeSevenStageFiveDyadicEntry) : Prop :=
  boundary.critical.ArithmeticValid parent ∧ boundary.critical.IsLower ∧
    match boundary.edge with
    | none => boundary.bound = boundary.critical.a2 + 1
    | some rejection =>
        rejection.ArithmeticValid parent ∧
          rejection.a2 = boundary.critical.a2 + 1 ∧
          boundary.bound = rejection.a2 + 1

/-- Integer and alignment part of lower-boundary validity, excluding the
expensive exact validity check of the optional edge rejection. -/
def SkeletonValid (boundary : DegreeSevenStageSixCompactLowerBoundary)
    (parent : DegreeSevenStageFiveDyadicEntry) : Prop :=
  boundary.critical.ArithmeticValid parent ∧ boundary.critical.IsLower ∧
    match boundary.edge with
    | none => boundary.bound = boundary.critical.a2 + 1
    | some rejection =>
        rejection.SkeletonValid parent ∧
          rejection.a2 = boundary.critical.a2 + 1 ∧
          boundary.bound = rejection.a2 + 1

def edgeRejections (boundary : DegreeSevenStageSixCompactLowerBoundary) :
    List DegreeSevenStageSixMultipleRootWitness :=
  boundary.edge.toList.flatMap
    DegreeSevenStageSixCompactRejection.exactWitnesses

instance (boundary : DegreeSevenStageSixCompactLowerBoundary)
    (parent : DegreeSevenStageFiveDyadicEntry) :
    Decidable (boundary.Valid parent) := by
  unfold Valid
  cases boundary.edge <;> infer_instance

instance (boundary : DegreeSevenStageSixCompactLowerBoundary)
    (parent : DegreeSevenStageFiveDyadicEntry) :
    Decidable (boundary.SkeletonValid parent) := by
  unfold SkeletonValid
  cases boundary.edge <;> infer_instance

theorem arithmeticValid_of_skeleton
    (boundary : DegreeSevenStageSixCompactLowerBoundary)
    (parent : DegreeSevenStageFiveDyadicEntry)
    (hskeleton : boundary.SkeletonValid parent)
    (hedge : boundary.edgeRejections.Forall
      DegreeSevenStageSixMultipleRootWitness.Valid) :
    boundary.ArithmeticValid parent := by
  rcases hskeleton with ⟨hcritical, hlower, hrecord⟩
  refine ⟨hcritical, hlower, ?_⟩
  cases hoption : boundary.edge with
  | none => simpa [hoption] using hrecord
  | some rejection =>
      have hrecord' : rejection.SkeletonValid parent ∧
          rejection.a2 = boundary.critical.a2 + 1 ∧
          boundary.bound = rejection.a2 + 1 := by
        simpa [hoption] using hrecord
      have hexact : rejection.exactWitnesses.Forall
          DegreeSevenStageSixMultipleRootWitness.Valid := by
        simpa [edgeRejections, hoption] using hedge
      have hvalid : rejection.ArithmeticValid parent :=
        rejection.arithmeticValid_of_skeleton_and_exact parent hrecord'.1 hexact
      simpa [hoption] using And.intro hvalid hrecord'.2

instance (boundary : DegreeSevenStageSixCompactLowerBoundary)
    (parent : DegreeSevenStageFiveDyadicEntry) :
    Decidable (boundary.ArithmeticValid parent) := by
  unfold ArithmeticValid
  cases boundary.edge <;> infer_instance

theorem valid_of_arithmeticValid
    (boundary : DegreeSevenStageSixCompactLowerBoundary)
    (parent : DegreeSevenStageFiveDyadicEntry)
    (h : boundary.ArithmeticValid parent) : boundary.Valid parent := by
  rcases h with ⟨hcritical, hlower, hedge⟩
  refine ⟨boundary.critical.valid_of_arithmeticValid parent hcritical,
    hlower, ?_⟩
  cases hoption : boundary.edge with
  | none => simpa [hoption] using hedge
  | some rejection =>
      have hrecord : rejection.ArithmeticValid parent ∧
          rejection.a2 = boundary.critical.a2 + 1 ∧
          boundary.bound = rejection.a2 + 1 := by
        simpa [hoption] using hedge
      simpa [hoption] using And.intro
        (rejection.valid_of_arithmeticValid parent hrecord.1) hrecord.2

theorem not_hunter_of_lt
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (boundary : DegreeSevenStageSixCompactLowerBoundary)
    (parent : DegreeSevenStageFiveDyadicEntry)
    (hparent : parent.Valid) (hvalid : boundary.Valid parent)
    (ha6 : parent.a6 = f.coeff 6) (ha5 : parent.a5 = f.coeff 5)
    (ha4 : parent.a4 = f.coeff 4) (ha3 : parent.a3 = f.coeff 3)
    (ha2 : f.coeff 2 < boundary.bound) : False := by
  rcases hvalid with ⟨hrelative, hlower, hedge⟩
  let witness := boundary.critical.toWitness parent
  have hcriticalValid : witness.Valid := by
    exact ⟨hparent, hrelative⟩
  have hcriticalTop : witness.SameTop parent := boundary.critical.sameTop parent
  cases hedgeOption : boundary.edge with
  | none =>
      have hbound : boundary.bound = boundary.critical.a2 + 1 := by
        simpa [hedgeOption] using hedge
      have hle : f.coeff 2 ≤ boundary.critical.a2 := by omega
      exact degreeSeven_criticalSignWitness_excludes_hunter h
        witness hcriticalValid
        (hcriticalTop.1.trans ha6) (hcriticalTop.2.1.trans ha5)
        (hcriticalTop.2.2.1.trans ha4) (hcriticalTop.2.2.2.trans ha3)
        (boundary.critical.excludes_of_isLower parent hlower hle)
  | some rejection =>
      have hedgeValid : rejection.Valid parent ∧
          rejection.a2 = boundary.critical.a2 + 1 ∧
          boundary.bound = rejection.a2 + 1 := by
        simpa [hedgeOption] using hedge
      by_cases heq : f.coeff 2 = rejection.a2
      · exact rejection.not_hunter_of_eq h parent hparent hedgeValid.1
          ha6 ha5 ha4 ha3 heq.symm
      · have hle : f.coeff 2 ≤ boundary.critical.a2 := by omega
        exact degreeSeven_criticalSignWitness_excludes_hunter h
          witness hcriticalValid
          (hcriticalTop.1.trans ha6) (hcriticalTop.2.1.trans ha5)
          (hcriticalTop.2.2.1.trans ha4) (hcriticalTop.2.2.2.trans ha3)
          (boundary.critical.excludes_of_isLower parent hlower hle)

end DegreeSevenStageSixCompactLowerBoundary

/-- A compact upper half-line boundary, dual to the lower boundary. -/
structure DegreeSevenStageSixCompactUpperBoundary where
  bound : ℤ
  critical : DegreeSevenStageSixCompactCriticalSign
  edge : Option DegreeSevenStageSixCompactRejection
deriving DecidableEq, Repr

namespace DegreeSevenStageSixCompactUpperBoundary

def Valid (boundary : DegreeSevenStageSixCompactUpperBoundary)
    (parent : DegreeSevenStageFiveDyadicEntry) : Prop :=
  boundary.critical.Valid parent ∧ boundary.critical.IsUpper ∧
    match boundary.edge with
    | none => boundary.bound = boundary.critical.a2 - 1
    | some rejection =>
        rejection.Valid parent ∧
          rejection.a2 = boundary.critical.a2 - 1 ∧
          boundary.bound = rejection.a2 - 1

def ArithmeticValid (boundary : DegreeSevenStageSixCompactUpperBoundary)
    (parent : DegreeSevenStageFiveDyadicEntry) : Prop :=
  boundary.critical.ArithmeticValid parent ∧ boundary.critical.IsUpper ∧
    match boundary.edge with
    | none => boundary.bound = boundary.critical.a2 - 1
    | some rejection =>
        rejection.ArithmeticValid parent ∧
          rejection.a2 = boundary.critical.a2 - 1 ∧
          boundary.bound = rejection.a2 - 1

def SkeletonValid (boundary : DegreeSevenStageSixCompactUpperBoundary)
    (parent : DegreeSevenStageFiveDyadicEntry) : Prop :=
  boundary.critical.ArithmeticValid parent ∧ boundary.critical.IsUpper ∧
    match boundary.edge with
    | none => boundary.bound = boundary.critical.a2 - 1
    | some rejection =>
        rejection.SkeletonValid parent ∧
          rejection.a2 = boundary.critical.a2 - 1 ∧
          boundary.bound = rejection.a2 - 1

def edgeRejections (boundary : DegreeSevenStageSixCompactUpperBoundary) :
    List DegreeSevenStageSixMultipleRootWitness :=
  boundary.edge.toList.flatMap
    DegreeSevenStageSixCompactRejection.exactWitnesses

instance (boundary : DegreeSevenStageSixCompactUpperBoundary)
    (parent : DegreeSevenStageFiveDyadicEntry) :
    Decidable (boundary.Valid parent) := by
  unfold Valid
  cases boundary.edge <;> infer_instance

instance (boundary : DegreeSevenStageSixCompactUpperBoundary)
    (parent : DegreeSevenStageFiveDyadicEntry) :
    Decidable (boundary.SkeletonValid parent) := by
  unfold SkeletonValid
  cases boundary.edge <;> infer_instance

theorem arithmeticValid_of_skeleton
    (boundary : DegreeSevenStageSixCompactUpperBoundary)
    (parent : DegreeSevenStageFiveDyadicEntry)
    (hskeleton : boundary.SkeletonValid parent)
    (hedge : boundary.edgeRejections.Forall
      DegreeSevenStageSixMultipleRootWitness.Valid) :
    boundary.ArithmeticValid parent := by
  rcases hskeleton with ⟨hcritical, hupper, hrecord⟩
  refine ⟨hcritical, hupper, ?_⟩
  cases hoption : boundary.edge with
  | none => simpa [hoption] using hrecord
  | some rejection =>
      have hrecord' : rejection.SkeletonValid parent ∧
          rejection.a2 = boundary.critical.a2 - 1 ∧
          boundary.bound = rejection.a2 - 1 := by
        simpa [hoption] using hrecord
      have hexact : rejection.exactWitnesses.Forall
          DegreeSevenStageSixMultipleRootWitness.Valid := by
        simpa [edgeRejections, hoption] using hedge
      have hvalid : rejection.ArithmeticValid parent :=
        rejection.arithmeticValid_of_skeleton_and_exact parent hrecord'.1 hexact
      simpa [hoption] using And.intro hvalid hrecord'.2

instance (boundary : DegreeSevenStageSixCompactUpperBoundary)
    (parent : DegreeSevenStageFiveDyadicEntry) :
    Decidable (boundary.ArithmeticValid parent) := by
  unfold ArithmeticValid
  cases boundary.edge <;> infer_instance

theorem valid_of_arithmeticValid
    (boundary : DegreeSevenStageSixCompactUpperBoundary)
    (parent : DegreeSevenStageFiveDyadicEntry)
    (h : boundary.ArithmeticValid parent) : boundary.Valid parent := by
  rcases h with ⟨hcritical, hupper, hedge⟩
  refine ⟨boundary.critical.valid_of_arithmeticValid parent hcritical,
    hupper, ?_⟩
  cases hoption : boundary.edge with
  | none => simpa [hoption] using hedge
  | some rejection =>
      have hrecord : rejection.ArithmeticValid parent ∧
          rejection.a2 = boundary.critical.a2 - 1 ∧
          boundary.bound = rejection.a2 - 1 := by
        simpa [hoption] using hedge
      simpa [hoption] using And.intro
        (rejection.valid_of_arithmeticValid parent hrecord.1) hrecord.2

theorem not_hunter_of_gt
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (boundary : DegreeSevenStageSixCompactUpperBoundary)
    (parent : DegreeSevenStageFiveDyadicEntry)
    (hparent : parent.Valid) (hvalid : boundary.Valid parent)
    (ha6 : parent.a6 = f.coeff 6) (ha5 : parent.a5 = f.coeff 5)
    (ha4 : parent.a4 = f.coeff 4) (ha3 : parent.a3 = f.coeff 3)
    (ha2 : boundary.bound < f.coeff 2) : False := by
  rcases hvalid with ⟨hrelative, hupper, hedge⟩
  let witness := boundary.critical.toWitness parent
  have hcriticalValid : witness.Valid := by
    exact ⟨hparent, hrelative⟩
  have hcriticalTop : witness.SameTop parent := boundary.critical.sameTop parent
  cases hedgeOption : boundary.edge with
  | none =>
      have hbound : boundary.bound = boundary.critical.a2 - 1 := by
        simpa [hedgeOption] using hedge
      have hle : boundary.critical.a2 ≤ f.coeff 2 := by omega
      exact degreeSeven_criticalSignWitness_excludes_hunter h
        witness hcriticalValid
        (hcriticalTop.1.trans ha6) (hcriticalTop.2.1.trans ha5)
        (hcriticalTop.2.2.1.trans ha4) (hcriticalTop.2.2.2.trans ha3)
        (boundary.critical.excludes_of_isUpper parent hupper hle)
  | some rejection =>
      have hedgeValid : rejection.Valid parent ∧
          rejection.a2 = boundary.critical.a2 - 1 ∧
          boundary.bound = rejection.a2 - 1 := by
        simpa [hedgeOption] using hedge
      by_cases heq : f.coeff 2 = rejection.a2
      · exact rejection.not_hunter_of_eq h parent hparent hedgeValid.1
          ha6 ha5 ha4 ha3 heq.symm
      · have hle : boundary.critical.a2 ≤ f.coeff 2 := by omega
        exact degreeSeven_criticalSignWitness_excludes_hunter h
          witness hcriticalValid
          (hcriticalTop.1.trans ha6) (hcriticalTop.2.1.trans ha5)
          (hcriticalTop.2.2.1.trans ha4) (hcriticalTop.2.2.2.trans ha3)
          (boundary.critical.excludes_of_isUpper parent hupper hle)

end DegreeSevenStageSixCompactUpperBoundary

/-- Complete compact coverage of one Stage Five row. -/
structure DegreeSevenStageSixStrongCompactCoverage where
  parent : DegreeSevenStageFiveDyadicEntry
  lower : DegreeSevenStageSixCompactLowerBoundary
  upper : DegreeSevenStageSixCompactUpperBoundary
  family : Option DegreeSevenStageSixDyadicFamily
deriving DecidableEq, Repr

namespace DegreeSevenStageSixStrongCompactCoverage

def Valid (coverage : DegreeSevenStageSixStrongCompactCoverage) : Prop :=
  coverage.parent.Valid ∧ coverage.lower.Valid coverage.parent ∧
    coverage.upper.Valid coverage.parent ∧
    match coverage.family with
    | none => coverage.upper.bound < coverage.lower.bound
    | some family =>
        family.Valid ∧
          family.a6 = coverage.parent.a6 ∧ family.a5 = coverage.parent.a5 ∧
          family.a4 = coverage.parent.a4 ∧ family.a3 = coverage.parent.a3 ∧
          family.a2Lower = coverage.lower.bound ∧
          family.a2Upper = coverage.upper.bound

def ArithmeticValid
    (coverage : DegreeSevenStageSixStrongCompactCoverage) : Prop :=
  coverage.parent.ArithmeticValid ∧
    coverage.lower.ArithmeticValid coverage.parent ∧
    coverage.upper.ArithmeticValid coverage.parent ∧
    match coverage.family with
    | none => coverage.upper.bound < coverage.lower.bound
    | some family =>
        family.ArithmeticValid ∧
          family.a6 = coverage.parent.a6 ∧ family.a5 = coverage.parent.a5 ∧
          family.a4 = coverage.parent.a4 ∧ family.a3 = coverage.parent.a3 ∧
          family.a2Lower = coverage.lower.bound ∧
          family.a2Upper = coverage.upper.bound

/-- All purely integral checks and edge alignment facts for one coverage. -/
def SkeletonValid
    (coverage : DegreeSevenStageSixStrongCompactCoverage) : Prop :=
  coverage.parent.ArithmeticValid ∧
    coverage.lower.SkeletonValid coverage.parent ∧
    coverage.upper.SkeletonValid coverage.parent ∧
    match coverage.family with
    | none => coverage.upper.bound < coverage.lower.bound
    | some family =>
        family.ArithmeticValid ∧
          family.a6 = coverage.parent.a6 ∧ family.a5 = coverage.parent.a5 ∧
          family.a4 = coverage.parent.a4 ∧ family.a3 = coverage.parent.a3 ∧
          family.a2Lower = coverage.lower.bound ∧
          family.a2Upper = coverage.upper.bound

def edgeRejections
    (coverage : DegreeSevenStageSixStrongCompactCoverage) :
    List DegreeSevenStageSixMultipleRootWitness :=
  coverage.lower.edgeRejections ++ coverage.upper.edgeRejections

instance (coverage : DegreeSevenStageSixStrongCompactCoverage) :
    Decidable coverage.Valid := by
  unfold Valid
  cases coverage.family <;> infer_instance

instance (coverage : DegreeSevenStageSixStrongCompactCoverage) :
    Decidable coverage.SkeletonValid := by
  unfold SkeletonValid
  cases coverage.family <;> infer_instance

theorem arithmeticValid_of_skeleton
    (coverage : DegreeSevenStageSixStrongCompactCoverage)
    (hskeleton : coverage.SkeletonValid)
    (hedges : coverage.edgeRejections.Forall
      DegreeSevenStageSixMultipleRootWitness.Valid) :
    coverage.ArithmeticValid := by
  rcases hskeleton with ⟨hparent, hlower, hupper, hfamily⟩
  have hedgeParts :
      coverage.lower.edgeRejections.Forall
          DegreeSevenStageSixMultipleRootWitness.Valid ∧
        coverage.upper.edgeRejections.Forall
          DegreeSevenStageSixMultipleRootWitness.Valid := by
    simpa [edgeRejections, List.forall_append] using hedges
  exact ⟨hparent,
    coverage.lower.arithmeticValid_of_skeleton coverage.parent
      hlower hedgeParts.1,
    coverage.upper.arithmeticValid_of_skeleton coverage.parent
      hupper hedgeParts.2, hfamily⟩

theorem list_forall_arithmeticValid_of_skeletons_and_edges
    (coverages : List DegreeSevenStageSixStrongCompactCoverage)
    (hskeletons : coverages.Forall SkeletonValid)
    (hedges : (coverages.flatMap edgeRejections).Forall
      DegreeSevenStageSixMultipleRootWitness.Valid) :
    coverages.Forall ArithmeticValid := by
  induction coverages with
  | nil => simp
  | cons coverage coverages induction =>
      simp only [List.forall_cons] at hskeletons ⊢
      simp only [List.flatMap_cons, List.forall_append] at hedges
      exact ⟨coverage.arithmeticValid_of_skeleton
          hskeletons.1 hedges.1,
        induction hskeletons.2 hedges.2⟩

instance (coverage : DegreeSevenStageSixStrongCompactCoverage) :
    Decidable coverage.ArithmeticValid := by
  unfold ArithmeticValid
  cases coverage.family <;> infer_instance

theorem valid_of_arithmeticValid
    (coverage : DegreeSevenStageSixStrongCompactCoverage)
    (h : coverage.ArithmeticValid) : coverage.Valid := by
  rcases h with ⟨hparent, hlower, hupper, hfamily⟩
  refine ⟨coverage.parent.valid_of_arithmeticValid hparent,
    coverage.lower.valid_of_arithmeticValid coverage.parent hlower,
    coverage.upper.valid_of_arithmeticValid coverage.parent hupper, ?_⟩
  cases hoption : coverage.family with
  | none => simpa [hoption] using hfamily
  | some family =>
      simp only [hoption] at hfamily
      simp only
      exact ⟨family.valid_of_arithmeticValid hfamily.1, hfamily.2⟩

theorem hunter_a2_mem_family
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (coverage : DegreeSevenStageSixStrongCompactCoverage)
    (hvalid : coverage.Valid)
    (ha6 : coverage.parent.a6 = f.coeff 6)
    (ha5 : coverage.parent.a5 = f.coeff 5)
    (ha4 : coverage.parent.a4 = f.coeff 4)
    (ha3 : coverage.parent.a3 = f.coeff 3) :
    ∃ family,
      coverage.family = some family ∧ family.Valid ∧
      f.coeff 2 ∈ family.toFamily.a2Candidates := by
  rcases hvalid with ⟨hparent, hlower, hupper, hfamily⟩
  cases hfamilyOption : coverage.family with
  | none =>
      have hgap : coverage.upper.bound < coverage.lower.bound := by
        simpa [hfamilyOption] using hfamily
      by_cases hlt : f.coeff 2 < coverage.lower.bound
      · exact (coverage.lower.not_hunter_of_lt h coverage.parent hparent hlower
          ha6 ha5 ha4 ha3 hlt).elim
      · have hgt : coverage.upper.bound < f.coeff 2 := by omega
        exact (coverage.upper.not_hunter_of_gt h coverage.parent hparent hupper
          ha6 ha5 ha4 ha3 hgt).elim
  | some family =>
      have hfamilyValid : family.Valid ∧
          family.a6 = coverage.parent.a6 ∧ family.a5 = coverage.parent.a5 ∧
          family.a4 = coverage.parent.a4 ∧ family.a3 = coverage.parent.a3 ∧
          family.a2Lower = coverage.lower.bound ∧
          family.a2Upper = coverage.upper.bound := by
        simpa [hfamilyOption] using hfamily
      have hlowerBound : coverage.lower.bound ≤ f.coeff 2 := by
        by_contra hnot
        exact coverage.lower.not_hunter_of_lt h coverage.parent hparent hlower
          ha6 ha5 ha4 ha3 (by omega)
      have hupperBound : f.coeff 2 ≤ coverage.upper.bound := by
        by_contra hnot
        exact coverage.upper.not_hunter_of_gt h coverage.parent hparent hupper
          ha6 ha5 ha4 ha3 (by omega)
      have ha2 : f.coeff 2 ∈ family.toFamily.a2Candidates := by
        rw [DegreeSevenStageSixFamily.a2Candidates,
          integerIcc, Finset.mem_Icc]
        constructor
        · change family.a2Lower ≤ f.coeff 2
          rw [hfamilyValid.2.2.2.2.2.1]
          exact hlowerBound
        · change f.coeff 2 ≤ family.a2Upper
          rw [hfamilyValid.2.2.2.2.2.2]
          exact hupperBound
      exact ⟨family, rfl, hfamilyValid.1, ha2⟩

theorem hunter_a1_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (coverage : DegreeSevenStageSixStrongCompactCoverage)
    (hvalid : coverage.Valid)
    (ha6 : coverage.parent.a6 = f.coeff 6)
    (ha5 : coverage.parent.a5 = f.coeff 5)
    (ha4 : coverage.parent.a4 = f.coeff 4)
    (ha3 : coverage.parent.a3 = f.coeff 3) :
    ∃ family,
      coverage.family = some family ∧
      f.coeff 2 ∈ family.toFamily.a2Candidates ∧
      f.coeff 1 ∈
        (family.toFamily.toEntry (f.coeff 2)).a1Candidates := by
  obtain ⟨family, hfamily, hfamilyValid, ha2⟩ :=
    coverage.hunter_a2_mem_family h hvalid ha6 ha5 ha4 ha3
  have hrecord := hvalid.2.2.2
  rw [hfamily] at hrecord
  have htop : family.a6 = f.coeff 6 ∧ family.a5 = f.coeff 5 ∧
      family.a4 = f.coeff 4 ∧ family.a3 = f.coeff 3 :=
    ⟨hrecord.2.1.trans ha6, hrecord.2.2.1.trans ha5,
      hrecord.2.2.2.1.trans ha4, hrecord.2.2.2.2.1.trans ha3⟩
  exact ⟨family, hfamily, ha2,
    DegreeSevenStageSixFamily.degreeSeven_minimumHunterCandidate_a1_mem_of_family
      h family.toFamily hfamilyValid htop.1 htop.2.1
        htop.2.2.1 htop.2.2.2 ha2⟩

end DegreeSevenStageSixStrongCompactCoverage

end

end TraceEuclidean
