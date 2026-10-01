import TraceEuclidean.DegreeSevenRolleStageSixRejected

/-!
# Complete finite coverage interface for the sixth degree-seven Rolle stage

Each checked Stage Five row is partitioned into at most one parametric family
and a finite list of excluded boundary values.  Exact equality of finite sets
turns this data partition into a proof: the actual `a2` of a Hunter septic is
in the family, since either kind of rejection contradicts split separability.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

/-- The two exact reasons by which an `a2` prefix can be rejected. -/
inductive DegreeSevenStageSixRejection where
  | multipleRoot (witness : DegreeSevenStageSixMultipleRootWitness)
  | criticalSign (witness : DegreeSevenStageSixCriticalSignWitness)
deriving DecidableEq, Repr

namespace DegreeSevenStageSixRejection

def a2 : DegreeSevenStageSixRejection → ℤ
  | .multipleRoot witness => witness.a2
  | .criticalSign witness => witness.a2

def Valid : DegreeSevenStageSixRejection → Prop
  | .multipleRoot witness => witness.Valid
  | .criticalSign witness => witness.Valid

instance (rejection : DegreeSevenStageSixRejection) :
    Decidable rejection.Valid := by
  cases rejection with
  | multipleRoot witness => exact inferInstanceAs (Decidable witness.Valid)
  | criticalSign witness => exact inferInstanceAs (Decidable witness.Valid)

def SameTop (rejection : DegreeSevenStageSixRejection)
    (parent : DegreeSevenStageFiveDyadicEntry) : Prop :=
  match rejection with
  | .multipleRoot witness =>
      witness.a6 = parent.a6 ∧ witness.a5 = parent.a5 ∧
        witness.a4 = parent.a4 ∧ witness.a3 = parent.a3
  | .criticalSign witness =>
      witness.parent.a6 = parent.a6 ∧ witness.parent.a5 = parent.a5 ∧
        witness.parent.a4 = parent.a4 ∧ witness.parent.a3 = parent.a3

instance (rejection : DegreeSevenStageSixRejection)
    (parent : DegreeSevenStageFiveDyadicEntry) :
    Decidable (rejection.SameTop parent) := by
  cases rejection <;> unfold SameTop <;> infer_instance

end DegreeSevenStageSixRejection

/-- One exact partition of the `a2` candidates attached to a Stage Five row. -/
structure DegreeSevenStageSixCoverage where
  parent : DegreeSevenStageFiveDyadicEntry
  candidateLower : ℤ
  candidateUpper : ℤ
  family : Option DegreeSevenStageSixDyadicFamily
  rejections : List DegreeSevenStageSixRejection
deriving DecidableEq, Repr

namespace DegreeSevenStageSixCoverage

def familyA2 (coverage : DegreeSevenStageSixCoverage) : Finset ℤ :=
  match coverage.family with
  | none => ∅
  | some family => family.toFamily.a2Candidates

def rejectedA2 (coverage : DegreeSevenStageSixCoverage) : Finset ℤ :=
  coverage.rejections.toFinset.image DegreeSevenStageSixRejection.a2

def coveredA2 (coverage : DegreeSevenStageSixCoverage) : Finset ℤ :=
  coverage.familyA2 ∪ coverage.rejectedA2

def computedLower (coverage : DegreeSevenStageSixCoverage) : ℤ :=
  quinticTranslationLowerBound coverage.parent.toEntry.baseCoefficients
    coverage.parent.toEntry.rightEndpoint coverage.parent.toEntry.firstRoot
      coverage.parent.toEntry.thirdRoot

def computedUpper (coverage : DegreeSevenStageSixCoverage) : ℤ :=
  quinticTranslationUpperBound coverage.parent.toEntry.baseCoefficients
    coverage.parent.toEntry.leftEndpoint coverage.parent.toEntry.secondRoot
      coverage.parent.toEntry.fourthRoot

def FamilySameTop (family : DegreeSevenStageSixDyadicFamily)
    (parent : DegreeSevenStageFiveDyadicEntry) : Prop :=
  family.a6 = parent.a6 ∧ family.a5 = parent.a5 ∧
    family.a4 = parent.a4 ∧ family.a3 = parent.a3

instance (family : DegreeSevenStageSixDyadicFamily)
    (parent : DegreeSevenStageFiveDyadicEntry) :
    Decidable (FamilySameTop family parent) := by
  unfold FamilySameTop
  infer_instance

/-- The family and every rejection are valid, share the parent coefficients,
and partition exactly the parent's finite `a2` candidate set. -/
def Valid (coverage : DegreeSevenStageSixCoverage) : Prop :=
  coverage.parent.Valid ∧
    (match coverage.family with
      | none => True
      | some family => family.Valid ∧ FamilySameTop family coverage.parent) ∧
    coverage.rejections.Forall (fun rejection =>
      rejection.Valid ∧ rejection.SameTop coverage.parent) ∧
    coverage.computedLower = coverage.candidateLower ∧
    coverage.computedUpper = coverage.candidateUpper ∧
    integerIcc coverage.candidateLower coverage.candidateUpper =
      coverage.coveredA2

/-- Generated files check the compact integer form of family validity. -/
def ArithmeticValid (coverage : DegreeSevenStageSixCoverage) : Prop :=
  coverage.parent.ArithmeticValid ∧
    (match coverage.family with
      | none => True
      | some family =>
          family.ArithmeticValid ∧ FamilySameTop family coverage.parent) ∧
    coverage.rejections.Forall (fun rejection =>
      rejection.Valid ∧ rejection.SameTop coverage.parent) ∧
    coverage.computedLower = coverage.candidateLower ∧
    coverage.computedUpper = coverage.candidateUpper ∧
    integerIcc coverage.candidateLower coverage.candidateUpper =
      coverage.coveredA2

instance (coverage : DegreeSevenStageSixCoverage) :
    Decidable coverage.ArithmeticValid := by
  unfold ArithmeticValid
  cases coverage.family <;> infer_instance

instance (coverage : DegreeSevenStageSixCoverage) :
    Decidable coverage.Valid := by
  unfold Valid
  cases coverage.family <;> infer_instance

/-- The fast generated check has the same proof-facing conclusion. -/
theorem valid_of_arithmeticValid
    (coverage : DegreeSevenStageSixCoverage)
    (h : coverage.ArithmeticValid) : coverage.Valid := by
  rcases h with
    ⟨hparent, hfamily, hrejections, hlower, hupper, hcovered⟩
  refine ⟨coverage.parent.valid_of_arithmeticValid hparent,
    ?_, hrejections, hlower, hupper, hcovered⟩
  cases hfamilyOption : coverage.family with
  | none => trivial
  | some family =>
      have hfamily' : family.ArithmeticValid ∧
          FamilySameTop family coverage.parent := by
        simpa [hfamilyOption] using hfamily
      exact ⟨family.valid_of_arithmeticValid hfamily'.1, hfamily'.2⟩

private theorem rejection_not_hunter
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (parent : DegreeSevenStageFiveDyadicEntry)
    (rejection : DegreeSevenStageSixRejection)
    (hvalid : rejection.Valid) (htop : rejection.SameTop parent)
    (ha6 : parent.a6 = f.coeff 6)
    (ha5 : parent.a5 = f.coeff 5)
    (ha4 : parent.a4 = f.coeff 4)
    (ha3 : parent.a3 = f.coeff 3)
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

private theorem false_of_rejected_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (coverage : DegreeSevenStageSixCoverage)
    (hrejections : coverage.rejections.Forall (fun rejection =>
      rejection.Valid ∧ rejection.SameTop coverage.parent))
    (ha6 : coverage.parent.a6 = f.coeff 6)
    (ha5 : coverage.parent.a5 = f.coeff 5)
    (ha4 : coverage.parent.a4 = f.coeff 4)
    (ha3 : coverage.parent.a3 = f.coeff 3)
    (ha2 : f.coeff 2 ∈ coverage.rejectedA2) : False := by
  rw [rejectedA2, Finset.mem_image] at ha2
  obtain ⟨rejection, hrejectionFinset, hrejectionA2⟩ := ha2
  have hrejection : rejection ∈ coverage.rejections := by
    simpa using hrejectionFinset
  have hrecord := List.forall_iff_forall_mem.mp hrejections rejection hrejection
  exact rejection_not_hunter h coverage.parent rejection hrecord.1 hrecord.2
    ha6 ha5 ha4 ha3 hrejectionA2

/-- The actual `a2` of a Hunter septic must lie in the surviving parametric
family of any valid coverage record with matching top coefficients. -/
theorem hunter_a2_mem_family
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (coverage : DegreeSevenStageSixCoverage) (hvalid : coverage.Valid)
    (ha6 : coverage.parent.a6 = f.coeff 6)
    (ha5 : coverage.parent.a5 = f.coeff 5)
    (ha4 : coverage.parent.a4 = f.coeff 4)
    (ha3 : coverage.parent.a3 = f.coeff 3)
    (ha2 : f.coeff 2 ∈ coverage.parent.a2Candidates) :
    ∃ family,
      coverage.family = some family ∧
      family.Valid ∧ FamilySameTop family coverage.parent ∧
      f.coeff 2 ∈ family.toFamily.a2Candidates := by
  have hcovered : f.coeff 2 ∈ coverage.coveredA2 := by
    have hcandidate :
        f.coeff 2 ∈ integerIcc
          coverage.candidateLower coverage.candidateUpper := by
      have ha2' : f.coeff 2 ∈ integerIcc
          coverage.computedLower coverage.computedUpper := by
        simpa [DegreeSevenStageFiveDyadicEntry.a2Candidates,
          DegreeSevenStageFiveEntry.a2Candidates,
          quinticTranslationCandidates, computedLower, computedUpper] using ha2
      rwa [hvalid.2.2.2.1, hvalid.2.2.2.2.1] at ha2'
    rw [← hvalid.2.2.2.2.2]
    exact hcandidate
  rw [coveredA2, Finset.mem_union] at hcovered
  cases hfamily : coverage.family with
  | none =>
      have hrejected : f.coeff 2 ∈ coverage.rejectedA2 := by
        simpa [familyA2, hfamily] using hcovered
      exact (false_of_rejected_mem h coverage hvalid.2.2.1
        ha6 ha5 ha4 ha3 hrejected).elim
  | some family =>
      have hfamilyValid : family.Valid ∧
          FamilySameTop family coverage.parent := by
        simpa [hfamily] using hvalid.2.1
      rcases hcovered with hfamilyMem | hrejected
      · have hmem : f.coeff 2 ∈ family.toFamily.a2Candidates := by
          simpa [familyA2, hfamily] using hfamilyMem
        exact ⟨family, rfl, hfamilyValid.1, hfamilyValid.2, hmem⟩
      · exact (false_of_rejected_mem h coverage hvalid.2.2.1
          ha6 ha5 ha4 ha3 hrejected).elim

/-- A complete coverage record yields the sharpened root-isolated `a1` set. -/
theorem hunter_a1_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (coverage : DegreeSevenStageSixCoverage) (hvalid : coverage.Valid)
    (ha6 : coverage.parent.a6 = f.coeff 6)
    (ha5 : coverage.parent.a5 = f.coeff 5)
    (ha4 : coverage.parent.a4 = f.coeff 4)
    (ha3 : coverage.parent.a3 = f.coeff 3)
    (ha2 : f.coeff 2 ∈ coverage.parent.a2Candidates) :
    ∃ family,
      coverage.family = some family ∧
      f.coeff 2 ∈ family.toFamily.a2Candidates ∧
      f.coeff 1 ∈
        (family.toFamily.toEntry (f.coeff 2)).a1Candidates := by
  obtain ⟨family, hfamily, hfamilyValid, htop, ha2Family⟩ :=
    coverage.hunter_a2_mem_family h hvalid ha6 ha5 ha4 ha3 ha2
  have hfamilyGeneral : family.toFamily.Valid := hfamilyValid
  exact ⟨family, hfamily, ha2Family,
    DegreeSevenStageSixFamily.degreeSeven_minimumHunterCandidate_a1_mem_of_family h
      family.toFamily hfamilyGeneral
      (htop.1.trans ha6) (htop.2.1.trans ha5)
      (htop.2.2.1.trans ha4) (htop.2.2.2.trans ha3) ha2Family⟩

end DegreeSevenStageSixCoverage

end

end TraceEuclidean
