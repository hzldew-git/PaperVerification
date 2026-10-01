import TraceEuclidean.DegreeSevenRolleStageSixRejected

/-!
# Half-line coverage for the sixth degree-seven Rolle stage

Strict critical signs are monotone in the constant coefficient.  A lower
boundary therefore excludes every smaller integer, while an upper boundary
excludes every larger integer.  An optional common-root witness handles the
single equality value between a strict boundary and the surviving interval.
This gives a compact complete coverage without reevaluating the large Stage
Five candidate finsets.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

namespace DegreeSevenStageSixCriticalSignWitness

def SameTop (witness : DegreeSevenStageSixCriticalSignWitness)
    (parent : DegreeSevenStageFiveDyadicEntry) : Prop :=
  witness.parent.a6 = parent.a6 ∧ witness.parent.a5 = parent.a5 ∧
    witness.parent.a4 = parent.a4 ∧ witness.parent.a3 = parent.a3

instance (witness : DegreeSevenStageSixCriticalSignWitness)
    (parent : DegreeSevenStageFiveDyadicEntry) :
    Decidable (witness.SameTop parent) := by
  unfold SameTop
  infer_instance

def IsLower (witness : DegreeSevenStageSixCriticalSignWitness) : Prop :=
  witness.point = .first ∨ witness.point = .third

def IsUpper (witness : DegreeSevenStageSixCriticalSignWitness) : Prop :=
  witness.point = .second ∨ witness.point = .fourth

instance (witness : DegreeSevenStageSixCriticalSignWitness) :
    Decidable witness.IsLower := by
  unfold IsLower
  infer_instance

instance (witness : DegreeSevenStageSixCriticalSignWitness) :
    Decidable witness.IsUpper := by
  unfold IsUpper
  infer_instance

theorem excludes_of_isLower (witness : DegreeSevenStageSixCriticalSignWitness)
    (hlower : witness.IsLower) {a2 : ℤ} (ha2 : a2 ≤ witness.a2) :
    witness.Excludes a2 := by
  rcases hlower with hpoint | hpoint
  · simp [Excludes, hpoint, ha2]
  · simp [Excludes, hpoint, ha2]

theorem excludes_of_isUpper (witness : DegreeSevenStageSixCriticalSignWitness)
    (hupper : witness.IsUpper) {a2 : ℤ} (ha2 : witness.a2 ≤ a2) :
    witness.Excludes a2 := by
  rcases hupper with hpoint | hpoint
  · simp [Excludes, hpoint, ha2]
  · simp [Excludes, hpoint, ha2]

end DegreeSevenStageSixCriticalSignWitness

namespace DegreeSevenStageSixMultipleRootWitness

def SameTop (witness : DegreeSevenStageSixMultipleRootWitness)
    (parent : DegreeSevenStageFiveDyadicEntry) : Prop :=
  witness.a6 = parent.a6 ∧ witness.a5 = parent.a5 ∧
    witness.a4 = parent.a4 ∧ witness.a3 = parent.a3

instance (witness : DegreeSevenStageSixMultipleRootWitness)
    (parent : DegreeSevenStageFiveDyadicEntry) :
    Decidable (witness.SameTop parent) := by
  unfold SameTop
  infer_instance

end DegreeSevenStageSixMultipleRootWitness

/-- A strict lower half-line exclusion, with an optional multiple-root value
immediately before the surviving lower bound. -/
structure DegreeSevenStageSixLowerBoundary where
  bound : ℤ
  critical : DegreeSevenStageSixCriticalSignWitness
  multiple : Option DegreeSevenStageSixMultipleRootWitness
deriving DecidableEq, Repr

namespace DegreeSevenStageSixLowerBoundary

def Valid (boundary : DegreeSevenStageSixLowerBoundary)
    (parent : DegreeSevenStageFiveDyadicEntry) : Prop :=
  boundary.critical.Valid ∧ boundary.critical.SameTop parent ∧
    boundary.critical.IsLower ∧
    match boundary.multiple with
    | none => boundary.bound = boundary.critical.a2 + 1
    | some witness =>
        witness.Valid ∧ witness.SameTop parent ∧
          witness.a2 = boundary.critical.a2 + 1 ∧
          boundary.bound = witness.a2 + 1

instance (boundary : DegreeSevenStageSixLowerBoundary)
    (parent : DegreeSevenStageFiveDyadicEntry) :
    Decidable (boundary.Valid parent) := by
  unfold Valid
  cases boundary.multiple <;> infer_instance

/-- Every integer below a valid lower boundary is impossible for a Hunter
septic with matching top coefficients. -/
theorem not_hunter_of_lt
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (boundary : DegreeSevenStageSixLowerBoundary)
    (parent : DegreeSevenStageFiveDyadicEntry)
    (hvalid : boundary.Valid parent)
    (ha6 : parent.a6 = f.coeff 6) (ha5 : parent.a5 = f.coeff 5)
    (ha4 : parent.a4 = f.coeff 4) (ha3 : parent.a3 = f.coeff 3)
    (ha2 : f.coeff 2 < boundary.bound) : False := by
  rcases hvalid with ⟨hcritical, hcriticalTop, hcriticalLower, hboundary⟩
  cases hmultiple : boundary.multiple with
  | none =>
      have hbound : boundary.bound = boundary.critical.a2 + 1 := by
        simpa [hmultiple] using hboundary
      have hle : f.coeff 2 ≤ boundary.critical.a2 := by omega
      exact degreeSeven_criticalSignWitness_excludes_hunter h
        boundary.critical hcritical
        (hcriticalTop.1.trans ha6) (hcriticalTop.2.1.trans ha5)
        (hcriticalTop.2.2.1.trans ha4) (hcriticalTop.2.2.2.trans ha3)
        (boundary.critical.excludes_of_isLower hcriticalLower hle)
  | some witness =>
      have hmultipleValid : witness.Valid ∧ witness.SameTop parent ∧
          witness.a2 = boundary.critical.a2 + 1 ∧
          boundary.bound = witness.a2 + 1 := by
        simpa [hmultiple] using hboundary
      by_cases heq : f.coeff 2 = witness.a2
      · exact degreeSeven_multipleRootWitness_not_hunter h witness
          hmultipleValid.1
          (hmultipleValid.2.1.1.trans ha6)
          (hmultipleValid.2.1.2.1.trans ha5)
          (hmultipleValid.2.1.2.2.1.trans ha4)
          (hmultipleValid.2.1.2.2.2.trans ha3) heq.symm
      · have hle : f.coeff 2 ≤ boundary.critical.a2 := by omega
        exact degreeSeven_criticalSignWitness_excludes_hunter h
          boundary.critical hcritical
          (hcriticalTop.1.trans ha6) (hcriticalTop.2.1.trans ha5)
          (hcriticalTop.2.2.1.trans ha4) (hcriticalTop.2.2.2.trans ha3)
          (boundary.critical.excludes_of_isLower hcriticalLower hle)

end DegreeSevenStageSixLowerBoundary

/-- A strict upper half-line exclusion, with an optional multiple-root value
immediately after the surviving upper bound. -/
structure DegreeSevenStageSixUpperBoundary where
  bound : ℤ
  critical : DegreeSevenStageSixCriticalSignWitness
  multiple : Option DegreeSevenStageSixMultipleRootWitness
deriving DecidableEq, Repr

namespace DegreeSevenStageSixUpperBoundary

def Valid (boundary : DegreeSevenStageSixUpperBoundary)
    (parent : DegreeSevenStageFiveDyadicEntry) : Prop :=
  boundary.critical.Valid ∧ boundary.critical.SameTop parent ∧
    boundary.critical.IsUpper ∧
    match boundary.multiple with
    | none => boundary.bound = boundary.critical.a2 - 1
    | some witness =>
        witness.Valid ∧ witness.SameTop parent ∧
          witness.a2 = boundary.critical.a2 - 1 ∧
          boundary.bound = witness.a2 - 1

instance (boundary : DegreeSevenStageSixUpperBoundary)
    (parent : DegreeSevenStageFiveDyadicEntry) :
    Decidable (boundary.Valid parent) := by
  unfold Valid
  cases boundary.multiple <;> infer_instance

/-- Every integer above a valid upper boundary is impossible for a Hunter
septic with matching top coefficients. -/
theorem not_hunter_of_gt
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (boundary : DegreeSevenStageSixUpperBoundary)
    (parent : DegreeSevenStageFiveDyadicEntry)
    (hvalid : boundary.Valid parent)
    (ha6 : parent.a6 = f.coeff 6) (ha5 : parent.a5 = f.coeff 5)
    (ha4 : parent.a4 = f.coeff 4) (ha3 : parent.a3 = f.coeff 3)
    (ha2 : boundary.bound < f.coeff 2) : False := by
  rcases hvalid with ⟨hcritical, hcriticalTop, hcriticalUpper, hboundary⟩
  cases hmultiple : boundary.multiple with
  | none =>
      have hbound : boundary.bound = boundary.critical.a2 - 1 := by
        simpa [hmultiple] using hboundary
      have hle : boundary.critical.a2 ≤ f.coeff 2 := by omega
      exact degreeSeven_criticalSignWitness_excludes_hunter h
        boundary.critical hcritical
        (hcriticalTop.1.trans ha6) (hcriticalTop.2.1.trans ha5)
        (hcriticalTop.2.2.1.trans ha4) (hcriticalTop.2.2.2.trans ha3)
        (boundary.critical.excludes_of_isUpper hcriticalUpper hle)
  | some witness =>
      have hmultipleValid : witness.Valid ∧ witness.SameTop parent ∧
          witness.a2 = boundary.critical.a2 - 1 ∧
          boundary.bound = witness.a2 - 1 := by
        simpa [hmultiple] using hboundary
      by_cases heq : f.coeff 2 = witness.a2
      · exact degreeSeven_multipleRootWitness_not_hunter h witness
          hmultipleValid.1
          (hmultipleValid.2.1.1.trans ha6)
          (hmultipleValid.2.1.2.1.trans ha5)
          (hmultipleValid.2.1.2.2.1.trans ha4)
          (hmultipleValid.2.1.2.2.2.trans ha3) heq.symm
      · have hle : boundary.critical.a2 ≤ f.coeff 2 := by omega
        exact degreeSeven_criticalSignWitness_excludes_hunter h
          boundary.critical hcritical
          (hcriticalTop.1.trans ha6) (hcriticalTop.2.1.trans ha5)
          (hcriticalTop.2.2.1.trans ha4) (hcriticalTop.2.2.2.trans ha3)
          (boundary.critical.excludes_of_isUpper hcriticalUpper hle)

end DegreeSevenStageSixUpperBoundary

/-- Strong complete coverage of one Stage Five row by two half-line
boundaries and an optional surviving family. -/
structure DegreeSevenStageSixStrongCoverage where
  parent : DegreeSevenStageFiveDyadicEntry
  lower : DegreeSevenStageSixLowerBoundary
  upper : DegreeSevenStageSixUpperBoundary
  family : Option DegreeSevenStageSixDyadicFamily
deriving DecidableEq, Repr

namespace DegreeSevenStageSixStrongCoverage

def Valid (coverage : DegreeSevenStageSixStrongCoverage) : Prop :=
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

/-- Efficient generated form of strong-coverage validity.  The compact
parent and surviving family are checked using cleared-denominator integer
arithmetic, while the two boundary witnesses retain their exact rational
validity predicates. -/
def ArithmeticValid (coverage : DegreeSevenStageSixStrongCoverage) : Prop :=
  coverage.parent.ArithmeticValid ∧ coverage.lower.Valid coverage.parent ∧
    coverage.upper.Valid coverage.parent ∧
    match coverage.family with
    | none => coverage.upper.bound < coverage.lower.bound
    | some family =>
        family.ArithmeticValid ∧
          family.a6 = coverage.parent.a6 ∧ family.a5 = coverage.parent.a5 ∧
          family.a4 = coverage.parent.a4 ∧ family.a3 = coverage.parent.a3 ∧
          family.a2Lower = coverage.lower.bound ∧
          family.a2Upper = coverage.upper.bound

instance (coverage : DegreeSevenStageSixStrongCoverage) :
    Decidable coverage.ArithmeticValid := by
  unfold ArithmeticValid
  cases coverage.family <;> infer_instance

instance (coverage : DegreeSevenStageSixStrongCoverage) :
    Decidable coverage.Valid := by
  unfold Valid
  cases coverage.family <;> infer_instance

/-- The efficient integer checks imply the proof-facing strong coverage. -/
theorem valid_of_arithmeticValid
    (coverage : DegreeSevenStageSixStrongCoverage)
    (h : coverage.ArithmeticValid) : coverage.Valid := by
  rcases h with ⟨hparent, hlower, hupper, hfamily⟩
  refine ⟨coverage.parent.valid_of_arithmeticValid hparent,
    hlower, hupper, ?_⟩
  cases hoption : coverage.family with
  | none =>
      simpa [hoption] using hfamily
  | some family =>
      simp only [hoption] at hfamily
      simp only
      exact ⟨family.valid_of_arithmeticValid hfamily.1, hfamily.2⟩

/-- A valid strong coverage with matching top coefficients necessarily has a
surviving family containing the actual `a2`. -/
theorem hunter_a2_mem_family
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (coverage : DegreeSevenStageSixStrongCoverage) (hvalid : coverage.Valid)
    (ha6 : coverage.parent.a6 = f.coeff 6)
    (ha5 : coverage.parent.a5 = f.coeff 5)
    (ha4 : coverage.parent.a4 = f.coeff 4)
    (ha3 : coverage.parent.a3 = f.coeff 3) :
    ∃ family,
      coverage.family = some family ∧ family.Valid ∧
      f.coeff 2 ∈ family.toFamily.a2Candidates := by
  rcases hvalid with ⟨_, hlower, hupper, hfamily⟩
  cases hfamilyOption : coverage.family with
  | none =>
      have hgap : coverage.upper.bound < coverage.lower.bound := by
        simpa [hfamilyOption] using hfamily
      by_cases hlt : f.coeff 2 < coverage.lower.bound
      · exact (coverage.lower.not_hunter_of_lt h coverage.parent hlower
          ha6 ha5 ha4 ha3 hlt).elim
      · have hgt : coverage.upper.bound < f.coeff 2 := by omega
        exact (coverage.upper.not_hunter_of_gt h coverage.parent hupper
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
        exact coverage.lower.not_hunter_of_lt h coverage.parent hlower
          ha6 ha5 ha4 ha3 (by omega)
      have hupperBound : f.coeff 2 ≤ coverage.upper.bound := by
        by_contra hnot
        exact coverage.upper.not_hunter_of_gt h coverage.parent hupper
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

/-- Strong coverage yields the exact root-isolated `a1` candidate set. -/
theorem hunter_a1_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (coverage : DegreeSevenStageSixStrongCoverage) (hvalid : coverage.Valid)
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
  have htop : family.a6 = f.coeff 6 ∧ family.a5 = f.coeff 5 ∧
      family.a4 = f.coeff 4 ∧ family.a3 = f.coeff 3 := by
    have hrecord := hvalid.2.2.2
    rw [hfamily] at hrecord
    exact ⟨hrecord.2.1.trans ha6, hrecord.2.2.1.trans ha5,
      hrecord.2.2.2.1.trans ha4, hrecord.2.2.2.2.1.trans ha3⟩
  exact ⟨family, hfamily, ha2,
    DegreeSevenStageSixFamily.degreeSeven_minimumHunterCandidate_a1_mem_of_family
      h family.toFamily hfamilyValid htop.1 htop.2.1
        htop.2.2.1 htop.2.2.2 ha2⟩

end DegreeSevenStageSixStrongCoverage

end

end TraceEuclidean
