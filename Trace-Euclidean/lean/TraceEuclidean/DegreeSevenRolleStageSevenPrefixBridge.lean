import TraceEuclidean.DegreeSevenRolleStageSixPiecewise
import TraceEuclidean.DegreeSevenRolleStageSixScaledCandidates
import TraceEuclidean.DegreeSevenRolleStageSevenRejectedScaled

/-!
# Finite-prefix bridge for the degree-seven final Rolle stage

This module gives data-independent list constructions that connect the
coefficient pairs enumerated by a Stage Six piecewise cover with the three
possible Stage Seven certificate classes.
-/

namespace TraceEuclidean

/-- A definitionally computable list version of the closed integer interval.
It is used by generated finite-prefix checks, where sorting a `Finset` would
otherwise block kernel reduction. -/
def integerIccList (lower upper : ℤ) : List ℤ :=
  (List.range (Int.toNat (upper - lower + 1))).map fun (n : ℕ) =>
    lower + (n : ℤ)

theorem mem_integerIccList {lower upper x : ℤ} :
    x ∈ integerIccList lower upper ↔
      lower ≤ x ∧ x ≤ upper := by
  unfold integerIccList
  constructor
  · intro hx
    rcases List.mem_map.mp hx with ⟨n, hn, rfl⟩
    have hnrange : n < Int.toNat (upper - lower + 1) :=
      List.mem_range.mp hn
    have hn0 : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
    have hlt : (n : ℤ) < upper - lower + 1 :=
      Int.lt_toNat.mp hnrange
    omega
  · intro h
    have hdiff : 0 ≤ x - lower := by omega
    have hcast : ((Int.toNat (x - lower) : ℕ) : ℤ) = x - lower :=
      Int.toNat_of_nonneg hdiff
    apply List.mem_map.mpr
    refine ⟨Int.toNat (x - lower), List.mem_range.mpr ?_, ?_⟩
    · apply Int.lt_toNat.mpr
      rw [hcast]
      omega
    · rw [hcast]
      omega

theorem mem_integerIccList_iff_mem_integerIcc
    {lower upper x : ℤ} :
    x ∈ integerIccList lower upper ↔
      x ∈ integerIcc lower upper := by
  rw [mem_integerIccList]
  simp [integerIcc]

/-- The six nonconstant coefficients fixed before the final `a0` step. -/
structure DegreeSevenStageSevenPrefix where
  a6 : ℤ
  a5 : ℤ
  a4 : ℤ
  a3 : ℤ
  a2 : ℤ
  a1 : ℤ
deriving DecidableEq, Repr

namespace DegreeSevenStageSevenPrefix

def ofScaledEntry (entry : DegreeSevenStageSevenScaledEntry) :
    DegreeSevenStageSevenPrefix :=
  ⟨entry.a6, entry.a5, entry.a4, entry.a3, entry.a2, entry.a1⟩

def ofMultipleRootWitness
    (witness : DegreeSevenStageSevenMultipleRootWitness) :
    DegreeSevenStageSevenPrefix :=
  ⟨witness.a6, witness.a5, witness.a4, witness.a3,
    witness.a2, witness.a1⟩

def ofScaledCriticalSignWitness
    (witness : DegreeSevenStageSevenScaledCriticalSignWitness) :
    DegreeSevenStageSevenPrefix :=
  ⟨witness.parent.a6, witness.parent.a5, witness.parent.a4,
    witness.parent.a3, witness.a2, witness.a1⟩

end DegreeSevenStageSevenPrefix

/-- A Stage Seven outcome, kept in the same order as its Stage Six candidate.
Each constructor retains the mathematical certificate used for that outcome. -/
inductive DegreeSevenStageSevenClassification where
  | scaled (entry : DegreeSevenStageSevenScaledEntry)
  | multipleRoot (witness : DegreeSevenStageSevenMultipleRootWitness)
  | criticalSign (witness : DegreeSevenStageSevenScaledCriticalSignWitness)
deriving DecidableEq, Repr

namespace DegreeSevenStageSevenClassification

def toPrefix : DegreeSevenStageSevenClassification →
    DegreeSevenStageSevenPrefix
  | .scaled entry => DegreeSevenStageSevenPrefix.ofScaledEntry entry
  | .multipleRoot witness =>
      DegreeSevenStageSevenPrefix.ofMultipleRootWitness witness
  | .criticalSign witness =>
      DegreeSevenStageSevenPrefix.ofScaledCriticalSignWitness witness

def scaledEntries : List DegreeSevenStageSevenClassification →
    List DegreeSevenStageSevenScaledEntry
  | [] => []
  | .scaled entry :: classifications =>
      entry :: scaledEntries classifications
  | _ :: classifications => scaledEntries classifications

def multipleRoots : List DegreeSevenStageSevenClassification →
    List DegreeSevenStageSevenMultipleRootWitness
  | [] => []
  | .multipleRoot witness :: classifications =>
      witness :: multipleRoots classifications
  | _ :: classifications => multipleRoots classifications

def criticalSigns : List DegreeSevenStageSevenClassification →
    List DegreeSevenStageSevenScaledCriticalSignWitness
  | [] => []
  | .criticalSign witness :: classifications =>
      witness :: criticalSigns classifications
  | _ :: classifications => criticalSigns classifications

@[simp] theorem scaledEntries_append
    (left right : List DegreeSevenStageSevenClassification) :
    scaledEntries (left ++ right) =
      scaledEntries left ++ scaledEntries right := by
  induction left with
  | nil => rfl
  | cons classification left ih =>
      cases classification <;> simp [scaledEntries, ih]

@[simp] theorem multipleRoots_append
    (left right : List DegreeSevenStageSevenClassification) :
    multipleRoots (left ++ right) =
      multipleRoots left ++ multipleRoots right := by
  induction left with
  | nil => rfl
  | cons classification left ih =>
      cases classification <;> simp [multipleRoots, ih]

@[simp] theorem criticalSigns_append
    (left right : List DegreeSevenStageSevenClassification) :
    criticalSigns (left ++ right) =
      criticalSigns left ++ criticalSigns right := by
  induction left with
  | nil => rfl
  | cons classification left ih =>
      cases classification <;> simp [criticalSigns, ih]

def Valid : DegreeSevenStageSevenClassification → Prop
  | .scaled entry => entry.toEntry.Valid
  | .multipleRoot witness => witness.Valid
  | .criticalSign witness => witness.toWitness.Valid

theorem forall_valid_of_projections
    {classifications : List DegreeSevenStageSevenClassification}
    (hscaled : (scaledEntries classifications).Forall
      (fun entry => entry.toEntry.Valid))
    (hmultiple : (multipleRoots classifications).Forall
      DegreeSevenStageSevenMultipleRootWitness.Valid)
    (hcritical : (criticalSigns classifications).Forall
      (fun witness => witness.toWitness.Valid)) :
    classifications.Forall Valid := by
  revert hscaled hmultiple hcritical
  induction classifications with
  | nil => simp
  | cons classification classifications ih =>
      intro hscaled hmultiple hcritical
      cases classification with
      | scaled entry =>
          simp only [scaledEntries, multipleRoots, criticalSigns,
            List.forall_cons] at hscaled hmultiple hcritical ⊢
          exact ⟨hscaled.1,
            ih hscaled.2 hmultiple hcritical⟩
      | multipleRoot witness =>
          simp only [scaledEntries, multipleRoots, criticalSigns,
            List.forall_cons] at hscaled hmultiple hcritical ⊢
          exact ⟨hmultiple.1,
            ih hscaled hmultiple.2 hcritical⟩
      | criticalSign witness =>
          simp only [scaledEntries, multipleRoots, criticalSigns,
            List.forall_cons] at hscaled hmultiple hcritical ⊢
          exact ⟨hcritical.1,
            ih hscaled hmultiple hcritical.2⟩

theorem scaledEntries_forall_valid
    {classifications : List DegreeSevenStageSevenClassification}
    (hvalid : classifications.Forall Valid) :
    (scaledEntries classifications).Forall
      (fun entry => entry.toEntry.Valid) := by
  induction classifications with
  | nil => exact trivial
  | cons classification classifications ih =>
      have hparts : Valid classification ∧ classifications.Forall Valid := by
        simpa only [List.forall_cons] using hvalid
      cases classification with
      | scaled entry =>
          have hentry : entry.toEntry.Valid := by
            simpa only [Valid] using hparts.1
          simpa only [scaledEntries, List.forall_cons] using
            (And.intro hentry (ih hparts.2))
      | multipleRoot witness =>
          exact ih hparts.2
      | criticalSign witness =>
          exact ih hparts.2

theorem multipleRoots_forall_valid
    {classifications : List DegreeSevenStageSevenClassification}
    (hvalid : classifications.Forall Valid) :
    (multipleRoots classifications).Forall
      DegreeSevenStageSevenMultipleRootWitness.Valid := by
  induction classifications with
  | nil => exact trivial
  | cons classification classifications ih =>
      have hparts : Valid classification ∧ classifications.Forall Valid := by
        simpa only [List.forall_cons] using hvalid
      cases classification with
      | scaled entry =>
          exact ih hparts.2
      | multipleRoot witness =>
          have hwitness : witness.Valid := by
            simpa only [Valid] using hparts.1
          simpa only [multipleRoots, List.forall_cons] using
            (And.intro hwitness (ih hparts.2))
      | criticalSign witness =>
          exact ih hparts.2

theorem criticalSigns_forall_valid
    {classifications : List DegreeSevenStageSevenClassification}
    (hvalid : classifications.Forall Valid) :
    (criticalSigns classifications).Forall
      (fun witness => witness.toWitness.Valid) := by
  induction classifications with
  | nil => exact trivial
  | cons classification classifications ih =>
      have hparts : Valid classification ∧ classifications.Forall Valid := by
        simpa only [List.forall_cons] using hvalid
      cases classification with
      | scaled entry =>
          exact ih hparts.2
      | multipleRoot witness =>
          exact ih hparts.2
      | criticalSign witness =>
          have hwitness : witness.toWitness.Valid := by
            simpa only [Valid] using hparts.1
          simpa only [criticalSigns, List.forall_cons] using
            (And.intro hwitness (ih hparts.2))

end DegreeSevenStageSevenClassification

/-- All Stage Six coefficient prefixes represented by a list of piecewise
covers. -/
def degreeSevenStageSixPrefixes
    (refinements : List DegreeSevenStageSixPiecewiseCoverage) :
    List DegreeSevenStageSevenPrefix :=
  refinements.flatMap fun refinement =>
    refinement.pieces.flatMap fun piece =>
      integerIccList piece.a2Lower piece.a2Upper |>.flatMap fun a2 =>
        integerIccList (piece.scaledA1LowerBound a2)
          (piece.scaledA1UpperBound a2) |>.map fun a1 =>
          ⟨refinement.coverage.parent.a6,
            refinement.coverage.parent.a5,
            refinement.coverage.parent.a4,
            refinement.coverage.parent.a3, a2, a1⟩

theorem DegreeSevenStageSixPiecewiseCoverage.prefix_mem
    {refinements : List DegreeSevenStageSixPiecewiseCoverage}
    (refinement : DegreeSevenStageSixPiecewiseCoverage)
    (hrefinement : refinement ∈ refinements)
    (piece : DegreeSevenStageSixScaledFamily)
    (hpiece : piece ∈ refinement.pieces)
    (hpieceValid : piece.ArithmeticValid)
    (a2 a1 : ℤ) (ha2 : a2 ∈ piece.toFamily.a2Candidates)
    (ha1 : a1 ∈ (piece.toFamily.toEntry a2).a1Candidates) :
    { a6 := refinement.coverage.parent.a6
      a5 := refinement.coverage.parent.a5
      a4 := refinement.coverage.parent.a4
      a3 := refinement.coverage.parent.a3
      a2 := a2
      a1 := a1 : DegreeSevenStageSevenPrefix } ∈
        degreeSevenStageSixPrefixes refinements := by
  have ha1Scaled : a1 ∈ piece.scaledA1Candidates a2 := by
    rw [← piece.a1Candidates_eq_scaledA1Candidates a2 hpieceValid]
    exact ha1
  have ha2List : a2 ∈ integerIccList piece.a2Lower piece.a2Upper := by
    rw [mem_integerIccList_iff_mem_integerIcc]
    simpa [DegreeSevenStageSixFamily.a2Candidates,
      DegreeSevenStageSixScaledFamily.toFamily] using ha2
  have ha1List :
      a1 ∈ integerIccList (piece.scaledA1LowerBound a2)
        (piece.scaledA1UpperBound a2) := by
    rw [mem_integerIccList_iff_mem_integerIcc]
    simpa [DegreeSevenStageSixScaledFamily.scaledA1Candidates] using
      ha1Scaled
  simp only [degreeSevenStageSixPrefixes, List.mem_flatMap,
    List.mem_map]
  exact ⟨refinement, hrefinement, piece, hpiece, a2, ha2List,
    a1, ha1List, rfl⟩

/-- Prefixes equipped with a six-root certificate, a rational multiple-root
rejection, or a scaled critical-sign rejection. -/
def degreeSevenStageSevenClassifiedPrefixes
    (entries : List DegreeSevenStageSevenScaledEntry)
    (multipleRoots : List DegreeSevenStageSevenMultipleRootWitness)
    (criticalSigns :
      List DegreeSevenStageSevenScaledCriticalSignWitness) :
    List DegreeSevenStageSevenPrefix :=
  entries.map DegreeSevenStageSevenPrefix.ofScaledEntry ++
    multipleRoots.map
      DegreeSevenStageSevenPrefix.ofMultipleRootWitness ++
  criticalSigns.map
      DegreeSevenStageSevenPrefix.ofScaledCriticalSignWitness

theorem degreeSevenStageSevenClassification_prefixes_toFinset
    (classifications : List DegreeSevenStageSevenClassification) :
    (classifications.map
      DegreeSevenStageSevenClassification.toPrefix).toFinset =
      (degreeSevenStageSevenClassifiedPrefixes
        (DegreeSevenStageSevenClassification.scaledEntries classifications)
        (DegreeSevenStageSevenClassification.multipleRoots classifications)
        (DegreeSevenStageSevenClassification.criticalSigns classifications)).toFinset := by
  apply Finset.ext
  intro candidate
  induction classifications with
  | nil =>
      simp [degreeSevenStageSevenClassifiedPrefixes,
        DegreeSevenStageSevenClassification.scaledEntries,
        DegreeSevenStageSevenClassification.multipleRoots,
        DegreeSevenStageSevenClassification.criticalSigns]
  | cons classification classifications ih =>
      cases classification <;>
          simp [degreeSevenStageSevenClassifiedPrefixes,
          DegreeSevenStageSevenClassification.toPrefix,
          DegreeSevenStageSevenClassification.scaledEntries,
          DegreeSevenStageSevenClassification.multipleRoots,
          DegreeSevenStageSevenClassification.criticalSigns,
          ih, or_assoc, or_comm]

end TraceEuclidean
