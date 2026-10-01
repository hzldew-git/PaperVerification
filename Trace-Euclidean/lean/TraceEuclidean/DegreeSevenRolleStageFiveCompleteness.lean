import TraceEuclidean.DegreeSevenRolleStageFive
import TraceEuclidean.DegreeSevenRolleStageFiveCompletenessCore

/-!
# Completeness of the fifth septic Rolle stage

This module instantiates the data-independent fifth-stage argument with the
generated compact root certificates and the two kernel-checked exceptional
lists.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

/-- The generated fifth-stage frontier satisfies every hypothesis of the
data-independent completeness bridge. -/
def degreeSevenStageFiveCertifiedData :
    DegreeSevenStageFiveCertifiedData where
  entries := degreeSevenStageFiveEntries
  coverages := degreeSevenStageFiveCoverages
  multipleRootWitnesses :=
    degreeSevenStageFiveMultipleRootWitnesses
  criticalSignWitnesses :=
    degreeSevenStageFiveCriticalSignWitnesses
  coverageRangesChecked :=
    degreeSevenStageFiveCoverageRanges_checked
  coveragesValid := degreeSevenStageFiveCoverages_valid
  entriesValid := degreeSevenStageFiveEntries_valid
  topQuadruplesChecked := by
    simpa [degreeSevenStageFiveTopQuadruples] using
      degreeSevenStageFiveTopQuadruples_checked
  multipleRootWitnessesChecked :=
    degreeSevenStageFiveMultipleRootWitnesses_checked
  criticalSignWitnessesChecked :=
    degreeSevenStageFiveCriticalSignWitnesses_checked
  multipleRootWitnessesValid :=
    degreeSevenStageFiveMultipleRootWitnesses_valid
  criticalSignWitnessesValid :=
    degreeSevenStageFiveCriticalSignWitnesses_valid

/-- Every sharpened septic Hunter candidate reaches one certified fifth-stage
row with the same four leading nonmonic coefficients. -/
theorem degreeSeven_minimumHunterCandidate_stageFive_complete
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f) :
    ∃ entry ∈ degreeSevenStageFiveEntries,
      entry.a6 = f.coeff 6 ∧
      entry.a5 = f.coeff 5 ∧
      entry.a4 = f.coeff 4 ∧
      entry.a3 = f.coeff 3 :=
  degreeSeven_minimumHunterCandidate_stageFive_complete_of_data
    degreeSevenStageFiveCertifiedData h

/-- The actual `a2` coefficient of every sharpened septic Hunter candidate
belongs to the interval stored in a certified fifth-stage row. -/
theorem degreeSeven_minimumHunterCandidate_a2_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f) :
    ∃ entry ∈ degreeSevenStageFiveEntries,
      entry.a6 = f.coeff 6 ∧
      entry.a5 = f.coeff 5 ∧
      entry.a4 = f.coeff 4 ∧
      entry.a3 = f.coeff 3 ∧
      f.coeff 2 ∈ entry.a2Candidates :=
  degreeSeven_minimumHunterCandidate_a2_mem_of_data
    degreeSevenStageFiveCertifiedData h

end

end TraceEuclidean
