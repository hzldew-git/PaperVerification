import TraceEuclidean.DegreeSevenRolleStageSevenPilot
import TraceEuclidean.DegreeSevenRolleStageSixPiecewisePilot

/-!
# End-to-end closure of the first ten degree-seven Stage Five rows

This module proves inside Lean that the exact Stage Six refinements of the
first ten pilot rows yield precisely four coefficient prefixes.  The final
Stage Seven certificates reject all four prefixes.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

def degreeSevenStageSevenPilotPrefixes :
    List (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) :=
  [((-3 : ℤ), (-9 : ℤ), (-6 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (-5 : ℤ), (1 : ℤ), (1 : ℤ), (0 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (-4 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ)),
    ((-3 : ℤ), (-9 : ℤ), (-4 : ℤ), (1 : ℤ), (1 : ℤ), (0 : ℤ))]

set_option maxHeartbeats 0 in
-- Exact reduction of ten generated rows and their rational interval bounds.
theorem degreeSevenStageSevenPilot_prefix_complete
    (refinement : DegreeSevenStageSixPiecewiseCoverage)
    (hrefinement : refinement ∈
      degreeSevenStageSixPiecewisePilot.take 10)
    (piece : DegreeSevenStageSixScaledFamily)
    (hpiece : piece ∈ refinement.pieces)
    (a2 a1 : ℤ)
    (ha2 : a2 ∈ piece.toFamily.a2Candidates)
    (ha1 : a1 ∈ (piece.toFamily.toEntry a2).a1Candidates) :
    (refinement.coverage.parent.a6, refinement.coverage.parent.a5,
      refinement.coverage.parent.a4, refinement.coverage.parent.a3,
      a2, a1) ∈
      degreeSevenStageSevenPilotPrefixes := by
  simp [degreeSevenStageSixPiecewisePilot] at hrefinement
  rcases hrefinement with rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpiece
  all_goals subst piece
  all_goals
    simp only [DegreeSevenStageSixScaledFamily.toFamily,
      DegreeSevenStageSixFamily.a2Candidates, integerIcc,
      Finset.mem_Icc] at ha2
  all_goals rcases ha2 with ⟨ha2lo, ha2hi⟩
  all_goals interval_cases a2
  all_goals
    norm_num [DegreeSevenStageSixScaledFamily.toFamily,
    DegreeSevenStageSixScaledFamily.interval,
    DegreeSevenStageSixFamily.toEntry,
    DegreeSevenStageSixEntry.a1Candidates,
    DegreeSevenStageSixEntry.baseCoefficients,
    DegreeSevenStageSixEntry.leftEndpoint,
    DegreeSevenStageSixEntry.rightEndpoint,
    sexticTranslationCandidates, integerIcc,
    sexticTranslationLowerBound, sexticTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat] at ha1
  all_goals norm_num [degreeSevenStageSevenPilotPrefixes]
  all_goals omega

def DegreeSevenStageSevenPilotClassified
    (a6 a5 a4 a3 a2 a1 : ℤ) : Prop :=
  (∃ entry ∈ degreeSevenStageSevenScaledPilot,
      entry.a6 = a6 ∧ entry.a5 = a5 ∧ entry.a4 = a4 ∧
        entry.a3 = a3 ∧ entry.a2 = a2 ∧ entry.a1 = a1) ∨
  (∃ witness ∈ degreeSevenStageSevenMultipleRootPilot,
      witness.a6 = a6 ∧ witness.a5 = a5 ∧ witness.a4 = a4 ∧
        witness.a3 = a3 ∧ witness.a2 = a2 ∧ witness.a1 = a1) ∨
  (∃ witness ∈ degreeSevenStageSevenCriticalSignPilot,
      witness.parent.a6 = a6 ∧ witness.parent.a5 = a5 ∧
        witness.parent.a4 = a4 ∧ witness.parent.a3 = a3 ∧
          witness.parent.a2 = a2 ∧ witness.a1 = a1)

theorem degreeSevenStageSevenPilot_prefix_classified
    {a6 a5 a4 a3 a2 a1 : ℤ}
    (hprefix : (a6, a5, a4, a3, a2, a1) ∈
      degreeSevenStageSevenPilotPrefixes) :
    DegreeSevenStageSevenPilotClassified a6 a5 a4 a3 a2 a1 := by
  norm_num [degreeSevenStageSevenPilotPrefixes] at hprefix
  rcases hprefix with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  all_goals
    simp [DegreeSevenStageSevenPilotClassified,
      degreeSevenStageSevenScaledPilot,
      degreeSevenStageSevenMultipleRootPilot,
      degreeSevenStageSevenCriticalSignPilot,
      degreeSevenStageSevenScaledCriticalSignPilot,
      DegreeSevenStageSevenScaledCriticalSignWitness.toWitness,
      DegreeSevenStageSixScaledFamily.toFamily,
      DegreeSevenStageSixFamily.toEntry]

theorem degreeSevenStageSevenPilot_excludes_firstTen
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (refinement : DegreeSevenStageSixPiecewiseCoverage)
    (hrefinement : refinement ∈
      degreeSevenStageSixPiecewisePilot.take 10)
    (ha6 : refinement.coverage.parent.a6 = f.coeff 6)
    (ha5 : refinement.coverage.parent.a5 = f.coeff 5)
    (ha4 : refinement.coverage.parent.a4 = f.coeff 4)
    (ha3 : refinement.coverage.parent.a3 = f.coeff 3) : False := by
  have hrefinementFull :
      refinement ∈ degreeSevenStageSixPiecewisePilot :=
    List.mem_of_mem_take hrefinement
  have hvalid := List.forall_iff_forall_mem.mp
    degreeSevenStageSixPiecewisePilot_valid refinement hrefinementFull
  obtain ⟨piece, hpiece, ha2, ha1⟩ :=
    refinement.hunter_a1_mem h hvalid ha6 ha5 ha4 ha3
  have hprefix := degreeSevenStageSevenPilot_prefix_complete
    refinement hrefinement piece hpiece (f.coeff 2) (f.coeff 1) ha2 ha1
  rw [ha6, ha5, ha4, ha3] at hprefix
  have hclassified := degreeSevenStageSevenPilot_prefix_classified hprefix
  rcases hclassified with
      ⟨entry, hentry, hea6, hea5, hea4, hea3, hea2, hea1⟩ |
      ⟨witness, hwitness, hwa6, hwa5, hwa4, hwa3, hwa2, hwa1⟩ |
      ⟨witness, hwitness, hwa6, hwa5, hwa4, hwa3, hwa2, hwa1⟩
  · have hentryValid := List.forall_iff_forall_mem.mp
      degreeSevenStageSevenScaledPilot_valid entry hentry
    have ha0 := degreeSeven_minimumHunterCandidate_a0_mem_of_stageSeven
      h entry.toEntry hentryValid hea6 hea5 hea4 hea3 hea2 hea1
    have hempty := List.forall_iff_forall_mem.mp
      degreeSevenStageSevenScaledPilot_a0Candidates_empty entry hentry
    rw [hempty] at ha0
    simp at ha0
  · have hwitnessValid := List.forall_iff_forall_mem.mp
      degreeSevenStageSevenMultipleRootPilot_valid witness hwitness
    exact degreeSeven_stageSevenMultipleRootWitness_not_hunter
      h witness hwitnessValid hwa6 hwa5 hwa4 hwa3 hwa2 hwa1
  · have hwitnessValid := List.forall_iff_forall_mem.mp
      degreeSevenStageSevenCriticalSignPilot_valid witness hwitness
    exact degreeSeven_stageSevenCriticalSignWitness_not_hunter
      h witness hwitnessValid hwa6 hwa5 hwa4 hwa3 hwa2 hwa1

end

end TraceEuclidean
