import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Closure
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Reduction.Chunk000
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Reduction.Chunk001
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Reduction.Chunk002
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Reduction.Chunk003
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Reduction.Chunk004
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Reduction.Chunk005
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Reduction.Chunk006
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Reduction.Chunk007
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Reduction.Chunk008
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Reduction.Chunk009

/-!
# Irreducible frontier for degree-seven Stage Five rows 100 through 199

The exact `a0` intervals contain 599 final monic septics.  Checked nontrivial
factorizations remove 590 of them.  This file combines the ten independent
chunks and reduces every irreducible Hunter candidate to nine explicit
coefficient lists.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows100To199 :
    List DegreeSevenFinalEntryCertificate :=
  degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk000 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk001 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk002 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk004 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk005 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk007 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk008 ++
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009))))))))

def degreeSevenStageSevenSurvivorCoefficientsRows100To199 :
    List (List ℤ) :=
  [
    [-1, -4, 0, 12, 5, -9, -3, 1],
    [-1, -5, -1, 14, 5, -9, -3, 1],
    [1, -3, -4, 12, 6, -9, -3, 1],
    [1, -5, -4, 14, 6, -9, -3, 1],
    [1, -4, -3, 14, 6, -9, -3, 1],
    [-1, -5, -2, 14, 6, -9, -3, 1],
    [-1, -6, -2, 15, 6, -9, -3, 1],
    [-1, -5, -1, 15, 6, -9, -3, 1],
    [-1, -5, 0, 16, 6, -9, -3, 1]
  ]

theorem degreeSevenStageSevenScaledRows100To199_chunks :
    degreeSevenStageSevenScaledRows100To199 =
      degreeSevenStageSevenScaledRows100To199Chunk000 ++
    (degreeSevenStageSevenScaledRows100To199Chunk001 ++
    (degreeSevenStageSevenScaledRows100To199Chunk002 ++
    (degreeSevenStageSevenScaledRows100To199Chunk003 ++
    (degreeSevenStageSevenScaledRows100To199Chunk004 ++
    (degreeSevenStageSevenScaledRows100To199Chunk005 ++
    (degreeSevenStageSevenScaledRows100To199Chunk006 ++
    (degreeSevenStageSevenScaledRows100To199Chunk007 ++
    (degreeSevenStageSevenScaledRows100To199Chunk008 ++
      degreeSevenStageSevenScaledRows100To199Chunk009)))))))) := by
  unfold degreeSevenStageSevenScaledRows100To199
    degreeSevenStageSevenClassificationsRows100To199
    degreeSevenStageSevenScaledRows100To199Chunk000
    degreeSevenStageSevenScaledRows100To199Chunk001
    degreeSevenStageSevenScaledRows100To199Chunk002
    degreeSevenStageSevenScaledRows100To199Chunk003
    degreeSevenStageSevenScaledRows100To199Chunk004
    degreeSevenStageSevenScaledRows100To199Chunk005
    degreeSevenStageSevenScaledRows100To199Chunk006
    degreeSevenStageSevenScaledRows100To199Chunk007
    degreeSevenStageSevenScaledRows100To199Chunk008
    degreeSevenStageSevenScaledRows100To199Chunk009
  simp only [DegreeSevenStageSevenClassification.scaledEntries_append,
    List.append_assoc]

theorem degreeSevenStageSevenScaledRows100To199_certificates :
    degreeSevenStageSevenScaledRows100To199 =
      degreeSevenStageSevenFinalEntryCertificatesRows100To199.map
        DegreeSevenFinalEntryCertificate.entry := by
  rw [degreeSevenStageSevenScaledRows100To199_chunks]
  simp only [degreeSevenStageSevenFinalEntryCertificatesRows100To199,
    List.map_append]
  rw [degreeSevenStageSevenScaledRows100To199Chunk000_parts,
    degreeSevenStageSevenScaledRows100To199Chunk001_parts,
    degreeSevenStageSevenScaledRows100To199Chunk002_parts,
    degreeSevenStageSevenScaledRows100To199Chunk003_parts,
    degreeSevenStageSevenScaledRows100To199Chunk004_parts,
    degreeSevenStageSevenScaledRows100To199Chunk005_parts,
    degreeSevenStageSevenScaledRows100To199Chunk006_parts,
    degreeSevenStageSevenScaledRows100To199Chunk007_parts,
    degreeSevenStageSevenScaledRows100To199Chunk008_parts,
    degreeSevenStageSevenScaledRows100To199Chunk009_parts]

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199.Forall
      (fun certificate => certificate.check = true) := by
  exact List.forall_append.mpr ⟨
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk000_valid,
    List.forall_append.mpr ⟨
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk001_valid,
      List.forall_append.mpr ⟨
        degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk002_valid,
        List.forall_append.mpr ⟨
          degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003_valid,
          List.forall_append.mpr ⟨
            degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk004_valid,
            List.forall_append.mpr ⟨
              degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk005_valid,
              List.forall_append.mpr ⟨
                degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006_valid,
                List.forall_append.mpr ⟨
                  degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk007_valid,
                  List.forall_append.mpr ⟨
                    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk008_valid,
                    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009_valid⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem degreeSevenStageSevenScaledRows100To199_arithmeticValid :
    degreeSevenStageSevenScaledRows100To199.Forall
      DegreeSevenStageSevenScaledEntry.ArithmeticValid := by
  rw [degreeSevenStageSevenScaledRows100To199_chunks]
  exact List.forall_append.mpr ⟨
    degreeSevenStageSevenScaledRows100To199Chunk000_arithmeticValid,
    List.forall_append.mpr ⟨
      degreeSevenStageSevenScaledRows100To199Chunk001_arithmeticValid,
      List.forall_append.mpr ⟨
        degreeSevenStageSevenScaledRows100To199Chunk002_arithmeticValid,
        List.forall_append.mpr ⟨
          degreeSevenStageSevenScaledRows100To199Chunk003_arithmeticValid,
          List.forall_append.mpr ⟨
            degreeSevenStageSevenScaledRows100To199Chunk004_arithmeticValid,
            List.forall_append.mpr ⟨
              degreeSevenStageSevenScaledRows100To199Chunk005_arithmeticValid,
              List.forall_append.mpr ⟨
                degreeSevenStageSevenScaledRows100To199Chunk006_arithmeticValid,
                List.forall_append.mpr ⟨
                  degreeSevenStageSevenScaledRows100To199Chunk007_arithmeticValid,
                  List.forall_append.mpr ⟨
                    degreeSevenStageSevenScaledRows100To199Chunk008_arithmeticValid,
                    degreeSevenStageSevenScaledRows100To199Chunk009_arithmeticValid⟩⟩⟩⟩⟩⟩⟩⟩⟩

set_option maxHeartbeats 0 in
theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199.length = 1369 := by
  rfl

set_option maxHeartbeats 0 in
theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows100To199).length = 599 := by
  rfl

set_option maxHeartbeats 0 in
theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199_survivors :
    DegreeSevenFinalEntryCertificate.survivorCoefficients
        degreeSevenStageSevenFinalEntryCertificatesRows100To199 =
      degreeSevenStageSevenSurvivorCoefficientsRows100To199 := by
  rfl

/-- A Hunter septic attached to a six-root entry from rows 100 through 199 is
one of the nine explicitly retained irreducible coefficient lists. -/
theorem degreeSevenStageSevenScaledRows100To199_hunter_survivor
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (entry : DegreeSevenStageSevenScaledEntry)
    (hentry : entry ∈ degreeSevenStageSevenScaledRows100To199)
    (ha6 : entry.a6 = f.coeff 6)
    (ha5 : entry.a5 = f.coeff 5)
    (ha4 : entry.a4 = f.coeff 4)
    (ha3 : entry.a3 = f.coeff 3)
    (ha2 : entry.a2 = f.coeff 2)
    (ha1 : entry.a1 = f.coeff 1) :
    [f.coeff 0, f.coeff 1, f.coeff 2, f.coeff 3,
      f.coeff 4, f.coeff 5, f.coeff 6, 1] ∈
        degreeSevenStageSevenSurvivorCoefficientsRows100To199 := by
  have hentryArithmetic := List.forall_iff_forall_mem.mp
    degreeSevenStageSevenScaledRows100To199_arithmeticValid entry hentry
  have ha0 := degreeSevenStageSevenRows100To199_a0_mem
    h entry hentry ha6 ha5 ha4 ha3 ha2 ha1
  have hcoefficients := entry.coefficients_mem_final hentry
    hentryArithmetic ha0
  rw [degreeSevenStageSevenScaledRows100To199_certificates] at hcoefficients
  have hirreducible :
      Irreducible (polynomialOfCoefficients
        [f.coeff 0, entry.a1, entry.a2, entry.a3,
          entry.a4, entry.a5, entry.a6, 1]) := by
    rw [ha1, ha2, ha3, ha4, ha5, ha6,
      ← degreeSeven_eq_polynomialOfCoefficients h.1 h.2.2.1]
    exact h.2.1
  have hsurvivor :=
    DegreeSevenFinalEntryCertificate.mem_survivorCoefficients_of_irreducible
      degreeSevenStageSevenFinalEntryCertificatesRows100To199_valid
      hcoefficients hirreducible
  rw [degreeSevenStageSevenFinalEntryCertificatesRows100To199_survivors]
    at hsurvivor
  simpa [ha1, ha2, ha3, ha4, ha5, ha6] using hsurvivor

/-- Every Hunter septic whose nonconstant coefficient prefix occurs in the
rows 100 through 199 classification has one of the nine retained coefficient
lists.  The multiple-root and forbidden critical-sign branches are impossible. -/
theorem degreeSevenStageSevenRows100To199_survivor_of_prefix_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (hprefix :
      { a6 := f.coeff 6
        a5 := f.coeff 5
        a4 := f.coeff 4
        a3 := f.coeff 3
        a2 := f.coeff 2
        a1 := f.coeff 1 : DegreeSevenStageSevenPrefix } ∈
        degreeSevenStageSixPrefixesRows100To199) :
    [f.coeff 0, f.coeff 1, f.coeff 2, f.coeff 3,
      f.coeff 4, f.coeff 5, f.coeff 6, 1] ∈
        degreeSevenStageSevenSurvivorCoefficientsRows100To199 := by
  let targetPrefix : DegreeSevenStageSevenPrefix :=
    { a6 := f.coeff 6
      a5 := f.coeff 5
      a4 := f.coeff 4
      a3 := f.coeff 3
      a2 := f.coeff 2
      a1 := f.coeff 1 }
  have hprefixFinset :
      targetPrefix ∈ degreeSevenStageSixPrefixesRows100To199.toFinset := by
    exact List.mem_toFinset.mpr hprefix
  rw [degreeSevenStageSevenRows100To199_keyFinsets_eq] at hprefixFinset
  have hclassified :
      targetPrefix ∈ degreeSevenStageSevenClassifiedPrefixesRows100To199 :=
    List.mem_toFinset.mp hprefixFinset
  simp only [degreeSevenStageSevenClassifiedPrefixesRows100To199,
    degreeSevenStageSevenClassifiedPrefixes,
    List.mem_append, List.mem_map] at hclassified
  rcases hclassified with (hscaled | hmultiple) | hcritical
  · obtain ⟨entry, hentry, hentryPrefix⟩ := hscaled
    have ha6 : entry.a6 = f.coeff 6 := by
      simpa [targetPrefix, DegreeSevenStageSevenPrefix.ofScaledEntry] using
        congrArg DegreeSevenStageSevenPrefix.a6 hentryPrefix
    have ha5 : entry.a5 = f.coeff 5 := by
      simpa [targetPrefix, DegreeSevenStageSevenPrefix.ofScaledEntry] using
        congrArg DegreeSevenStageSevenPrefix.a5 hentryPrefix
    have ha4 : entry.a4 = f.coeff 4 := by
      simpa [targetPrefix, DegreeSevenStageSevenPrefix.ofScaledEntry] using
        congrArg DegreeSevenStageSevenPrefix.a4 hentryPrefix
    have ha3 : entry.a3 = f.coeff 3 := by
      simpa [targetPrefix, DegreeSevenStageSevenPrefix.ofScaledEntry] using
        congrArg DegreeSevenStageSevenPrefix.a3 hentryPrefix
    have ha2 : entry.a2 = f.coeff 2 := by
      simpa [targetPrefix, DegreeSevenStageSevenPrefix.ofScaledEntry] using
        congrArg DegreeSevenStageSevenPrefix.a2 hentryPrefix
    have ha1 : entry.a1 = f.coeff 1 := by
      simpa [targetPrefix, DegreeSevenStageSevenPrefix.ofScaledEntry] using
        congrArg DegreeSevenStageSevenPrefix.a1 hentryPrefix
    exact degreeSevenStageSevenScaledRows100To199_hunter_survivor
      h entry hentry ha6 ha5 ha4 ha3 ha2 ha1
  · obtain ⟨witness, hwitness, hwitnessPrefix⟩ := hmultiple
    have hvalid := List.forall_iff_forall_mem.mp
      degreeSevenStageSevenMultipleRootRows100To199_valid witness hwitness
    exact (degreeSeven_stageSevenMultipleRootWitness_not_hunter
      h witness hvalid
      (by simpa [targetPrefix,
        DegreeSevenStageSevenPrefix.ofMultipleRootWitness] using
          congrArg DegreeSevenStageSevenPrefix.a6 hwitnessPrefix)
      (by simpa [targetPrefix,
        DegreeSevenStageSevenPrefix.ofMultipleRootWitness] using
          congrArg DegreeSevenStageSevenPrefix.a5 hwitnessPrefix)
      (by simpa [targetPrefix,
        DegreeSevenStageSevenPrefix.ofMultipleRootWitness] using
          congrArg DegreeSevenStageSevenPrefix.a4 hwitnessPrefix)
      (by simpa [targetPrefix,
        DegreeSevenStageSevenPrefix.ofMultipleRootWitness] using
          congrArg DegreeSevenStageSevenPrefix.a3 hwitnessPrefix)
      (by simpa [targetPrefix,
        DegreeSevenStageSevenPrefix.ofMultipleRootWitness] using
          congrArg DegreeSevenStageSevenPrefix.a2 hwitnessPrefix)
      (by simpa [targetPrefix,
        DegreeSevenStageSevenPrefix.ofMultipleRootWitness] using
          congrArg DegreeSevenStageSevenPrefix.a1 hwitnessPrefix)).elim
  · obtain ⟨witness, hwitness, hwitnessPrefix⟩ := hcritical
    have hvalid := List.forall_iff_forall_mem.mp
      degreeSevenStageSevenScaledCriticalSignRows100To199_valid
        witness hwitness
    exact (degreeSeven_stageSevenCriticalSignWitness_not_hunter
      h witness.toWitness hvalid
      (by simpa [targetPrefix,
        DegreeSevenStageSevenPrefix.ofScaledCriticalSignWitness,
        DegreeSevenStageSevenScaledCriticalSignWitness.toWitness,
        DegreeSevenStageSixScaledFamily.toFamily,
        DegreeSevenStageSixFamily.toEntry] using
          congrArg DegreeSevenStageSevenPrefix.a6 hwitnessPrefix)
      (by simpa [targetPrefix,
        DegreeSevenStageSevenPrefix.ofScaledCriticalSignWitness,
        DegreeSevenStageSevenScaledCriticalSignWitness.toWitness,
        DegreeSevenStageSixScaledFamily.toFamily,
        DegreeSevenStageSixFamily.toEntry] using
          congrArg DegreeSevenStageSevenPrefix.a5 hwitnessPrefix)
      (by simpa [targetPrefix,
        DegreeSevenStageSevenPrefix.ofScaledCriticalSignWitness,
        DegreeSevenStageSevenScaledCriticalSignWitness.toWitness,
        DegreeSevenStageSixScaledFamily.toFamily,
        DegreeSevenStageSixFamily.toEntry] using
          congrArg DegreeSevenStageSevenPrefix.a4 hwitnessPrefix)
      (by simpa [targetPrefix,
        DegreeSevenStageSevenPrefix.ofScaledCriticalSignWitness,
        DegreeSevenStageSevenScaledCriticalSignWitness.toWitness,
        DegreeSevenStageSixScaledFamily.toFamily,
        DegreeSevenStageSixFamily.toEntry] using
          congrArg DegreeSevenStageSevenPrefix.a3 hwitnessPrefix)
      (by simpa [targetPrefix,
        DegreeSevenStageSevenPrefix.ofScaledCriticalSignWitness,
        DegreeSevenStageSevenScaledCriticalSignWitness.toWitness,
        DegreeSevenStageSixScaledFamily.toFamily,
        DegreeSevenStageSixFamily.toEntry] using
          congrArg DegreeSevenStageSevenPrefix.a2 hwitnessPrefix)
      (by simpa [targetPrefix,
        DegreeSevenStageSevenPrefix.ofScaledCriticalSignWitness,
        DegreeSevenStageSevenScaledCriticalSignWitness.toWitness,
        DegreeSevenStageSixScaledFamily.toFamily,
        DegreeSevenStageSixFamily.toEntry] using
          congrArg DegreeSevenStageSevenPrefix.a1 hwitnessPrefix)).elim

def degreeSevenStageSixPiecewiseRows100To199 :
    List DegreeSevenStageSixPiecewiseCoverage :=
  degreeSevenStageSixPiecewiseRows100To199Chunk000 ++
    (degreeSevenStageSixPiecewiseRows100To199Chunk001 ++
    (degreeSevenStageSixPiecewiseRows100To199Chunk002 ++
    (degreeSevenStageSixPiecewiseRows100To199Chunk003 ++
    (degreeSevenStageSixPiecewiseRows100To199Chunk004 ++
    (degreeSevenStageSixPiecewiseRows100To199Chunk005 ++
    (degreeSevenStageSixPiecewiseRows100To199Chunk006 ++
    (degreeSevenStageSixPiecewiseRows100To199Chunk007 ++
    (degreeSevenStageSixPiecewiseRows100To199Chunk008 ++
      degreeSevenStageSixPiecewiseRows100To199Chunk009))))))))

theorem degreeSevenStageSixPiecewiseRows100To199_valid :
    degreeSevenStageSixPiecewiseRows100To199.Forall
      DegreeSevenStageSixPiecewiseCoverage.Valid := by
  exact List.forall_append.mpr ⟨
    degreeSevenStageSixPiecewiseRows100To199Chunk000_valid,
    List.forall_append.mpr ⟨
      degreeSevenStageSixPiecewiseRows100To199Chunk001_valid,
      List.forall_append.mpr ⟨
        degreeSevenStageSixPiecewiseRows100To199Chunk002_valid,
        List.forall_append.mpr ⟨
          degreeSevenStageSixPiecewiseRows100To199Chunk003_valid,
          List.forall_append.mpr ⟨
            degreeSevenStageSixPiecewiseRows100To199Chunk004_valid,
            List.forall_append.mpr ⟨
              degreeSevenStageSixPiecewiseRows100To199Chunk005_valid,
              List.forall_append.mpr ⟨
                degreeSevenStageSixPiecewiseRows100To199Chunk006_valid,
                List.forall_append.mpr ⟨
                  degreeSevenStageSixPiecewiseRows100To199Chunk007_valid,
                  List.forall_append.mpr ⟨
                    degreeSevenStageSixPiecewiseRows100To199Chunk008_valid,
                    degreeSevenStageSixPiecewiseRows100To199Chunk009_valid⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem degreeSevenStageSixPiecewiseRows100To199_prefixes :
    degreeSevenStageSixPrefixes
        degreeSevenStageSixPiecewiseRows100To199 =
      degreeSevenStageSixPrefixesRows100To199 := by
  simp [degreeSevenStageSixPiecewiseRows100To199,
    degreeSevenStageSixPrefixesRows100To199,
    degreeSevenStageSixPrefixesRows100To199Chunk000,
    degreeSevenStageSixPrefixesRows100To199Chunk001,
    degreeSevenStageSixPrefixesRows100To199Chunk002,
    degreeSevenStageSixPrefixesRows100To199Chunk003,
    degreeSevenStageSixPrefixesRows100To199Chunk004,
    degreeSevenStageSixPrefixesRows100To199Chunk005,
    degreeSevenStageSixPrefixesRows100To199Chunk006,
    degreeSevenStageSixPrefixesRows100To199Chunk007,
    degreeSevenStageSixPrefixesRows100To199Chunk008,
    degreeSevenStageSixPrefixesRows100To199Chunk009,
    degreeSevenStageSixPrefixes, List.append_assoc]

/-- End-to-end reduction for a Hunter septic whose first four nonconstant
coefficients match one of the certified Stage Five rows 100 through 199. -/
theorem degreeSevenStageSevenRows100To199_reduces_to_nine
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (refinement : DegreeSevenStageSixPiecewiseCoverage)
    (hrefinement : refinement ∈ degreeSevenStageSixPiecewiseRows100To199)
    (ha6 : refinement.coverage.parent.a6 = f.coeff 6)
    (ha5 : refinement.coverage.parent.a5 = f.coeff 5)
    (ha4 : refinement.coverage.parent.a4 = f.coeff 4)
    (ha3 : refinement.coverage.parent.a3 = f.coeff 3) :
    [f.coeff 0, f.coeff 1, f.coeff 2, f.coeff 3,
      f.coeff 4, f.coeff 5, f.coeff 6, 1] ∈
        degreeSevenStageSevenSurvivorCoefficientsRows100To199 := by
  have hvalid := List.forall_iff_forall_mem.mp
    degreeSevenStageSixPiecewiseRows100To199_valid refinement hrefinement
  obtain ⟨piece, hpiece, ha2, ha1⟩ :=
    refinement.hunter_a1_mem h hvalid ha6 ha5 ha4 ha3
  have hpieceValid := List.forall_iff_forall_mem.mp
    (refinement.pieces_forall_arithmeticValid hvalid.2) piece hpiece
  have hprefix := refinement.prefix_mem hrefinement piece hpiece
    hpieceValid (f.coeff 2) (f.coeff 1) ha2 ha1
  rw [degreeSevenStageSixPiecewiseRows100To199_prefixes,
    ha6, ha5, ha4, ha3] at hprefix
  exact degreeSevenStageSevenRows100To199_survivor_of_prefix_mem h hprefix

end

end TraceEuclidean
