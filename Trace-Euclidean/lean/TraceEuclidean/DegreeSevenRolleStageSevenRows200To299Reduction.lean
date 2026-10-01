import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Closure
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Reduction.Chunk000
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Reduction.Chunk001
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Reduction.Chunk002
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Reduction.Chunk003
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Reduction.Chunk004
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Reduction.Chunk005
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Reduction.Chunk006
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Reduction.Chunk007
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Reduction.Chunk008
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Reduction.Chunk009

/-!
# Irreducible frontier for degree-seven Stage Five rows 200 through 299

The exact `a0` intervals contain 1,381 final monic septics.  Checked
nontrivial factorizations remove 1,287 of them.  This file combines the ten
independent chunks and reduces every irreducible Hunter candidate to 94
explicit coefficient lists.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows200To299 :
    List DegreeSevenFinalEntryCertificate :=
  degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk001 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk003 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk004 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk005 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk007 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk008 ++
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk009))))))))

set_option maxHeartbeats 0 in
-- The exact 94-row list exceeds the default elaboration heartbeat budget.
def degreeSevenStageSevenSurvivorCoefficientsRows200To299 :
    List (List ℤ) :=
  [
    [-1, -4, 2, 17, 6, -9, -3, 1],
    [1, -2, -5, 9, 7, -9, -3, 1],
    [1, -2, -6, 10, 7, -9, -3, 1],
    [1, -3, -5, 12, 7, -9, -3, 1],
    [1, -4, -5, 13, 7, -9, -3, 1],
    [1, -3, -5, 13, 7, -9, -3, 1],
    [-1, -5, -2, 13, 7, -9, -3, 1],
    [1, -5, -5, 14, 7, -9, -3, 1],
    [1, -4, -4, 14, 7, -9, -3, 1],
    [-1, -5, -1, 14, 7, -9, -3, 1],
    [1, -6, -5, 15, 7, -9, -3, 1],
    [-1, -6, -3, 15, 7, -9, -3, 1],
    [1, -4, -3, 15, 7, -9, -3, 1],
    [-1, -5, -2, 15, 7, -9, -3, 1],
    [-1, -4, 1, 15, 7, -9, -3, 1],
    [-1, -7, -3, 16, 7, -9, -3, 1],
    [1, -5, -3, 16, 7, -9, -3, 1],
    [-1, -6, -2, 16, 7, -9, -3, 1],
    [-1, -5, -1, 16, 7, -9, -3, 1],
    [-2, -8, -2, 17, 7, -9, -3, 1],
    [-1, -7, -2, 17, 7, -9, -3, 1],
    [-1, -6, -1, 17, 7, -9, -3, 1],
    [-1, -6, 0, 18, 7, -9, -3, 1],
    [-1, -5, 1, 18, 7, -9, -3, 1],
    [-1, -4, 2, 18, 7, -9, -3, 1],
    [-1, -4, 3, 19, 7, -9, -3, 1],
    [1, -3, -5, 11, 8, -9, -3, 1],
    [1, -2, -7, 12, 8, -9, -3, 1],
    [1, -3, -6, 12, 8, -9, -3, 1],
    [1, -3, -7, 13, 8, -9, -3, 1],
    [1, -4, -6, 13, 8, -9, -3, 1],
    [1, -3, -6, 13, 8, -9, -3, 1],
    [1, -3, -5, 13, 8, -9, -3, 1],
    [2, -5, -7, 14, 8, -9, -3, 1],
    [1, -4, -7, 14, 8, -9, -3, 1],
    [1, -5, -6, 14, 8, -9, -3, 1],
    [1, -4, -6, 14, 8, -9, -3, 1],
    [1, -3, -6, 14, 8, -9, -3, 1],
    [1, -4, -5, 14, 8, -9, -3, 1],
    [1, -3, -5, 14, 8, -9, -3, 1],
    [-1, -6, -3, 14, 8, -9, -3, 1],
    [-1, -5, -2, 14, 8, -9, -3, 1],
    [2, -6, -7, 15, 8, -9, -3, 1],
    [1, -6, -6, 15, 8, -9, -3, 1],
    [1, -5, -6, 15, 8, -9, -3, 1],
    [1, -5, -5, 15, 8, -9, -3, 1],
    [1, -4, -5, 15, 8, -9, -3, 1],
    [1, -4, -4, 15, 8, -9, -3, 1],
    [-1, -5, -1, 15, 8, -9, -3, 1],
    [2, -7, -7, 16, 8, -9, -3, 1],
    [1, -7, -6, 16, 8, -9, -3, 1],
    [1, -6, -6, 16, 8, -9, -3, 1],
    [-1, -6, -5, 16, 8, -9, -3, 1],
    [1, -6, -5, 16, 8, -9, -3, 1],
    [-1, -7, -4, 16, 8, -9, -3, 1],
    [-1, -6, -4, 16, 8, -9, -3, 1],
    [1, -5, -4, 16, 8, -9, -3, 1],
    [1, -4, -4, 16, 8, -9, -3, 1],
    [-1, -6, -3, 16, 8, -9, -3, 1],
    [1, -4, -3, 16, 8, -9, -3, 1],
    [-1, -5, 0, 16, 8, -9, -3, 1],
    [-1, -4, 1, 16, 8, -9, -3, 1],
    [1, -7, -5, 17, 8, -9, -3, 1],
    [-1, -8, -4, 17, 8, -9, -3, 1],
    [-1, -7, -4, 17, 8, -9, -3, 1],
    [-1, -7, -3, 17, 8, -9, -3, 1],
    [-1, -6, -3, 17, 8, -9, -3, 1],
    [1, -5, -3, 17, 8, -9, -3, 1],
    [-1, -6, -2, 17, 8, -9, -3, 1],
    [-1, -5, -1, 17, 8, -9, -3, 1],
    [-2, -10, -4, 18, 8, -9, -3, 1],
    [-1, -9, -4, 18, 8, -9, -3, 1],
    [-2, -9, -3, 18, 8, -9, -3, 1],
    [-1, -8, -3, 18, 8, -9, -3, 1],
    [1, -6, -3, 18, 8, -9, -3, 1],
    [-2, -8, -2, 18, 8, -9, -3, 1],
    [-1, -7, -2, 18, 8, -9, -3, 1],
    [-1, -6, -2, 18, 8, -9, -3, 1],
    [1, -5, -2, 18, 8, -9, -3, 1],
    [-1, -6, -1, 18, 8, -9, -3, 1],
    [-1, -5, 0, 18, 8, -9, -3, 1],
    [-3, -11, -3, 19, 8, -9, -3, 1],
    [-2, -9, -2, 19, 8, -9, -3, 1],
    [-1, -8, -2, 19, 8, -9, -3, 1],
    [-2, -8, -1, 19, 8, -9, -3, 1],
    [-1, -7, -1, 19, 8, -9, -3, 1],
    [-1, -5, 0, 19, 8, -9, -3, 1],
    [-1, -5, 1, 19, 8, -9, -3, 1],
    [-1, -6, 1, 20, 8, -9, -3, 1],
    [-1, -5, 2, 20, 8, -9, -3, 1],
    [-1, -4, 3, 20, 8, -9, -3, 1],
    [-2, -7, 2, 21, 8, -9, -3, 1],
    [-1, -5, 3, 21, 8, -9, -3, 1],
    [-1, -4, 5, 22, 8, -9, -3, 1]
  ]

theorem degreeSevenStageSevenScaledRows200To299_chunks :
    degreeSevenStageSevenScaledRows200To299 =
      degreeSevenStageSevenScaledRows200To299Chunk000 ++
    (degreeSevenStageSevenScaledRows200To299Chunk001 ++
    (degreeSevenStageSevenScaledRows200To299Chunk002 ++
    (degreeSevenStageSevenScaledRows200To299Chunk003 ++
    (degreeSevenStageSevenScaledRows200To299Chunk004 ++
    (degreeSevenStageSevenScaledRows200To299Chunk005 ++
    (degreeSevenStageSevenScaledRows200To299Chunk006 ++
    (degreeSevenStageSevenScaledRows200To299Chunk007 ++
    (degreeSevenStageSevenScaledRows200To299Chunk008 ++
      degreeSevenStageSevenScaledRows200To299Chunk009)))))))) := by
  unfold degreeSevenStageSevenScaledRows200To299
    degreeSevenStageSevenClassificationsRows200To299
    degreeSevenStageSevenScaledRows200To299Chunk000
    degreeSevenStageSevenScaledRows200To299Chunk001
    degreeSevenStageSevenScaledRows200To299Chunk002
    degreeSevenStageSevenScaledRows200To299Chunk003
    degreeSevenStageSevenScaledRows200To299Chunk004
    degreeSevenStageSevenScaledRows200To299Chunk005
    degreeSevenStageSevenScaledRows200To299Chunk006
    degreeSevenStageSevenScaledRows200To299Chunk007
    degreeSevenStageSevenScaledRows200To299Chunk008
    degreeSevenStageSevenScaledRows200To299Chunk009
  simp only [DegreeSevenStageSevenClassification.scaledEntries_append,
    List.append_assoc]

theorem degreeSevenStageSevenScaledRows200To299_certificates :
    degreeSevenStageSevenScaledRows200To299 =
      degreeSevenStageSevenFinalEntryCertificatesRows200To299.map
        DegreeSevenFinalEntryCertificate.entry := by
  rw [degreeSevenStageSevenScaledRows200To299_chunks]
  simp only [degreeSevenStageSevenFinalEntryCertificatesRows200To299,
    List.map_append]
  rw [degreeSevenStageSevenScaledRows200To299Chunk000_parts,
    degreeSevenStageSevenScaledRows200To299Chunk001_parts,
    degreeSevenStageSevenScaledRows200To299Chunk002_parts,
    degreeSevenStageSevenScaledRows200To299Chunk003_parts,
    degreeSevenStageSevenScaledRows200To299Chunk004_parts,
    degreeSevenStageSevenScaledRows200To299Chunk005_parts,
    degreeSevenStageSevenScaledRows200To299Chunk006_parts,
    degreeSevenStageSevenScaledRows200To299Chunk007_parts,
    degreeSevenStageSevenScaledRows200To299Chunk008_parts,
    degreeSevenStageSevenScaledRows200To299Chunk009_parts]

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows200To299.Forall
      (fun certificate => certificate.check = true) := by
  exact List.forall_append.mpr ⟨
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000_valid,
    List.forall_append.mpr ⟨
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk001_valid,
      List.forall_append.mpr ⟨
        degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002_valid,
        List.forall_append.mpr ⟨
          degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk003_valid,
          List.forall_append.mpr ⟨
            degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk004_valid,
            List.forall_append.mpr ⟨
              degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk005_valid,
              List.forall_append.mpr ⟨
                degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006_valid,
                List.forall_append.mpr ⟨
                  degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk007_valid,
                  List.forall_append.mpr ⟨
                    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk008_valid,
                    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk009_valid⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem degreeSevenStageSevenScaledRows200To299_arithmeticValid :
    degreeSevenStageSevenScaledRows200To299.Forall
      DegreeSevenStageSevenScaledEntry.ArithmeticValid := by
  rw [degreeSevenStageSevenScaledRows200To299_chunks]
  exact List.forall_append.mpr ⟨
    degreeSevenStageSevenScaledRows200To299Chunk000_arithmeticValid,
    List.forall_append.mpr ⟨
      degreeSevenStageSevenScaledRows200To299Chunk001_arithmeticValid,
      List.forall_append.mpr ⟨
        degreeSevenStageSevenScaledRows200To299Chunk002_arithmeticValid,
        List.forall_append.mpr ⟨
          degreeSevenStageSevenScaledRows200To299Chunk003_arithmeticValid,
          List.forall_append.mpr ⟨
            degreeSevenStageSevenScaledRows200To299Chunk004_arithmeticValid,
            List.forall_append.mpr ⟨
              degreeSevenStageSevenScaledRows200To299Chunk005_arithmeticValid,
              List.forall_append.mpr ⟨
                degreeSevenStageSevenScaledRows200To299Chunk006_arithmeticValid,
                List.forall_append.mpr ⟨
                  degreeSevenStageSevenScaledRows200To299Chunk007_arithmeticValid,
                  List.forall_append.mpr ⟨
                    degreeSevenStageSevenScaledRows200To299Chunk008_arithmeticValid,
                    degreeSevenStageSevenScaledRows200To299Chunk009_arithmeticValid⟩⟩⟩⟩⟩⟩⟩⟩⟩

set_option maxHeartbeats 0 in
theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows200To299.length = 2725 := by
  rfl

set_option maxHeartbeats 0 in
theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows200To299).length = 1381 := by
  rfl

set_option maxHeartbeats 0 in
theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299_survivors :
    DegreeSevenFinalEntryCertificate.survivorCoefficients
        degreeSevenStageSevenFinalEntryCertificatesRows200To299 =
      degreeSevenStageSevenSurvivorCoefficientsRows200To299 := by
  rfl

/-- A Hunter septic attached to a six-root entry from rows 200 through 299 is
one of the 94 explicitly retained irreducible coefficient lists. -/
theorem degreeSevenStageSevenScaledRows200To299_hunter_survivor
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (entry : DegreeSevenStageSevenScaledEntry)
    (hentry : entry ∈ degreeSevenStageSevenScaledRows200To299)
    (ha6 : entry.a6 = f.coeff 6)
    (ha5 : entry.a5 = f.coeff 5)
    (ha4 : entry.a4 = f.coeff 4)
    (ha3 : entry.a3 = f.coeff 3)
    (ha2 : entry.a2 = f.coeff 2)
    (ha1 : entry.a1 = f.coeff 1) :
    [f.coeff 0, f.coeff 1, f.coeff 2, f.coeff 3,
      f.coeff 4, f.coeff 5, f.coeff 6, 1] ∈
        degreeSevenStageSevenSurvivorCoefficientsRows200To299 := by
  have hentryArithmetic := List.forall_iff_forall_mem.mp
    degreeSevenStageSevenScaledRows200To299_arithmeticValid entry hentry
  have ha0 := degreeSevenStageSevenRows200To299_a0_mem
    h entry hentry ha6 ha5 ha4 ha3 ha2 ha1
  have hcoefficients := entry.coefficients_mem_final hentry
    hentryArithmetic ha0
  rw [degreeSevenStageSevenScaledRows200To299_certificates] at hcoefficients
  have hirreducible :
      Irreducible (polynomialOfCoefficients
        [f.coeff 0, entry.a1, entry.a2, entry.a3,
          entry.a4, entry.a5, entry.a6, 1]) := by
    rw [ha1, ha2, ha3, ha4, ha5, ha6,
      ← degreeSeven_eq_polynomialOfCoefficients h.1 h.2.2.1]
    exact h.2.1
  have hsurvivor :=
    DegreeSevenFinalEntryCertificate.mem_survivorCoefficients_of_irreducible
      degreeSevenStageSevenFinalEntryCertificatesRows200To299_valid
      hcoefficients hirreducible
  rw [degreeSevenStageSevenFinalEntryCertificatesRows200To299_survivors]
    at hsurvivor
  simpa [ha1, ha2, ha3, ha4, ha5, ha6] using hsurvivor

/-- Every Hunter septic whose nonconstant coefficient prefix occurs in the
rows 200 through 299 classification has one of the 94 retained coefficient
lists.  The multiple-root and forbidden critical-sign branches are impossible. -/
theorem degreeSevenStageSevenRows200To299_survivor_of_prefix_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (hprefix :
      { a6 := f.coeff 6
        a5 := f.coeff 5
        a4 := f.coeff 4
        a3 := f.coeff 3
        a2 := f.coeff 2
        a1 := f.coeff 1 : DegreeSevenStageSevenPrefix } ∈
        degreeSevenStageSixPrefixesRows200To299) :
    [f.coeff 0, f.coeff 1, f.coeff 2, f.coeff 3,
      f.coeff 4, f.coeff 5, f.coeff 6, 1] ∈
        degreeSevenStageSevenSurvivorCoefficientsRows200To299 := by
  let targetPrefix : DegreeSevenStageSevenPrefix :=
    { a6 := f.coeff 6
      a5 := f.coeff 5
      a4 := f.coeff 4
      a3 := f.coeff 3
      a2 := f.coeff 2
      a1 := f.coeff 1 }
  have hprefixFinset :
      targetPrefix ∈ degreeSevenStageSixPrefixesRows200To299.toFinset := by
    exact List.mem_toFinset.mpr hprefix
  rw [degreeSevenStageSevenRows200To299_keyFinsets_eq] at hprefixFinset
  have hclassified :
      targetPrefix ∈ degreeSevenStageSevenClassifiedPrefixesRows200To299 :=
    List.mem_toFinset.mp hprefixFinset
  simp only [degreeSevenStageSevenClassifiedPrefixesRows200To299,
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
    exact degreeSevenStageSevenScaledRows200To299_hunter_survivor
      h entry hentry ha6 ha5 ha4 ha3 ha2 ha1
  · obtain ⟨witness, hwitness, hwitnessPrefix⟩ := hmultiple
    have hvalid := List.forall_iff_forall_mem.mp
      degreeSevenStageSevenMultipleRootRows200To299_valid witness hwitness
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
      degreeSevenStageSevenScaledCriticalSignRows200To299_valid
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

def degreeSevenStageSixPiecewiseRows200To299 :
    List DegreeSevenStageSixPiecewiseCoverage :=
  degreeSevenStageSixPiecewiseRows200To299Chunk000 ++
    (degreeSevenStageSixPiecewiseRows200To299Chunk001 ++
    (degreeSevenStageSixPiecewiseRows200To299Chunk002 ++
    (degreeSevenStageSixPiecewiseRows200To299Chunk003 ++
    (degreeSevenStageSixPiecewiseRows200To299Chunk004 ++
    (degreeSevenStageSixPiecewiseRows200To299Chunk005 ++
    (degreeSevenStageSixPiecewiseRows200To299Chunk006 ++
    (degreeSevenStageSixPiecewiseRows200To299Chunk007 ++
    (degreeSevenStageSixPiecewiseRows200To299Chunk008 ++
      degreeSevenStageSixPiecewiseRows200To299Chunk009))))))))

theorem degreeSevenStageSixPiecewiseRows200To299_valid :
    degreeSevenStageSixPiecewiseRows200To299.Forall
      DegreeSevenStageSixPiecewiseCoverage.Valid := by
  exact List.forall_append.mpr ⟨
    degreeSevenStageSixPiecewiseRows200To299Chunk000_valid,
    List.forall_append.mpr ⟨
      degreeSevenStageSixPiecewiseRows200To299Chunk001_valid,
      List.forall_append.mpr ⟨
        degreeSevenStageSixPiecewiseRows200To299Chunk002_valid,
        List.forall_append.mpr ⟨
          degreeSevenStageSixPiecewiseRows200To299Chunk003_valid,
          List.forall_append.mpr ⟨
            degreeSevenStageSixPiecewiseRows200To299Chunk004_valid,
            List.forall_append.mpr ⟨
              degreeSevenStageSixPiecewiseRows200To299Chunk005_valid,
              List.forall_append.mpr ⟨
                degreeSevenStageSixPiecewiseRows200To299Chunk006_valid,
                List.forall_append.mpr ⟨
                  degreeSevenStageSixPiecewiseRows200To299Chunk007_valid,
                  List.forall_append.mpr ⟨
                    degreeSevenStageSixPiecewiseRows200To299Chunk008_valid,
                    degreeSevenStageSixPiecewiseRows200To299Chunk009_valid⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem degreeSevenStageSixPiecewiseRows200To299_prefixes :
    degreeSevenStageSixPrefixes
        degreeSevenStageSixPiecewiseRows200To299 =
      degreeSevenStageSixPrefixesRows200To299 := by
  simp [degreeSevenStageSixPiecewiseRows200To299,
    degreeSevenStageSixPrefixesRows200To299,
    degreeSevenStageSixPrefixesRows200To299Chunk000,
    degreeSevenStageSixPrefixesRows200To299Chunk001,
    degreeSevenStageSixPrefixesRows200To299Chunk002,
    degreeSevenStageSixPrefixesRows200To299Chunk003,
    degreeSevenStageSixPrefixesRows200To299Chunk004,
    degreeSevenStageSixPrefixesRows200To299Chunk005,
    degreeSevenStageSixPrefixesRows200To299Chunk006,
    degreeSevenStageSixPrefixesRows200To299Chunk007,
    degreeSevenStageSixPrefixesRows200To299Chunk008,
    degreeSevenStageSixPrefixesRows200To299Chunk009,
    degreeSevenStageSixPrefixes, List.append_assoc]

/-- End-to-end reduction for a Hunter septic whose first four nonconstant
coefficients match one of the certified Stage Five rows 200 through 299. -/
theorem degreeSevenStageSevenRows200To299_reduces_to_ninetyFour
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (refinement : DegreeSevenStageSixPiecewiseCoverage)
    (hrefinement : refinement ∈ degreeSevenStageSixPiecewiseRows200To299)
    (ha6 : refinement.coverage.parent.a6 = f.coeff 6)
    (ha5 : refinement.coverage.parent.a5 = f.coeff 5)
    (ha4 : refinement.coverage.parent.a4 = f.coeff 4)
    (ha3 : refinement.coverage.parent.a3 = f.coeff 3) :
    [f.coeff 0, f.coeff 1, f.coeff 2, f.coeff 3,
      f.coeff 4, f.coeff 5, f.coeff 6, 1] ∈
        degreeSevenStageSevenSurvivorCoefficientsRows200To299 := by
  have hvalid := List.forall_iff_forall_mem.mp
    degreeSevenStageSixPiecewiseRows200To299_valid refinement hrefinement
  obtain ⟨piece, hpiece, ha2, ha1⟩ :=
    refinement.hunter_a1_mem h hvalid ha6 ha5 ha4 ha3
  have hpieceValid := List.forall_iff_forall_mem.mp
    (refinement.pieces_forall_arithmeticValid hvalid.2) piece hpiece
  have hprefix := refinement.prefix_mem hrefinement piece hpiece
    hpieceValid (f.coeff 2) (f.coeff 1) ha2 ha1
  rw [degreeSevenStageSixPiecewiseRows200To299_prefixes,
    ha6, ha5, ha4, ha3] at hprefix
  exact degreeSevenStageSevenRows200To299_survivor_of_prefix_mem h hprefix

end

end TraceEuclidean
