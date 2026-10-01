import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Closure
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Reducibility.Chunk000
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Reducibility.Chunk001
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Reducibility.Chunk002
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Reducibility.Chunk003
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Reducibility.Chunk004
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Reducibility.Chunk005
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Reducibility.Chunk006
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Reducibility.Chunk007
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Reducibility.Chunk008
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Reducibility.Chunk009

/-!
# Reducibility closure for the first 100 degree-seven Stage Five rows

The ten chunk certificates cover every final `a0` candidate attached to the
exact Stage Seven six-root entries.  Together with the multiple-root and
critical-sign rejection certificates, they exclude a Hunter septic arising
from any of the first 100 piecewise Stage Five rows.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

set_option maxRecDepth 100000

def degreeSevenStageSevenFactorCertificatesPrefix100 :
    List PolynomialFactorCertificate :=
  degreeSevenStageSevenFactorCertificatesPrefix100Chunk000 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk001 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk002 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk003 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk004 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk005 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk006 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk007 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk008 ++
      degreeSevenStageSevenFactorCertificatesPrefix100Chunk009))))))))

theorem degreeSevenStageSevenScaledPrefix100_chunks :
    degreeSevenStageSevenScaledPrefix100 =
      degreeSevenStageSevenScaledPrefix100Chunk000 ++
    (degreeSevenStageSevenScaledPrefix100Chunk001 ++
    (degreeSevenStageSevenScaledPrefix100Chunk002 ++
    (degreeSevenStageSevenScaledPrefix100Chunk003 ++
    (degreeSevenStageSevenScaledPrefix100Chunk004 ++
    (degreeSevenStageSevenScaledPrefix100Chunk005 ++
    (degreeSevenStageSevenScaledPrefix100Chunk006 ++
    (degreeSevenStageSevenScaledPrefix100Chunk007 ++
    (degreeSevenStageSevenScaledPrefix100Chunk008 ++
      degreeSevenStageSevenScaledPrefix100Chunk009)))))))) := by
  unfold degreeSevenStageSevenScaledPrefix100
    degreeSevenStageSevenClassificationsPrefix100
  simp only [DegreeSevenStageSevenClassification.scaledEntries_append]
  rfl

theorem degreeSevenStageSevenScaledPrefix100_arithmeticValid :
    degreeSevenStageSevenScaledPrefix100.Forall
      DegreeSevenStageSevenScaledEntry.ArithmeticValid := by
  rw [degreeSevenStageSevenScaledPrefix100_chunks]
  exact List.forall_append.mpr ⟨
    degreeSevenStageSevenScaledPrefix100Chunk000_arithmeticValid,
    List.forall_append.mpr ⟨
      degreeSevenStageSevenScaledPrefix100Chunk001_arithmeticValid,
      List.forall_append.mpr ⟨
        degreeSevenStageSevenScaledPrefix100Chunk002_arithmeticValid,
        List.forall_append.mpr ⟨
          degreeSevenStageSevenScaledPrefix100Chunk003_arithmeticValid,
          List.forall_append.mpr ⟨
            degreeSevenStageSevenScaledPrefix100Chunk004_arithmeticValid,
            List.forall_append.mpr ⟨
              degreeSevenStageSevenScaledPrefix100Chunk005_arithmeticValid,
              List.forall_append.mpr ⟨
                degreeSevenStageSevenScaledPrefix100Chunk006_arithmeticValid,
                List.forall_append.mpr ⟨
                  degreeSevenStageSevenScaledPrefix100Chunk007_arithmeticValid,
                  List.forall_append.mpr ⟨
                    degreeSevenStageSevenScaledPrefix100Chunk008_arithmeticValid,
                    degreeSevenStageSevenScaledPrefix100Chunk009_arithmeticValid⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem degreeSevenStageSevenFactorCertificatesPrefix100_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100.Forall
      (fun certificate => certificate.check = true) := by
  exact List.forall_append.mpr ⟨
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk000_valid,
    List.forall_append.mpr ⟨
      degreeSevenStageSevenFactorCertificatesPrefix100Chunk001_valid,
      List.forall_append.mpr ⟨
        degreeSevenStageSevenFactorCertificatesPrefix100Chunk002_valid,
        List.forall_append.mpr ⟨
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk003_valid,
          List.forall_append.mpr ⟨
            degreeSevenStageSevenFactorCertificatesPrefix100Chunk004_valid,
            List.forall_append.mpr ⟨
              degreeSevenStageSevenFactorCertificatesPrefix100Chunk005_valid,
              List.forall_append.mpr ⟨
                degreeSevenStageSevenFactorCertificatesPrefix100Chunk006_valid,
                List.forall_append.mpr ⟨
                  degreeSevenStageSevenFactorCertificatesPrefix100Chunk007_valid,
                  List.forall_append.mpr ⟨
                    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008_valid,
                    degreeSevenStageSevenFactorCertificatesPrefix100Chunk009_valid⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem degreeSevenStageSevenFactorCertificatesPrefix100_count :
    degreeSevenStageSevenFactorCertificatesPrefix100.length = 95 := by
  rfl

theorem degreeSevenStageSevenFactorCertificatesPrefix100_complete
    (coefficients : List ℤ) :
    coefficients ∈ degreeSevenStageSevenFinalCoefficients
        degreeSevenStageSevenScaledPrefix100 ↔
      coefficients ∈
        degreeSevenStageSevenFactorCertificatesPrefix100.map
          PolynomialFactorCertificate.coefficients := by
  rw [degreeSevenStageSevenScaledPrefix100_chunks]
  simp only [degreeSevenStageSevenFinalCoefficients_append,
    degreeSevenStageSevenFactorCertificatesPrefix100,
    List.map_append, List.mem_append]
  rw [degreeSevenStageSevenFactorCertificatesPrefix100Chunk000_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk001_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk002_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk003_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk004_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk005_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk006_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk007_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk009_complete coefficients]

/-- A Hunter septic matching one of the six-root entries from the first 100
rows contradicts its checked nontrivial factorization. -/
theorem degreeSevenStageSevenScaledPrefix100_not_hunter
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (entry : DegreeSevenStageSevenScaledEntry)
    (hentry : entry ∈ degreeSevenStageSevenScaledPrefix100)
    (ha6 : entry.a6 = f.coeff 6)
    (ha5 : entry.a5 = f.coeff 5)
    (ha4 : entry.a4 = f.coeff 4)
    (ha3 : entry.a3 = f.coeff 3)
    (ha2 : entry.a2 = f.coeff 2)
    (ha1 : entry.a1 = f.coeff 1) : False := by
  have hentryArithmetic := List.forall_iff_forall_mem.mp
    degreeSevenStageSevenScaledPrefix100_arithmeticValid entry hentry
  have ha0 := degreeSevenStageSevenPrefix100_a0_mem
    h entry hentry ha6 ha5 ha4 ha3 ha2 ha1
  have hcoefficients := entry.coefficients_mem_final hentry
    hentryArithmetic ha0
  have hcertificate :=
    (degreeSevenStageSevenFactorCertificatesPrefix100_complete
      [f.coeff 0, entry.a1, entry.a2, entry.a3,
        entry.a4, entry.a5, entry.a6, 1]).mp hcoefficients
  have hnotIrreducible := not_irreducible_of_mem_factorCertificates
    degreeSevenStageSevenFactorCertificatesPrefix100_valid hcertificate
  apply hnotIrreducible
  rw [ha1, ha2, ha3, ha4, ha5, ha6,
    ← degreeSeven_eq_polynomialOfCoefficients h.1 h.2.2.1]
  exact h.2.1

/-- No Hunter septic has a nonconstant coefficient prefix in the exact
Stage Six prefix list attached to the first 100 Stage Five rows. -/
theorem degreeSevenStageSevenPrefix100_not_hunter_of_prefix_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (hprefix :
      { a6 := f.coeff 6
        a5 := f.coeff 5
        a4 := f.coeff 4
        a3 := f.coeff 3
        a2 := f.coeff 2
        a1 := f.coeff 1 : DegreeSevenStageSevenPrefix } ∈
        degreeSevenStageSixPrefixesPrefix100) : False := by
  let targetPrefix : DegreeSevenStageSevenPrefix :=
    { a6 := f.coeff 6
      a5 := f.coeff 5
      a4 := f.coeff 4
      a3 := f.coeff 3
      a2 := f.coeff 2
      a1 := f.coeff 1 }
  have hprefixFinset :
      targetPrefix ∈ degreeSevenStageSixPrefixesPrefix100.toFinset := by
    exact List.mem_toFinset.mpr hprefix
  rw [degreeSevenStageSevenPrefix100_keyFinsets_eq] at hprefixFinset
  have hclassified :
      targetPrefix ∈ degreeSevenStageSevenClassifiedPrefixesPrefix100 :=
    List.mem_toFinset.mp hprefixFinset
  simp only [degreeSevenStageSevenClassifiedPrefixesPrefix100,
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
    exact degreeSevenStageSevenScaledPrefix100_not_hunter
      h entry hentry ha6 ha5 ha4 ha3 ha2 ha1
  · obtain ⟨witness, hwitness, hwitnessPrefix⟩ := hmultiple
    have hvalid := List.forall_iff_forall_mem.mp
      degreeSevenStageSevenMultipleRootPrefix100_valid witness hwitness
    exact degreeSeven_stageSevenMultipleRootWitness_not_hunter
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
          congrArg DegreeSevenStageSevenPrefix.a1 hwitnessPrefix)
  · obtain ⟨witness, hwitness, hwitnessPrefix⟩ := hcritical
    have hvalid := List.forall_iff_forall_mem.mp
      degreeSevenStageSevenScaledCriticalSignPrefix100_valid
        witness hwitness
    exact degreeSeven_stageSevenCriticalSignWitness_not_hunter
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
          congrArg DegreeSevenStageSevenPrefix.a1 hwitnessPrefix)

def degreeSevenStageSixPiecewisePrefix100 :
    List DegreeSevenStageSixPiecewiseCoverage :=
  degreeSevenStageSixPiecewisePrefix100Chunk000 ++
    (degreeSevenStageSixPiecewisePrefix100Chunk001 ++
    (degreeSevenStageSixPiecewisePrefix100Chunk002 ++
    (degreeSevenStageSixPiecewisePrefix100Chunk003 ++
    (degreeSevenStageSixPiecewisePrefix100Chunk004 ++
    (degreeSevenStageSixPiecewisePrefix100Chunk005 ++
    (degreeSevenStageSixPiecewisePrefix100Chunk006 ++
    (degreeSevenStageSixPiecewisePrefix100Chunk007 ++
    (degreeSevenStageSixPiecewisePrefix100Chunk008 ++
      degreeSevenStageSixPiecewisePrefix100Chunk009))))))))

theorem degreeSevenStageSixPiecewisePrefix100_valid :
    degreeSevenStageSixPiecewisePrefix100.Forall
      DegreeSevenStageSixPiecewiseCoverage.Valid := by
  exact List.forall_append.mpr ⟨
    degreeSevenStageSixPiecewisePrefix100Chunk000_valid,
    List.forall_append.mpr ⟨
      degreeSevenStageSixPiecewisePrefix100Chunk001_valid,
      List.forall_append.mpr ⟨
        degreeSevenStageSixPiecewisePrefix100Chunk002_valid,
        List.forall_append.mpr ⟨
          degreeSevenStageSixPiecewisePrefix100Chunk003_valid,
          List.forall_append.mpr ⟨
            degreeSevenStageSixPiecewisePrefix100Chunk004_valid,
            List.forall_append.mpr ⟨
              degreeSevenStageSixPiecewisePrefix100Chunk005_valid,
              List.forall_append.mpr ⟨
                degreeSevenStageSixPiecewisePrefix100Chunk006_valid,
                List.forall_append.mpr ⟨
                  degreeSevenStageSixPiecewisePrefix100Chunk007_valid,
                  List.forall_append.mpr ⟨
                    degreeSevenStageSixPiecewisePrefix100Chunk008_valid,
                    degreeSevenStageSixPiecewisePrefix100Chunk009_valid⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem degreeSevenStageSixPiecewisePrefix100_prefixes :
    degreeSevenStageSixPrefixes
        degreeSevenStageSixPiecewisePrefix100 =
      degreeSevenStageSixPrefixesPrefix100 := by
  simp [degreeSevenStageSixPiecewisePrefix100,
    degreeSevenStageSixPrefixesPrefix100,
    degreeSevenStageSixPrefixesPrefix100Chunk000,
    degreeSevenStageSixPrefixesPrefix100Chunk001,
    degreeSevenStageSixPrefixesPrefix100Chunk002,
    degreeSevenStageSixPrefixesPrefix100Chunk003,
    degreeSevenStageSixPrefixesPrefix100Chunk004,
    degreeSevenStageSixPrefixesPrefix100Chunk005,
    degreeSevenStageSixPrefixesPrefix100Chunk006,
    degreeSevenStageSixPrefixesPrefix100Chunk007,
    degreeSevenStageSixPrefixesPrefix100Chunk008,
    degreeSevenStageSixPrefixesPrefix100Chunk009,
    degreeSevenStageSixPrefixes]

/-- End-to-end exclusion for a Hunter septic whose first four nonconstant
coefficients match one of the first 100 certified Stage Five rows. -/
theorem degreeSevenStageSevenPrefix100_excludes_first100
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (refinement : DegreeSevenStageSixPiecewiseCoverage)
    (hrefinement : refinement ∈ degreeSevenStageSixPiecewisePrefix100)
    (ha6 : refinement.coverage.parent.a6 = f.coeff 6)
    (ha5 : refinement.coverage.parent.a5 = f.coeff 5)
    (ha4 : refinement.coverage.parent.a4 = f.coeff 4)
    (ha3 : refinement.coverage.parent.a3 = f.coeff 3) : False := by
  have hvalid := List.forall_iff_forall_mem.mp
    degreeSevenStageSixPiecewisePrefix100_valid refinement hrefinement
  obtain ⟨piece, hpiece, ha2, ha1⟩ :=
    refinement.hunter_a1_mem h hvalid ha6 ha5 ha4 ha3
  have hpieceValid := List.forall_iff_forall_mem.mp
    (refinement.pieces_forall_arithmeticValid hvalid.2) piece hpiece
  have hprefix := refinement.prefix_mem hrefinement piece hpiece
    hpieceValid (f.coeff 2) (f.coeff 1) ha2 ha1
  rw [degreeSevenStageSixPiecewisePrefix100_prefixes,
    ha6, ha5, ha4, ha3] at hprefix
  exact degreeSevenStageSevenPrefix100_not_hunter_of_prefix_mem h hprefix

end

end TraceEuclidean
