import TraceEuclidean.DegreeFiveFrontierClassification.Chunk000
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk001
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk002
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk003
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk004
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk005
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk006
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk007
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk008
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk009
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk010
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk011
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk012
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk013
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk014
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk015
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk016
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk017
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk018
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk019
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk020
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk021
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk022
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk023
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk024
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk025
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk026
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk027
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk028
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk029
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk030
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk031
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk032
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk033
import TraceEuclidean.DegreeFiveFrontierClassification.Chunk034

/-!
# Exhaustive proof-bearing classification of the degree-five frontier

The 1,217 final Rolle candidates split into 978 reducible rows, 215 rows
with a safe discriminant quotient, and 24 rows with maximal-order field
certificates.  Every constructor carries the proof used below.
-/

namespace TraceEuclidean

open Polynomial

universe u

def degreeFiveCertifiedCases :
    List DegreeFiveCertifiedCase.{u} :=
  degreeFiveCertifiedCasesChunk000.{u} ++
    degreeFiveCertifiedCasesChunk001.{u} ++
    degreeFiveCertifiedCasesChunk002.{u} ++
    degreeFiveCertifiedCasesChunk003.{u} ++
    degreeFiveCertifiedCasesChunk004.{u} ++
    degreeFiveCertifiedCasesChunk005.{u} ++
    degreeFiveCertifiedCasesChunk006.{u} ++
    degreeFiveCertifiedCasesChunk007.{u} ++
    degreeFiveCertifiedCasesChunk008.{u} ++
    degreeFiveCertifiedCasesChunk009.{u} ++
    degreeFiveCertifiedCasesChunk010.{u} ++
    degreeFiveCertifiedCasesChunk011.{u} ++
    degreeFiveCertifiedCasesChunk012.{u} ++
    degreeFiveCertifiedCasesChunk013.{u} ++
    degreeFiveCertifiedCasesChunk014.{u} ++
    degreeFiveCertifiedCasesChunk015.{u} ++
    degreeFiveCertifiedCasesChunk016.{u} ++
    degreeFiveCertifiedCasesChunk017.{u} ++
    degreeFiveCertifiedCasesChunk018.{u} ++
    degreeFiveCertifiedCasesChunk019.{u} ++
    degreeFiveCertifiedCasesChunk020.{u} ++
    degreeFiveCertifiedCasesChunk021.{u} ++
    degreeFiveCertifiedCasesChunk022.{u} ++
    degreeFiveCertifiedCasesChunk023.{u} ++
    degreeFiveCertifiedCasesChunk024.{u} ++
    degreeFiveCertifiedCasesChunk025.{u} ++
    degreeFiveCertifiedCasesChunk026.{u} ++
    degreeFiveCertifiedCasesChunk027.{u} ++
    degreeFiveCertifiedCasesChunk028.{u} ++
    degreeFiveCertifiedCasesChunk029.{u} ++
    degreeFiveCertifiedCasesChunk030.{u} ++
    degreeFiveCertifiedCasesChunk031.{u} ++
    degreeFiveCertifiedCasesChunk032.{u} ++
    degreeFiveCertifiedCasesChunk033.{u} ++
    degreeFiveCertifiedCasesChunk034.{u}

theorem degreeFiveCertifiedCases_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈
          (degreeFiveStageFiveEntries.flatMap fun entry =>
            entry.a0Candidates.toList.map fun a0 =>
              [a0, entry.a1, entry.a2, entry.a3, entry.a4, 1]) ↔
        coefficients ∈
          degreeFiveCertifiedCases.{u}.map
            DegreeFiveCertifiedCase.coefficients := by
  intro coefficients
  simp only [degreeFiveStageFiveEntries,
    degreeFiveCertifiedCases, List.flatMap_append,
    List.map_append, List.mem_append]
  rw [degreeFiveCertifiedCasesChunk000_complete coefficients,
    degreeFiveCertifiedCasesChunk001_complete coefficients,
    degreeFiveCertifiedCasesChunk002_complete coefficients,
    degreeFiveCertifiedCasesChunk003_complete coefficients,
    degreeFiveCertifiedCasesChunk004_complete coefficients,
    degreeFiveCertifiedCasesChunk005_complete coefficients,
    degreeFiveCertifiedCasesChunk006_complete coefficients,
    degreeFiveCertifiedCasesChunk007_complete coefficients,
    degreeFiveCertifiedCasesChunk008_complete coefficients,
    degreeFiveCertifiedCasesChunk009_complete coefficients,
    degreeFiveCertifiedCasesChunk010_complete coefficients,
    degreeFiveCertifiedCasesChunk011_complete coefficients,
    degreeFiveCertifiedCasesChunk012_complete coefficients,
    degreeFiveCertifiedCasesChunk013_complete coefficients,
    degreeFiveCertifiedCasesChunk014_complete coefficients,
    degreeFiveCertifiedCasesChunk015_complete coefficients,
    degreeFiveCertifiedCasesChunk016_complete coefficients,
    degreeFiveCertifiedCasesChunk017_complete coefficients,
    degreeFiveCertifiedCasesChunk018_complete coefficients,
    degreeFiveCertifiedCasesChunk019_complete coefficients,
    degreeFiveCertifiedCasesChunk020_complete coefficients,
    degreeFiveCertifiedCasesChunk021_complete coefficients,
    degreeFiveCertifiedCasesChunk022_complete coefficients,
    degreeFiveCertifiedCasesChunk023_complete coefficients,
    degreeFiveCertifiedCasesChunk024_complete coefficients,
    degreeFiveCertifiedCasesChunk025_complete coefficients,
    degreeFiveCertifiedCasesChunk026_complete coefficients,
    degreeFiveCertifiedCasesChunk027_complete coefficients,
    degreeFiveCertifiedCasesChunk028_complete coefficients,
    degreeFiveCertifiedCasesChunk029_complete coefficients,
    degreeFiveCertifiedCasesChunk030_complete coefficients,
    degreeFiveCertifiedCasesChunk031_complete coefficients,
    degreeFiveCertifiedCasesChunk032_complete coefficients,
    degreeFiveCertifiedCasesChunk033_complete coefficients,
    degreeFiveCertifiedCasesChunk034_complete coefficients]

/-- Every field-realizable sharpened Hunter quintic is represented by a
proof-bearing frontier case. -/
theorem degreeFive_hunterFieldCandidate_exists_certifiedCase
    {K : Type u} [Field K] [NumberField K]
    {f : ℤ[X]}
    (hfield : HunterFieldPolynomialCandidate K 5 67 f) :
    ∃ certificate ∈ degreeFiveCertifiedCases.{u},
      certificate.coefficients =
        [f.coeff 0, f.coeff 1, f.coeff 2,
          f.coeff 3, f.coeff 4, 1] := by
  obtain ⟨entry, hentry, ha4, ha3, ha2, ha1, ha0⟩ :=
    degreeFive_minimumHunterCandidate_stageFive_frontier_complete
      hfield.1
  have hmembership :
      [f.coeff 0, f.coeff 1, f.coeff 2,
        f.coeff 3, f.coeff 4, 1] ∈
        (degreeFiveStageFiveEntries.flatMap fun current =>
          current.a0Candidates.toList.map fun a0 =>
            [a0, current.a1, current.a2,
              current.a3, current.a4, 1]) := by
    apply List.mem_flatMap.mpr
    refine ⟨entry, hentry, ?_⟩
    apply List.mem_map.mpr
    refine ⟨f.coeff 0, Finset.mem_toList.mpr ha0, ?_⟩
    simp [ha1, ha2, ha3, ha4]
  rw [degreeFiveCertifiedCases_complete] at hmembership
  obtain ⟨certificate, hcertificate, heq⟩ :=
    List.mem_map.mp hmembership
  exact ⟨certificate, hcertificate, heq⟩

/-- The complete degree-five frontier rules out every totally real quintic
field of absolute discriminant below `14641`. -/
theorem no_totallyRealQuinticField_discriminant_lt_14641
    (K : Type u) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 5)
    (hdisc : ((|NumberField.discr K| : ℤ) : ℝ) < 14641) : False := by
  obtain ⟨f, hfield⟩ :=
    exists_degreeFive_hunterFieldCandidate_of_discriminant_lt_14641
      K hreal hdegree hdisc
  obtain ⟨certificate, _, hcoefficients⟩ :=
    degreeFive_hunterFieldCandidate_exists_certifiedCase hfield
  have hlower : 14641 ≤ (NumberField.discr K).natAbs :=
    DegreeFiveCertifiedCase.fieldDiscriminant_lowerBound
      hfield certificate hcoefficients
  have hdiscInt : |NumberField.discr K| < (14641 : ℤ) := by
    exact_mod_cast hdisc
  have hdiscNat : (NumberField.discr K).natAbs < 14641 := by
    rw [← Nat.cast_lt (α := ℤ), Int.natCast_natAbs]
    exact hdiscInt
  omega

end TraceEuclidean
