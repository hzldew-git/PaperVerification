import TraceEuclidean.DegreeSevenRolleStageSixPiecewise
import TraceEuclidean.DegreeSevenRolleStageSixStrongCompactCompleteness

/-!
# Global completeness of piecewise degree-seven Stage Six certificates

This module separates the proof of completeness from the generated piecewise
certificate table.  Any valid refinement list whose parent coverages are
exactly the established compact Stage Six coverage list inherits the global
Hunter-candidate completeness theorem.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

/-- A valid piecewise refinement of every compact Stage Six coverage contains
the coefficients `a2` and `a1` of every sharpened septic Hunter candidate. -/
theorem degreeSeven_minimumHunterCandidate_stageSix_piecewise_complete
    (refinements : List DegreeSevenStageSixPiecewiseCoverage)
    (hvalid : refinements.Forall
      DegreeSevenStageSixPiecewiseCoverage.Valid)
    (hcoverages :
      refinements.map DegreeSevenStageSixPiecewiseCoverage.coverage =
        degreeSevenStageSixStrongCompactCoverages)
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f) :
    ∃ refinement ∈ refinements,
      ∃ piece ∈ refinement.pieces,
        f.coeff 2 ∈ piece.toFamily.a2Candidates ∧
          f.coeff 1 ∈
            (piece.toFamily.toEntry (f.coeff 2)).a1Candidates := by
  obtain ⟨coverage, hcoverage, ha6, ha5, ha4, ha3,
      _, _, _, _⟩ :=
    degreeSeven_minimumHunterCandidate_stageSix_complete_with_top h
  have hcoverageMap :
      coverage ∈
        refinements.map DegreeSevenStageSixPiecewiseCoverage.coverage := by
    rw [hcoverages]
    exact hcoverage
  obtain ⟨refinement, hrefinement, hrefinementCoverage⟩ :=
    List.mem_map.mp hcoverageMap
  have hrefinementValid : refinement.Valid :=
    (List.forall_iff_forall_mem.mp hvalid) refinement hrefinement
  have hrefinementA6 : refinement.coverage.parent.a6 = f.coeff 6 := by
    rw [hrefinementCoverage]
    exact ha6
  have hrefinementA5 : refinement.coverage.parent.a5 = f.coeff 5 := by
    rw [hrefinementCoverage]
    exact ha5
  have hrefinementA4 : refinement.coverage.parent.a4 = f.coeff 4 := by
    rw [hrefinementCoverage]
    exact ha4
  have hrefinementA3 : refinement.coverage.parent.a3 = f.coeff 3 := by
    rw [hrefinementCoverage]
    exact ha3
  obtain ⟨piece, hpiece, ha2, ha1⟩ :=
    DegreeSevenStageSixPiecewiseCoverage.hunter_a1_mem h refinement
      hrefinementValid hrefinementA6 hrefinementA5 hrefinementA4 hrefinementA3
  exact ⟨refinement, hrefinement, piece, hpiece, ha2, ha1⟩

end

end TraceEuclidean
