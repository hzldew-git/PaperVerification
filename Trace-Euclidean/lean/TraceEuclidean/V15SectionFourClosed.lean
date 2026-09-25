import TraceEuclidean.V15DegreeThreeHunterClosed
import TraceEuclidean.V15OdlyzkoExplicitFormulaClosed

/-!
# Closed Section 4 interfaces

This module substitutes the internally proved cubic Hunter certificate into
the Section 4 discriminant and table-membership endpoints.  The only remaining
source inputs in these endpoints concern degrees four through eleven.
-/

namespace TraceEuclidean

noncomputable section

/-- The Section 4 discriminant input after discharging the cubic Hunter
certificate and the analytic Table 4 range internally. -/
theorem v15_sectionFourDiscriminantInput_of_degreeFourToEleven_closed
    (hMin : V15DegreeFourToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput) :
    V15SectionFourDiscriminantInput :=
  v15_sectionFourDiscriminantInput_of_hunterCertificate_closed
    v15_degree_three_hunterCertificate hMin hTen hEleven

/-- Membership in the manuscript's classic table, with only the degree-four
through degree-eleven discriminant source inputs remaining. -/
theorem v15_classic_pair_mem_of_degreeFourToEleven_closed
    (hMin : V15DegreeFourToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput)
    (c : GlobalLatticeClass)
    (hE : c.IsClassicTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15ClassicAdmissiblePairs :=
  v15_classic_pair_mem_of_hunterCertificate_closed
    v15_degree_three_hunterCertificate hMin hTen hEleven c hE

/-- Membership in the manuscript's integral table, with only the degree-four
through degree-eleven discriminant source inputs remaining. -/
theorem v15_integral_pair_mem_of_degreeFourToEleven_closed
    (hMin : V15DegreeFourToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput)
    (c : GlobalLatticeClass)
    (hE : c.IsIntegralTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15IntegralAdmissiblePairs :=
  v15_integral_pair_mem_of_hunterCertificate_closed
    v15_degree_three_hunterCertificate hMin hTen hEleven c hE

end

end TraceEuclidean
