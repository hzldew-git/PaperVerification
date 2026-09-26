import TraceEuclidean.V15SectionFourClosed
import TraceEuclidean.V15VoightEnumerationBridge
import TraceEuclidean.V15DegreeElevenSensitivity

/-!
# Section 4 with the Voight enumeration boundary

This module substitutes the checked Voight discriminant columns and the
single source-facing completeness statement into the strongest Section 4
interfaces.  The only remaining small-degree field input is the optimized
degree-eleven root-discriminant bound.
-/

namespace TraceEuclidean

noncomputable section

/-- The Section 4 discriminant input obtained from Voight's enumeration
through root discriminant fourteen and the optimized degree-eleven bound. -/
theorem v15_sectionFourDiscriminantInput_of_voightEnumeration_closed
    (hEnum : V15VoightEnumerationUpToFourteenInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput) :
    V15SectionFourDiscriminantInput :=
  v15_sectionFourDiscriminantInput_of_degreeFiveToEleven_closed
    (v15_degreeFiveToNineMinimumInput_of_voightEnumeration hEnum)
    (v15_degreeTenRootDiscriminantInput_of_voightEnumeration hEnum)
    hEleven

/-- Membership in the manuscript's classic table, with Voight's enumeration
completeness and the optimized degree-eleven bound as the field inputs. -/
theorem v15_classic_pair_mem_of_voightEnumeration_closed
    (hEnum : V15VoightEnumerationUpToFourteenInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput)
    (c : GlobalLatticeClass)
    (hE : c.IsClassicTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15ClassicAdmissiblePairs :=
  v15_classic_pair_mem_of_degreeFiveToEleven_closed
    (v15_degreeFiveToNineMinimumInput_of_voightEnumeration hEnum)
    (v15_degreeTenRootDiscriminantInput_of_voightEnumeration hEnum)
    hEleven c hE

/-- Membership in the manuscript's integral table, with Voight's enumeration
completeness and the optimized degree-eleven bound as the field inputs. -/
theorem v15_integral_pair_mem_of_voightEnumeration_closed
    (hEnum : V15VoightEnumerationUpToFourteenInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput)
    (c : GlobalLatticeClass)
    (hE : c.IsIntegralTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15IntegralAdmissiblePairs :=
  v15_integral_pair_mem_of_degreeFiveToEleven_closed
    (v15_degreeFiveToNineMinimumInput_of_voightEnumeration hEnum)
    (v15_degreeTenRootDiscriminantInput_of_voightEnumeration hEnum)
    hEleven c hE

/-- Source-aligned Section 4 endpoint using the all-degrees
Odlyzko--Martinet statement quoted in Voight's enumeration paper. -/
theorem v15_sectionFourDiscriminantInput_of_publishedVoightBounds_closed
    (hEnum : V15VoightEnumerationUpToFourteenInput)
    (hBound : V15OdlyzkoMartinetAtLeastElevenInput) :
    V15SectionFourDiscriminantInput :=
  v15_sectionFourDiscriminantInput_of_voightEnumeration_closed hEnum
    (v15_degreeElevenRootDiscriminantInput_of_odlyzkoMartinet hBound)

/-- Classic table membership from the two source-facing bounds recorded in
Voight's paper. -/
theorem v15_classic_pair_mem_of_publishedVoightBounds_closed
    (hEnum : V15VoightEnumerationUpToFourteenInput)
    (hBound : V15OdlyzkoMartinetAtLeastElevenInput)
    (c : GlobalLatticeClass)
    (hE : c.IsClassicTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15ClassicAdmissiblePairs :=
  v15_classic_pair_mem_of_voightEnumeration_closed hEnum
    (v15_degreeElevenRootDiscriminantInput_of_odlyzkoMartinet hBound) c hE

/-- Integral table membership from the two source-facing bounds recorded in
Voight's paper. -/
theorem v15_integral_pair_mem_of_publishedVoightBounds_closed
    (hEnum : V15VoightEnumerationUpToFourteenInput)
    (hBound : V15OdlyzkoMartinetAtLeastElevenInput)
    (c : GlobalLatticeClass)
    (hE : c.IsIntegralTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15IntegralAdmissiblePairs :=
  v15_integral_pair_mem_of_voightEnumeration_closed hEnum
    (v15_degreeElevenRootDiscriminantInput_of_odlyzkoMartinet hBound) c hE

end

end TraceEuclidean
