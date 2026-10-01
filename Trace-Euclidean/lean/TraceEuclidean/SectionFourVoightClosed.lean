import TraceEuclidean.SectionFourClosed
import TraceEuclidean.VoightEnumerationBridge
import TraceEuclidean.DegreeFiveMinimumClosed
import TraceEuclidean.DegreeElevenSensitivity
import TraceEuclidean.PoitouDegreeElevenClosed

/-!
# Section 4 with the Voight enumeration boundary

This module substitutes the checked Voight discriminant columns and the
single source-facing completeness statement into the strongest Section 4
interfaces.  The only remaining small-degree field input is the optimized
degree-eleven root-discriminant bound.
-/

namespace TraceEuclidean

noncomputable section

/-- The Section 4 discriminant input after proving the degree-five minimum
internally.  The Voight completeness premise now starts in degree six. -/
theorem sectionFourDiscriminantInput_of_voightEnumerationSixToTen_closed
    (hEnum : VoightEnumerationSixToTenInput)
    (hEleven : DegreeElevenRootDiscriminantInput) :
    SectionFourDiscriminantInput :=
  sectionFourDiscriminantInput_of_degreeFiveToEleven_closed
    (degreeFiveToNineMinimumInput_of_sixToNine
      (degreeSixToNineMinimumInput_of_voightEnumeration hEnum))
    (degreeTenRootDiscriminantInput_of_voightEnumerationSixToTen hEnum)
    hEleven

/-- Classic-table membership after closing the quintic minimum internally. -/
theorem classic_pair_mem_of_voightEnumerationSixToTen_closed
    (hEnum : VoightEnumerationSixToTenInput)
    (hEleven : DegreeElevenRootDiscriminantInput)
    (c : GlobalLatticeClass)
    (hE : c.IsClassicTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ classicAdmissiblePairs :=
  classic_pair_mem_of_degreeFiveToEleven_closed
    (degreeFiveToNineMinimumInput_of_sixToNine
      (degreeSixToNineMinimumInput_of_voightEnumeration hEnum))
    (degreeTenRootDiscriminantInput_of_voightEnumerationSixToTen hEnum)
    hEleven c hE

/-- Integral-table membership after closing the quintic minimum internally. -/
theorem integral_pair_mem_of_voightEnumerationSixToTen_closed
    (hEnum : VoightEnumerationSixToTenInput)
    (hEleven : DegreeElevenRootDiscriminantInput)
    (c : GlobalLatticeClass)
    (hE : c.IsIntegralTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ integralAdmissiblePairs :=
  integral_pair_mem_of_degreeFiveToEleven_closed
    (degreeFiveToNineMinimumInput_of_sixToNine
      (degreeSixToNineMinimumInput_of_voightEnumeration hEnum))
    (degreeTenRootDiscriminantInput_of_voightEnumerationSixToTen hEnum)
    hEleven c hE

/-- The Section 4 discriminant input obtained from Voight's enumeration
through root discriminant fourteen and the optimized degree-eleven bound. -/
theorem sectionFourDiscriminantInput_of_voightEnumeration_closed
    (hEnum : VoightEnumerationUpToFourteenInput)
    (hEleven : DegreeElevenRootDiscriminantInput) :
    SectionFourDiscriminantInput :=
  sectionFourDiscriminantInput_of_voightEnumerationSixToTen_closed
    (voightEnumerationSixToTenInput_of_fiveToTen hEnum) hEleven

/-- Membership in the manuscript's classic table, with Voight's enumeration
completeness and the optimized degree-eleven bound as the field inputs. -/
theorem classic_pair_mem_of_voightEnumeration_closed
    (hEnum : VoightEnumerationUpToFourteenInput)
    (hEleven : DegreeElevenRootDiscriminantInput)
    (c : GlobalLatticeClass)
    (hE : c.IsClassicTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ classicAdmissiblePairs :=
  classic_pair_mem_of_voightEnumerationSixToTen_closed
    (voightEnumerationSixToTenInput_of_fiveToTen hEnum)
    hEleven c hE

/-- Membership in the manuscript's integral table, with Voight's enumeration
completeness and the optimized degree-eleven bound as the field inputs. -/
theorem integral_pair_mem_of_voightEnumeration_closed
    (hEnum : VoightEnumerationUpToFourteenInput)
    (hEleven : DegreeElevenRootDiscriminantInput)
    (c : GlobalLatticeClass)
    (hE : c.IsIntegralTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ integralAdmissiblePairs :=
  integral_pair_mem_of_voightEnumerationSixToTen_closed
    (voightEnumerationSixToTenInput_of_fiveToTen hEnum)
    hEleven c hE

/-- Strongest Poitou endpoint after closing the degree-five minimum. -/
theorem sectionFourDiscriminantInput_of_voightEnumerationSixToTen_poitou
    (hEnum : VoightEnumerationSixToTenInput)
    (hFormula :
      PoitouDegreeEleven.PoitouDegreeElevenFormulaInput) :
    SectionFourDiscriminantInput :=
  sectionFourDiscriminantInput_of_voightEnumerationSixToTen_closed hEnum
    (PoitouDegreeElevenClosed.degreeElevenRootDiscriminantInput_of_poitouFormula
      hFormula)

/-- Strongest classic-table endpoint after closing the quintic minimum. -/
theorem classic_pair_mem_of_voightEnumerationSixToTen_poitou
    (hEnum : VoightEnumerationSixToTenInput)
    (hFormula :
      PoitouDegreeEleven.PoitouDegreeElevenFormulaInput)
    (c : GlobalLatticeClass)
    (hE : c.IsClassicTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ classicAdmissiblePairs :=
  classic_pair_mem_of_voightEnumerationSixToTen_closed hEnum
    (PoitouDegreeElevenClosed.degreeElevenRootDiscriminantInput_of_poitouFormula
      hFormula) c hE

/-- Strongest integral-table endpoint after closing the quintic minimum. -/
theorem integral_pair_mem_of_voightEnumerationSixToTen_poitou
    (hEnum : VoightEnumerationSixToTenInput)
    (hFormula :
      PoitouDegreeEleven.PoitouDegreeElevenFormulaInput)
    (c : GlobalLatticeClass)
    (hE : c.IsIntegralTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ integralAdmissiblePairs :=
  integral_pair_mem_of_voightEnumerationSixToTen_closed hEnum
    (PoitouDegreeElevenClosed.degreeElevenRootDiscriminantInput_of_poitouFormula
      hFormula) c hE

/-- The Section 4 discriminant input obtained from Voight completeness and
Poitou's specialized degree-eleven explicit formula.  The numerical
optimization producing `14.083` is discharged internally. -/
theorem sectionFourDiscriminantInput_of_voightEnumeration_poitou
    (hEnum : VoightEnumerationUpToFourteenInput)
    (hFormula :
      PoitouDegreeEleven.PoitouDegreeElevenFormulaInput) :
    SectionFourDiscriminantInput :=
  sectionFourDiscriminantInput_of_voightEnumerationSixToTen_poitou
    (voightEnumerationSixToTenInput_of_fiveToTen hEnum) hFormula

/-- Classic table membership from Voight completeness and Poitou's
specialized degree-eleven explicit formula. -/
theorem classic_pair_mem_of_voightEnumeration_poitou
    (hEnum : VoightEnumerationUpToFourteenInput)
    (hFormula :
      PoitouDegreeEleven.PoitouDegreeElevenFormulaInput)
    (c : GlobalLatticeClass)
    (hE : c.IsClassicTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ classicAdmissiblePairs :=
  classic_pair_mem_of_voightEnumerationSixToTen_poitou
    (voightEnumerationSixToTenInput_of_fiveToTen hEnum)
    hFormula c hE

/-- Integral table membership from Voight completeness and Poitou's
specialized degree-eleven explicit formula. -/
theorem integral_pair_mem_of_voightEnumeration_poitou
    (hEnum : VoightEnumerationUpToFourteenInput)
    (hFormula :
      PoitouDegreeEleven.PoitouDegreeElevenFormulaInput)
    (c : GlobalLatticeClass)
    (hE : c.IsIntegralTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ integralAdmissiblePairs :=
  integral_pair_mem_of_voightEnumerationSixToTen_poitou
    (voightEnumerationSixToTenInput_of_fiveToTen hEnum)
    hFormula c hE

/-- Source-aligned Section 4 endpoint using the all-degrees
Odlyzko--Martinet statement quoted in Voight's enumeration paper. -/
theorem sectionFourDiscriminantInput_of_publishedVoightBounds_closed
    (hEnum : VoightEnumerationUpToFourteenInput)
    (hBound : OdlyzkoMartinetAtLeastElevenInput) :
    SectionFourDiscriminantInput :=
  sectionFourDiscriminantInput_of_voightEnumeration_closed hEnum
    (degreeElevenRootDiscriminantInput_of_odlyzkoMartinet hBound)

/-- Classic table membership from the two source-facing bounds recorded in
Voight's paper. -/
theorem classic_pair_mem_of_publishedVoightBounds_closed
    (hEnum : VoightEnumerationUpToFourteenInput)
    (hBound : OdlyzkoMartinetAtLeastElevenInput)
    (c : GlobalLatticeClass)
    (hE : c.IsClassicTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ classicAdmissiblePairs :=
  classic_pair_mem_of_voightEnumeration_closed hEnum
    (degreeElevenRootDiscriminantInput_of_odlyzkoMartinet hBound) c hE

/-- Integral table membership from the two source-facing bounds recorded in
Voight's paper. -/
theorem integral_pair_mem_of_publishedVoightBounds_closed
    (hEnum : VoightEnumerationUpToFourteenInput)
    (hBound : OdlyzkoMartinetAtLeastElevenInput)
    (c : GlobalLatticeClass)
    (hE : c.IsIntegralTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ integralAdmissiblePairs :=
  integral_pair_mem_of_voightEnumeration_closed hEnum
    (degreeElevenRootDiscriminantInput_of_odlyzkoMartinet hBound) c hE

end

end TraceEuclidean
