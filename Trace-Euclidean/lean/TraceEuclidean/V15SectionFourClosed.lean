import TraceEuclidean.V15DegreeThreeHunterClosed
import TraceEuclidean.V15OdlyzkoExplicitFormulaClosed
import TraceEuclidean.V15QuarticImprimitiveCertificate
import TraceEuclidean.V15QuarticPrimitiveShortSelection

/-!
# Closed Section 4 interfaces

This module substitutes the internally proved cubic Hunter certificate into
the Section 4 discriminant and table-membership endpoints. Compatibility
endpoints retain the degree-four through degree-eleven inputs; strengthened
endpoints prove the quadratic-subfield row classification internally, reduce
degree four to seven relative-different norm bounds, and begin the
exact-minimum data in degree five.  The degree-four bound is now proved
internally by the unconditional Minkowski short-vector route.
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

/-- The unconditional degree-four theorem and the residual degree-five to
degree-nine minima imply the earlier degree-four to degree-nine interface. -/
theorem v15_degreeFourToNineMinimumInput_closed
    (hMin : V15DegreeFiveToNineMinimumInput) :
    V15DegreeFourToNineMinimumInput := by
  intro K hreal
  dsimp only
  intro hd4 hd9
  by_cases hdegree : Module.finrank ℚ K.1 = 4
  · have hbound :=
      v15_coded_degree_four_discriminant_ge_725 K hreal hdegree
    simp only [hdegree, v15MinimumDiscriminant]
    exact_mod_cast hbound
  · exact hMin K hreal (by omega) hd9

/-- Strongest Section 4 discriminant endpoint: all degree-one through
degree-four rows are internal, so the exact-minimum source input begins in
degree five. -/
theorem v15_sectionFourDiscriminantInput_of_degreeFiveToEleven_closed
    (hMin : V15DegreeFiveToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput) :
    V15SectionFourDiscriminantInput :=
  v15_sectionFourDiscriminantInput_of_degreeFourToEleven_closed
    (v15_degreeFourToNineMinimumInput_closed hMin) hTen hEleven

/-- The Section 4 discriminant input after reducing the quartic row to its
normalized Hunter certificate.  The exact-minimum table premise now begins
in degree five. -/
theorem v15_sectionFourDiscriminantInput_of_degreeFourHunterCertificate_closed
    (hFour : V15DegreeFourHunterCertificateInput)
    (hMin : V15DegreeFiveToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput) :
    V15SectionFourDiscriminantInput :=
  v15_sectionFourDiscriminantInput_of_degreeFourToEleven_closed
    (v15_degreeFourToNineMinimumInput_of_hunterCertificate hFour hMin)
    hTen hEleven

/-- The Section 4 discriminant input with the quartic row reduced to an
actual primitive Hunter generator and its normalized coefficient and strict
upper-spread bounds. -/
theorem v15_sectionFourDiscriminantInput_of_degreeFourPrimitiveGenerator_closed
    (hFour : V15DegreeFourPrimitiveGeneratorInput)
    (hMin : V15DegreeFiveToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput) :
    V15SectionFourDiscriminantInput :=
  v15_sectionFourDiscriminantInput_of_degreeFourHunterCertificate_closed
    (v15_degree_four_hunterCertificate_of_primitiveGenerator hFour)
    hMin hTen hEleven

/-- The finite imprimitive-quartic inputs and the residual degree-five to
degree-nine minima imply the earlier degree-four to degree-nine interface. -/
theorem v15_degreeFourToNineMinimumInput_of_radicand_and_norm
    (hRadicand : V15QuarticSmallDiscriminantQuadraticRadicandInput)
    (hNorm : V15QuarticSmallDiscriminantRelativeDifferentNormInput)
    (hMin : V15DegreeFiveToNineMinimumInput) :
    V15DegreeFourToNineMinimumInput := by
  intro K hreal
  dsimp only
  intro hd4 hd9
  by_cases hdegree : Module.finrank ℚ K.1 = 4
  · have hbound :=
      v15_coded_degree_four_discriminant_ge_725_of_radicand_and_norm
        hRadicand hNorm K hreal hdegree
    simp only [hdegree, v15MinimumDiscriminant]
    exact_mod_cast hbound
  · exact hMin K hreal (by omega) hd9

/-- The degree-four row now needs only the seven relative-different norm
bounds; the quadratic-subfield discriminant classification is internal. -/
theorem v15_degreeFourToNineMinimumInput_of_relativeDifferentNorm
    (hNorm : V15QuarticSmallDiscriminantRelativeDifferentNormInput)
    (hMin : V15DegreeFiveToNineMinimumInput) :
    V15DegreeFourToNineMinimumInput := by
  intro K hreal
  dsimp only
  intro hd4 hd9
  by_cases hdegree : Module.finrank ℚ K.1 = 4
  · have hbound :=
      v15_coded_degree_four_discriminant_ge_725_of_relativeDifferentNorm
        hNorm K hreal hdegree
    simp only [hdegree, v15MinimumDiscriminant]
    exact_mod_cast hbound
  · exact hMin K hreal (by omega) hd9

/-- Compatibility endpoint splitting the former degree-four source boundary
into a quadratic-radicand bridge and seven relative-different norm bounds. -/
theorem v15_sectionFourDiscriminantInput_of_quarticRelativeDifferent_closed
    (hRadicand : V15QuarticSmallDiscriminantQuadraticRadicandInput)
    (hNorm : V15QuarticSmallDiscriminantRelativeDifferentNormInput)
    (hMin : V15DegreeFiveToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput) :
    V15SectionFourDiscriminantInput :=
  v15_sectionFourDiscriminantInput_of_degreeFourToEleven_closed
    (v15_degreeFourToNineMinimumInput_of_radicand_and_norm
      hRadicand hNorm hMin)
    hTen hEleven

/-- Compatibility endpoint retaining only the seven relative-different norm
bounds from the former quartic source interface. -/
theorem v15_sectionFourDiscriminantInput_of_relativeDifferentNorm_closed
    (hNorm : V15QuarticSmallDiscriminantRelativeDifferentNormInput)
    (hMin : V15DegreeFiveToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput) :
    V15SectionFourDiscriminantInput :=
  v15_sectionFourDiscriminantInput_of_degreeFourToEleven_closed
    (v15_degreeFourToNineMinimumInput_of_relativeDifferentNorm hNorm hMin)
    hTen hEleven

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

/-- Classic-table membership with all degree-one through degree-four field
bounds proved internally. -/
theorem v15_classic_pair_mem_of_degreeFiveToEleven_closed
    (hMin : V15DegreeFiveToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput)
    (c : GlobalLatticeClass)
    (hE : c.IsClassicTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15ClassicAdmissiblePairs :=
  v15_classic_pair_mem_of_degreeFourToEleven_closed
    (v15_degreeFourToNineMinimumInput_closed hMin) hTen hEleven c hE

/-- Classic-table membership with the quartic row represented by its Hunter
certificate and exact-minimum data required only in degrees five through
nine. -/
theorem v15_classic_pair_mem_of_degreeFourHunterCertificate_closed
    (hFour : V15DegreeFourHunterCertificateInput)
    (hMin : V15DegreeFiveToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput)
    (c : GlobalLatticeClass)
    (hE : c.IsClassicTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15ClassicAdmissiblePairs :=
  v15_classic_pair_mem_of_degreeFourToEleven_closed
    (v15_degreeFourToNineMinimumInput_of_hunterCertificate hFour hMin)
    hTen hEleven c hE

/-- Classic-table membership with the quartic source boundary reduced to an
actual primitive Hunter generator and its normalized coefficient and strict
upper-spread bounds. -/
theorem v15_classic_pair_mem_of_degreeFourPrimitiveGenerator_closed
    (hFour : V15DegreeFourPrimitiveGeneratorInput)
    (hMin : V15DegreeFiveToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput)
    (c : GlobalLatticeClass)
    (hE : c.IsClassicTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15ClassicAdmissiblePairs :=
  v15_classic_pair_mem_of_degreeFourHunterCertificate_closed
    (v15_degree_four_hunterCertificate_of_primitiveGenerator hFour)
    hMin hTen hEleven c hE

/-- Classic-table membership with the degree-four input reduced to the finite
quadratic-subfield and relative-different certificate. -/
theorem v15_classic_pair_mem_of_quarticRelativeDifferent_closed
    (hRadicand : V15QuarticSmallDiscriminantQuadraticRadicandInput)
    (hNorm : V15QuarticSmallDiscriminantRelativeDifferentNormInput)
    (hMin : V15DegreeFiveToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput)
    (c : GlobalLatticeClass)
    (hE : c.IsClassicTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15ClassicAdmissiblePairs :=
  v15_classic_pair_mem_of_degreeFourToEleven_closed
    (v15_degreeFourToNineMinimumInput_of_radicand_and_norm
      hRadicand hNorm hMin)
    hTen hEleven c hE

/-- Classic-table membership with the quadratic-subfield classification
proved internally and only the seven relative-different norm bounds retained. -/
theorem v15_classic_pair_mem_of_relativeDifferentNorm_closed
    (hNorm : V15QuarticSmallDiscriminantRelativeDifferentNormInput)
    (hMin : V15DegreeFiveToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput)
    (c : GlobalLatticeClass)
    (hE : c.IsClassicTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15ClassicAdmissiblePairs :=
  v15_classic_pair_mem_of_degreeFourToEleven_closed
    (v15_degreeFourToNineMinimumInput_of_relativeDifferentNorm hNorm hMin)
    hTen hEleven c hE

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

/-- Integral-table membership with all degree-one through degree-four field
bounds proved internally. -/
theorem v15_integral_pair_mem_of_degreeFiveToEleven_closed
    (hMin : V15DegreeFiveToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput)
    (c : GlobalLatticeClass)
    (hE : c.IsIntegralTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15IntegralAdmissiblePairs :=
  v15_integral_pair_mem_of_degreeFourToEleven_closed
    (v15_degreeFourToNineMinimumInput_closed hMin) hTen hEleven c hE

/-- Integral-table membership with the quartic row represented by its Hunter
certificate and exact-minimum data required only in degrees five through
nine. -/
theorem v15_integral_pair_mem_of_degreeFourHunterCertificate_closed
    (hFour : V15DegreeFourHunterCertificateInput)
    (hMin : V15DegreeFiveToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput)
    (c : GlobalLatticeClass)
    (hE : c.IsIntegralTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15IntegralAdmissiblePairs :=
  v15_integral_pair_mem_of_degreeFourToEleven_closed
    (v15_degreeFourToNineMinimumInput_of_hunterCertificate hFour hMin)
    hTen hEleven c hE

/-- Integral-table membership with the quartic source boundary reduced to an
actual primitive Hunter generator and its normalized coefficient and strict
upper-spread bounds. -/
theorem v15_integral_pair_mem_of_degreeFourPrimitiveGenerator_closed
    (hFour : V15DegreeFourPrimitiveGeneratorInput)
    (hMin : V15DegreeFiveToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput)
    (c : GlobalLatticeClass)
    (hE : c.IsIntegralTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15IntegralAdmissiblePairs :=
  v15_integral_pair_mem_of_degreeFourHunterCertificate_closed
    (v15_degree_four_hunterCertificate_of_primitiveGenerator hFour)
    hMin hTen hEleven c hE

/-- Integral-table membership with the degree-four input reduced to the finite
quadratic-subfield and relative-different certificate. -/
theorem v15_integral_pair_mem_of_quarticRelativeDifferent_closed
    (hRadicand : V15QuarticSmallDiscriminantQuadraticRadicandInput)
    (hNorm : V15QuarticSmallDiscriminantRelativeDifferentNormInput)
    (hMin : V15DegreeFiveToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput)
    (c : GlobalLatticeClass)
    (hE : c.IsIntegralTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15IntegralAdmissiblePairs :=
  v15_integral_pair_mem_of_degreeFourToEleven_closed
    (v15_degreeFourToNineMinimumInput_of_radicand_and_norm
      hRadicand hNorm hMin)
    hTen hEleven c hE

/-- Integral-table membership with the quadratic-subfield classification
proved internally and only the seven relative-different norm bounds retained. -/
theorem v15_integral_pair_mem_of_relativeDifferentNorm_closed
    (hNorm : V15QuarticSmallDiscriminantRelativeDifferentNormInput)
    (hMin : V15DegreeFiveToNineMinimumInput)
    (hTen : V15DegreeTenRootDiscriminantInput)
    (hEleven : V15DegreeElevenRootDiscriminantInput)
    (c : GlobalLatticeClass)
    (hE : c.IsIntegralTraceEuclidean (c.degree : ℝ)) :
    (c.rank, c.degree) ∈ v15IntegralAdmissiblePairs :=
  v15_integral_pair_mem_of_degreeFourToEleven_closed
    (v15_degreeFourToNineMinimumInput_of_relativeDifferentNorm hNorm hMin)
    hTen hEleven c hE

end

end TraceEuclidean
