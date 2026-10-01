import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Reduction
import TraceEuclidean.DegreeSevenSurvivorDiscriminants.Case000
import TraceEuclidean.DegreeSevenSurvivorDiscriminants.Case001
import TraceEuclidean.DegreeSevenSurvivorDiscriminants.Case002
import TraceEuclidean.DegreeSevenSurvivorDiscriminants.Case003
import TraceEuclidean.DegreeSevenSurvivorDiscriminants.Case004
import TraceEuclidean.DegreeSevenSurvivorDiscriminants.Case005
import TraceEuclidean.DegreeSevenSurvivorDiscriminants.Case006
import TraceEuclidean.DegreeSevenSurvivorDiscriminants.Case007
import TraceEuclidean.DegreeSevenSurvivorDiscriminants.Case008

/-!
# Discriminant closure for Stage Five rows 100 through 199

The nine exact resultant certificates cover the complete irreducible frontier
left by the coefficient search.  Each squarefree residual discriminant is at
least `20134393`, so none can generate a field below that threshold.
-/

namespace TraceEuclidean

open Polynomial

noncomputable section

def degreeSevenSurvivorDiscriminantCertificatesRows100To199 :
    List DegreeSevenSurvivorDiscriminantCertificate :=
  [
    DegreeSevenSurvivorDiscriminantCase000.certificate,
    DegreeSevenSurvivorDiscriminantCase001.certificate,
    DegreeSevenSurvivorDiscriminantCase002.certificate,
    DegreeSevenSurvivorDiscriminantCase003.certificate,
    DegreeSevenSurvivorDiscriminantCase004.certificate,
    DegreeSevenSurvivorDiscriminantCase005.certificate,
    DegreeSevenSurvivorDiscriminantCase006.certificate,
    DegreeSevenSurvivorDiscriminantCase007.certificate,
    DegreeSevenSurvivorDiscriminantCase008.certificate
  ]

theorem degreeSevenSurvivorDiscriminantCertificatesRows100To199_count :
    degreeSevenSurvivorDiscriminantCertificatesRows100To199.length = 9 := by
  rfl

theorem degreeSevenSurvivorDiscriminantCertificatesRows100To199_coefficients :
    degreeSevenSurvivorDiscriminantCertificatesRows100To199.map
        DegreeSevenSurvivorDiscriminantCertificate.coefficients =
      degreeSevenStageSevenSurvivorCoefficientsRows100To199 := by
  rfl

/-- Every retained coefficient list forces the field discriminant to meet the
target threshold. -/
theorem degreeSevenRows100To199_fieldDiscriminant_lowerBound_of_survivor
    {K : Type*} [Field K] [NumberField K]
    {f : ℤ[X]} (hfield : HunterFieldPolynomialCandidate K 7 194 f)
    (hcoefficients :
      [f.coeff 0, f.coeff 1, f.coeff 2, f.coeff 3,
        f.coeff 4, f.coeff 5, f.coeff 6, 1] ∈
          degreeSevenStageSevenSurvivorCoefficientsRows100To199) :
    20134393 ≤ (NumberField.discr K).natAbs := by
  rw [←
    degreeSevenSurvivorDiscriminantCertificatesRows100To199_coefficients]
    at hcoefficients
  obtain ⟨certificate, hcertificate, hcertificateCoefficients⟩ :=
    List.mem_map.mp hcoefficients
  exact certificate.fieldDiscriminant_lowerBound
    hfield hcertificateCoefficients

/-- End-to-end discriminant lower bound for a Hunter septic whose first four
nonconstant coefficients lie in Stage Five rows 100 through 199. -/
theorem degreeSevenStageSevenRows100To199_fieldDiscriminant_lowerBound
    {K : Type*} [Field K] [NumberField K]
    {f : ℤ[X]} (hfield : HunterFieldPolynomialCandidate K 7 194 f)
    (refinement : DegreeSevenStageSixPiecewiseCoverage)
    (hrefinement : refinement ∈ degreeSevenStageSixPiecewiseRows100To199)
    (ha6 : refinement.coverage.parent.a6 = f.coeff 6)
    (ha5 : refinement.coverage.parent.a5 = f.coeff 5)
    (ha4 : refinement.coverage.parent.a4 = f.coeff 4)
    (ha3 : refinement.coverage.parent.a3 = f.coeff 3) :
    20134393 ≤ (NumberField.discr K).natAbs := by
  apply degreeSevenRows100To199_fieldDiscriminant_lowerBound_of_survivor
    hfield
  exact degreeSevenStageSevenRows100To199_reduces_to_nine
    hfield.1 refinement hrefinement ha6 ha5 ha4 ha3

/-- No row in the certified 100 through 199 block can occur for a field of
absolute discriminant strictly below `20134393`. -/
theorem degreeSevenStageSevenRows100To199_excludes_discriminant_lt
    {K : Type*} [Field K] [NumberField K]
    {f : ℤ[X]} (hfield : HunterFieldPolynomialCandidate K 7 194 f)
    (refinement : DegreeSevenStageSixPiecewiseCoverage)
    (hrefinement : refinement ∈ degreeSevenStageSixPiecewiseRows100To199)
    (ha6 : refinement.coverage.parent.a6 = f.coeff 6)
    (ha5 : refinement.coverage.parent.a5 = f.coeff 5)
    (ha4 : refinement.coverage.parent.a4 = f.coeff 4)
    (ha3 : refinement.coverage.parent.a3 = f.coeff 3)
    (hdiscriminant : (NumberField.discr K).natAbs < 20134393) : False := by
  exact (not_lt_of_ge
    (degreeSevenStageSevenRows100To199_fieldDiscriminant_lowerBound
      hfield refinement hrefinement ha6 ha5 ha4 ha3)) hdiscriminant

end

end TraceEuclidean
