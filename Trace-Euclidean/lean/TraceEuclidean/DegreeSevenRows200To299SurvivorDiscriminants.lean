import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Reduction
import TraceEuclidean.DegreeSevenRows200To299ExceptionalMaximalOrder
import TraceEuclidean.DegreeSevenRows200To299SurvivorDiscriminantGroups.Group000
import TraceEuclidean.DegreeSevenRows200To299SurvivorDiscriminantGroups.Group001
import TraceEuclidean.DegreeSevenRows200To299SurvivorDiscriminantGroups.Group002
import TraceEuclidean.DegreeSevenRows200To299SurvivorDiscriminantGroups.Group003
import TraceEuclidean.DegreeSevenRows200To299SurvivorDiscriminantGroups.Group004
import TraceEuclidean.DegreeSevenRows200To299SurvivorDiscriminantGroups.Group005
import TraceEuclidean.DegreeSevenRows200To299SurvivorDiscriminantGroups.Group006
import TraceEuclidean.DegreeSevenRows200To299SurvivorDiscriminantGroups.Group007
import TraceEuclidean.DegreeSevenRows200To299SurvivorDiscriminantGroups.Group008
import TraceEuclidean.DegreeSevenRows200To299SurvivorDiscriminantGroups.Group009
import TraceEuclidean.DegreeSevenRows200To299SurvivorDiscriminantGroups.Group010
import TraceEuclidean.DegreeSevenRows200To299SurvivorDiscriminantGroups.Group011
import TraceEuclidean.DegreeSevenRows200To299SurvivorDiscriminantGroups.Group012
import TraceEuclidean.DegreeSevenRows200To299SurvivorDiscriminantGroups.Group013
import TraceEuclidean.DegreeSevenRows200To299SurvivorDiscriminantGroups.Group014
import TraceEuclidean.DegreeSevenRows200To299SurvivorDiscriminantGroups.Group015
import TraceEuclidean.DegreeSevenRows200To299SurvivorDiscriminantGroups.Group016
import TraceEuclidean.DegreeSevenRows200To299SurvivorDiscriminantGroups.Group017
import TraceEuclidean.DegreeSevenRows200To299SurvivorDiscriminantGroups.Group018

/-!
# Discriminant closure for Stage Five rows 200 through 299

Exact resultant certificates and one Dedekind maximal-order certificate cover
the complete 94-polynomial irreducible frontier.
-/

namespace TraceEuclidean

open Polynomial

noncomputable section

def degreeSevenFieldDiscriminantLowerBoundCertificatesRows200To299 :
    List DegreeSevenFieldDiscriminantLowerBoundCertificate :=
  [
    DegreeSevenRows200To299SurvivorDiscriminantCase000.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase001.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase002.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase003.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase004.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase005.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299ExceptionalMaximalOrder.lowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase007.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase008.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase009.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase010.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase011.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase012.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase013.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase014.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase015.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase016.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase017.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase018.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase019.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase020.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase021.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase022.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase023.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase024.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase025.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase026.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase027.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase028.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase029.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase030.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase031.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase032.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase033.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase034.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase035.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase036.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase037.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase038.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase039.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase040.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase041.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase042.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase043.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase044.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase045.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase046.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase047.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase048.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase049.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase050.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase051.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase052.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase053.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase054.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase055.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase056.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase057.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase058.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase059.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase060.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase061.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase062.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase063.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase064.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase065.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase066.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase067.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase068.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase069.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase070.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase071.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase072.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase073.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase074.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase075.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase076.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase077.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase078.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase079.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase080.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase081.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase082.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase083.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase084.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase085.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase086.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase087.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase088.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase089.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase090.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase091.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase092.certificate.toLowerBoundCertificate,
    DegreeSevenRows200To299SurvivorDiscriminantCase093.certificate.toLowerBoundCertificate
  ]

theorem degreeSevenFieldDiscriminantLowerBoundCertificatesRows200To299_count :
    degreeSevenFieldDiscriminantLowerBoundCertificatesRows200To299.length =
      94 := by
  rfl

theorem degreeSevenFieldDiscriminantLowerBoundCertificatesRows200To299_coefficients :
    degreeSevenFieldDiscriminantLowerBoundCertificatesRows200To299.map
        DegreeSevenFieldDiscriminantLowerBoundCertificate.coefficients =
      degreeSevenStageSevenSurvivorCoefficientsRows200To299 := by
  rfl

/-- Every retained coefficient list from rows 200 through 299 forces the
target field-discriminant lower bound. -/
theorem degreeSevenRows200To299_fieldDiscriminant_lowerBound_of_survivor
    {K : Type*} [Field K] [NumberField K]
    {f : ℤ[X]} (hfield : HunterFieldPolynomialCandidate K 7 194 f)
    (hcoefficients :
      [f.coeff 0, f.coeff 1, f.coeff 2, f.coeff 3,
        f.coeff 4, f.coeff 5, f.coeff 6, 1] ∈
          degreeSevenStageSevenSurvivorCoefficientsRows200To299) :
    20134393 ≤ (NumberField.discr K).natAbs := by
  rw [←
    degreeSevenFieldDiscriminantLowerBoundCertificatesRows200To299_coefficients]
    at hcoefficients
  obtain ⟨certificate, hcertificate, hcertificateCoefficients⟩ :=
    List.mem_map.mp hcoefficients
  exact certificate.lowerBound hfield hcertificateCoefficients

/-- End-to-end discriminant lower bound for a Hunter septic whose first four
nonconstant coefficients lie in Stage Five rows 200 through 299. -/
theorem degreeSevenStageSevenRows200To299_fieldDiscriminant_lowerBound
    {K : Type*} [Field K] [NumberField K]
    {f : ℤ[X]} (hfield : HunterFieldPolynomialCandidate K 7 194 f)
    (refinement : DegreeSevenStageSixPiecewiseCoverage)
    (hrefinement : refinement ∈ degreeSevenStageSixPiecewiseRows200To299)
    (ha6 : refinement.coverage.parent.a6 = f.coeff 6)
    (ha5 : refinement.coverage.parent.a5 = f.coeff 5)
    (ha4 : refinement.coverage.parent.a4 = f.coeff 4)
    (ha3 : refinement.coverage.parent.a3 = f.coeff 3) :
    20134393 ≤ (NumberField.discr K).natAbs := by
  apply degreeSevenRows200To299_fieldDiscriminant_lowerBound_of_survivor
    hfield
  exact degreeSevenStageSevenRows200To299_reduces_to_ninetyFour
    hfield.1 refinement hrefinement ha6 ha5 ha4 ha3

/-- No row in the certified 200 through 299 block can occur for a field of
absolute discriminant strictly below `20134393`. -/
theorem degreeSevenStageSevenRows200To299_excludes_discriminant_lt
    {K : Type*} [Field K] [NumberField K]
    {f : ℤ[X]} (hfield : HunterFieldPolynomialCandidate K 7 194 f)
    (refinement : DegreeSevenStageSixPiecewiseCoverage)
    (hrefinement : refinement ∈ degreeSevenStageSixPiecewiseRows200To299)
    (ha6 : refinement.coverage.parent.a6 = f.coeff 6)
    (ha5 : refinement.coverage.parent.a5 = f.coeff 5)
    (ha4 : refinement.coverage.parent.a4 = f.coeff 4)
    (ha3 : refinement.coverage.parent.a3 = f.coeff 3)
    (hdiscriminant : (NumberField.discr K).natAbs < 20134393) : False := by
  exact (not_lt_of_ge
    (degreeSevenStageSevenRows200To299_fieldDiscriminant_lowerBound
      hfield refinement hrefinement ha6 ha5 ha4 ha3)) hdiscriminant

end

end TraceEuclidean
