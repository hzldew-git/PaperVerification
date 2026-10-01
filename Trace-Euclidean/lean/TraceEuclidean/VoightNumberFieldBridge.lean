import TraceEuclidean.VoightNumberFieldCore
import TraceEuclidean.VoightPolynomialBridge
import TraceEuclidean.VoightTotalRealityCertificates
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# Number fields presented by the archived Voight polynomials

The archived tables supply integral defining polynomials.  Earlier modules
prove that all 2,773 polynomials are irreducible and split over the reals.
This module converts those polynomial statements into actual totally real
number fields of the expected degree.
-/

namespace TraceEuclidean

open Polynomial

noncomputable section

/-- Every row in one archived degree table has a monic defining
polynomial. -/
theorem voightPolynomialRows_monic (degree : ℕ) :
    ∀ row ∈ voightPolynomialRows degree, row.polynomial.Monic := by
  intro row hrow
  have hvalid :=
    (List.all_eq_true.mp
      (voightPolynomialRows_structural_certificate degree)) row hrow
  have hconditions :=
    (voightPolynomialRow_structurallyValid_iff degree row).1 hvalid
  exact (voightPolynomial_isMonicOfDegree degree row
    hconditions.1 hconditions.2.1).monic

/-- All archived degree 5 through 10 defining polynomials are monic. -/
theorem allVoightPolynomialRows_monic :
    ∀ row ∈ allVoightPolynomialRows, row.polynomial.Monic := by
  dsimp [allVoightPolynomialRows]
  exact forall_mem_append
    (voightPolynomialRows_monic 5)
    (forall_mem_append
      (voightPolynomialRows_monic 6)
      (forall_mem_append
        (voightPolynomialRows_monic 7)
        (forall_mem_append
          (voightPolynomialRows_monic 8)
          (forall_mem_append
            (voightPolynomialRows_monic 9)
            (voightPolynomialRows_monic 10)))))

/-- Every archived degree 5 through 10 row presents an actual totally real
number field whose degree is the defining-polynomial degree. -/
theorem allVoightPolynomialRows_present_totallyRealNumberField :
    ∀ row ∈ allVoightPolynomialRows,
      row.PresentsTotallyRealNumberField := by
  intro row hrow
  exact voightPolynomialRow_presentsTotallyRealNumberField row
    (allVoightPolynomialRows_monic row hrow)
    (allVoightPolynomialRows_irreducible row hrow)
    (allVoightPolynomialRows_splits row hrow)

end

end TraceEuclidean
