import TraceEuclidean.VoightIrreducibilityCertificates
import TraceEuclidean.VoightSpecialIrreducibility
import TraceEuclidean.VoightAllRows

/-!
# Irreducibility of every archived Voight defining polynomial

This module combines the single-prime Rabin certificates, the multi-prime
factor-degree certificates, and the exceptional degree-eight coefficient
argument.  The final theorem covers all `2773` defining polynomials in the
archived degree `5` through `10` tables.
-/

namespace TraceEuclidean

/-- Combine a certificate for the filtered regular rows with a certificate
for the explicitly listed exceptional rows. -/
theorem irreducible_of_regular_and_exceptions
    {rows exceptions : List VoightPolynomialRow}
    (hregular : ∀ row ∈ rows.filter
      (fun row => decide (row ∉ exceptions)), Irreducible row.polynomial)
    (hexceptions : ∀ row ∈ exceptions, Irreducible row.polynomial) :
    ∀ row ∈ rows, Irreducible row.polynomial := by
  intro row hrow
  by_cases hexception : row ∈ exceptions
  · exact hexceptions row hexception
  · apply hregular row
    exact List.mem_filter.mpr ⟨hrow, by simp [hexception]⟩

theorem voightRabinExceptionsFive_irreducible :
    ∀ row ∈ voightRabinExceptionsFive,
      Irreducible row.polynomial := by
  simp [voightRabinExceptionsFive]

theorem voightRabinExceptionsSix_irreducible :
    ∀ row ∈ voightRabinExceptionsSix,
      Irreducible row.polynomial := by
  have heq : voightRabinExceptionsSix =
      voightMultiPrimeRowsSix := by
    native_decide
  rw [heq]
  exact voightMultiPrimeRowsSix_irreducible

theorem voightRabinExceptionsSeven_irreducible :
    ∀ row ∈ voightRabinExceptionsSeven,
      Irreducible row.polynomial := by
  simp [voightRabinExceptionsSeven]

theorem voightRabinExceptionsEight_irreducible :
    ∀ row ∈ voightRabinExceptionsEight,
      Irreducible row.polynomial := by
  have heq : voightRabinExceptionsEight =
      voightMultiPrimeRowsEight.take 10 ++
        [voightSpecialEightRow] ++
        voightMultiPrimeRowsEight.drop 10 := by
    native_decide
  rw [heq]
  apply forall_mem_append
  · apply forall_mem_append
    · intro row hrow
      exact voightMultiPrimeRowsEight_irreducible row
        (List.mem_of_mem_take hrow)
    · intro row hrow
      simp only [List.mem_singleton] at hrow
      subst row
      exact voightSpecialEight_irreducible
  · intro row hrow
    exact voightMultiPrimeRowsEight_irreducible row
      (List.mem_of_mem_drop hrow)

theorem voightRabinExceptionsNine_irreducible :
    ∀ row ∈ voightRabinExceptionsNine,
      Irreducible row.polynomial := by
  have heq : voightRabinExceptionsNine =
      voightMultiPrimeRowsNine := by
    native_decide
  rw [heq]
  exact voightMultiPrimeRowsNine_irreducible

theorem voightRabinExceptionsTen_irreducible :
    ∀ row ∈ voightRabinExceptionsTen,
      Irreducible row.polynomial := by
  have heq : voightRabinExceptionsTen =
      voightMultiPrimeRowsTen := by
    native_decide
  rw [heq]
  exact voightMultiPrimeRowsTen_irreducible

theorem voightPolynomialRowsFive_irreducible :
    ∀ row ∈ voightPolynomialRowsFive,
      Irreducible row.polynomial :=
  irreducible_of_regular_and_exceptions
    voightPolynomialRowsFive_rabin_irreducible
    voightRabinExceptionsFive_irreducible

theorem voightPolynomialRowsSix_irreducible :
    ∀ row ∈ voightPolynomialRowsSix,
      Irreducible row.polynomial :=
  irreducible_of_regular_and_exceptions
    voightPolynomialRowsSix_rabin_irreducible
    voightRabinExceptionsSix_irreducible

theorem voightPolynomialRowsSeven_irreducible :
    ∀ row ∈ voightPolynomialRowsSeven,
      Irreducible row.polynomial :=
  irreducible_of_regular_and_exceptions
    voightPolynomialRowsSeven_rabin_irreducible
    voightRabinExceptionsSeven_irreducible

theorem voightPolynomialRowsEight_irreducible :
    ∀ row ∈ voightPolynomialRowsEight,
      Irreducible row.polynomial :=
  irreducible_of_regular_and_exceptions
    voightPolynomialRowsEight_rabin_irreducible
    voightRabinExceptionsEight_irreducible

theorem voightPolynomialRowsNine_irreducible :
    ∀ row ∈ voightPolynomialRowsNine,
      Irreducible row.polynomial :=
  irreducible_of_regular_and_exceptions
    voightPolynomialRowsNine_rabin_irreducible
    voightRabinExceptionsNine_irreducible

theorem voightPolynomialRowsTen_irreducible :
    ∀ row ∈ voightPolynomialRowsTen,
      Irreducible row.polynomial :=
  irreducible_of_regular_and_exceptions
    voightPolynomialRowsTen_rabin_irreducible
    voightRabinExceptionsTen_irreducible

/-- The combined archive contains exactly `2773` defining polynomials. -/
theorem allVoightPolynomialRows_length :
    allVoightPolynomialRows.length = 2773 := by
  native_decide

set_option maxRecDepth 100000 in
-- The statement combines six generated lists containing 2773 rows.
/-- Every one of the `2773` archived defining polynomials is irreducible over
the integers. -/
theorem allVoightPolynomialRows_irreducible :
    ∀ row ∈ allVoightPolynomialRows,
      Irreducible row.polynomial := by
  dsimp [allVoightPolynomialRows]
  exact forall_mem_append
    voightPolynomialRowsFive_irreducible
    (forall_mem_append
      voightPolynomialRowsSix_irreducible
      (forall_mem_append
        voightPolynomialRowsSeven_irreducible
        (forall_mem_append
          voightPolynomialRowsEight_irreducible
          (forall_mem_append
            voightPolynomialRowsNine_irreducible
            voightPolynomialRowsTen_irreducible))))

end TraceEuclidean
