import TraceEuclidean.V15VoightIrreducibilityCertificates
import TraceEuclidean.V15VoightSpecialIrreducibility

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
theorem v15_irreducible_of_regular_and_exceptions
    {rows exceptions : List V15VoightPolynomialRow}
    (hregular : ∀ row ∈ rows.filter
      (fun row => decide (row ∉ exceptions)), Irreducible row.polynomial)
    (hexceptions : ∀ row ∈ exceptions, Irreducible row.polynomial) :
    ∀ row ∈ rows, Irreducible row.polynomial := by
  intro row hrow
  by_cases hexception : row ∈ exceptions
  · exact hexceptions row hexception
  · apply hregular row
    exact List.mem_filter.mpr ⟨hrow, by simp [hexception]⟩

theorem v15_voightRabinExceptionsFive_irreducible :
    ∀ row ∈ v15VoightRabinExceptionsFive,
      Irreducible row.polynomial := by
  simp [v15VoightRabinExceptionsFive]

theorem v15_voightRabinExceptionsSix_irreducible :
    ∀ row ∈ v15VoightRabinExceptionsSix,
      Irreducible row.polynomial := by
  have heq : v15VoightRabinExceptionsSix =
      v15VoightMultiPrimeRowsSix := by
    native_decide
  rw [heq]
  exact v15_voightMultiPrimeRowsSix_irreducible

theorem v15_voightRabinExceptionsSeven_irreducible :
    ∀ row ∈ v15VoightRabinExceptionsSeven,
      Irreducible row.polynomial := by
  simp [v15VoightRabinExceptionsSeven]

theorem v15_voightRabinExceptionsEight_irreducible :
    ∀ row ∈ v15VoightRabinExceptionsEight,
      Irreducible row.polynomial := by
  have heq : v15VoightRabinExceptionsEight =
      v15VoightMultiPrimeRowsEight.take 10 ++
        [v15VoightSpecialEightRow] ++
        v15VoightMultiPrimeRowsEight.drop 10 := by
    native_decide
  rw [heq]
  apply v15_forall_mem_append
  · apply v15_forall_mem_append
    · intro row hrow
      exact v15_voightMultiPrimeRowsEight_irreducible row
        (List.mem_of_mem_take hrow)
    · intro row hrow
      simp only [List.mem_singleton] at hrow
      subst row
      exact v15_voightSpecialEight_irreducible
  · intro row hrow
    exact v15_voightMultiPrimeRowsEight_irreducible row
      (List.mem_of_mem_drop hrow)

theorem v15_voightRabinExceptionsNine_irreducible :
    ∀ row ∈ v15VoightRabinExceptionsNine,
      Irreducible row.polynomial := by
  have heq : v15VoightRabinExceptionsNine =
      v15VoightMultiPrimeRowsNine := by
    native_decide
  rw [heq]
  exact v15_voightMultiPrimeRowsNine_irreducible

theorem v15_voightRabinExceptionsTen_irreducible :
    ∀ row ∈ v15VoightRabinExceptionsTen,
      Irreducible row.polynomial := by
  have heq : v15VoightRabinExceptionsTen =
      v15VoightMultiPrimeRowsTen := by
    native_decide
  rw [heq]
  exact v15_voightMultiPrimeRowsTen_irreducible

theorem v15_voightPolynomialRowsFive_irreducible :
    ∀ row ∈ v15VoightPolynomialRowsFive,
      Irreducible row.polynomial :=
  v15_irreducible_of_regular_and_exceptions
    v15_voightPolynomialRowsFive_rabin_irreducible
    v15_voightRabinExceptionsFive_irreducible

theorem v15_voightPolynomialRowsSix_irreducible :
    ∀ row ∈ v15VoightPolynomialRowsSix,
      Irreducible row.polynomial :=
  v15_irreducible_of_regular_and_exceptions
    v15_voightPolynomialRowsSix_rabin_irreducible
    v15_voightRabinExceptionsSix_irreducible

theorem v15_voightPolynomialRowsSeven_irreducible :
    ∀ row ∈ v15VoightPolynomialRowsSeven,
      Irreducible row.polynomial :=
  v15_irreducible_of_regular_and_exceptions
    v15_voightPolynomialRowsSeven_rabin_irreducible
    v15_voightRabinExceptionsSeven_irreducible

theorem v15_voightPolynomialRowsEight_irreducible :
    ∀ row ∈ v15VoightPolynomialRowsEight,
      Irreducible row.polynomial :=
  v15_irreducible_of_regular_and_exceptions
    v15_voightPolynomialRowsEight_rabin_irreducible
    v15_voightRabinExceptionsEight_irreducible

theorem v15_voightPolynomialRowsNine_irreducible :
    ∀ row ∈ v15VoightPolynomialRowsNine,
      Irreducible row.polynomial :=
  v15_irreducible_of_regular_and_exceptions
    v15_voightPolynomialRowsNine_rabin_irreducible
    v15_voightRabinExceptionsNine_irreducible

theorem v15_voightPolynomialRowsTen_irreducible :
    ∀ row ∈ v15VoightPolynomialRowsTen,
      Irreducible row.polynomial :=
  v15_irreducible_of_regular_and_exceptions
    v15_voightPolynomialRowsTen_rabin_irreducible
    v15_voightRabinExceptionsTen_irreducible

/-- The complete list of archived defining-polynomial rows used in the
degree `5` through `10` verification. -/
def v15AllVoightPolynomialRows : List V15VoightPolynomialRow :=
  v15VoightPolynomialRowsFive ++
    (v15VoightPolynomialRowsSix ++
      (v15VoightPolynomialRowsSeven ++
        (v15VoightPolynomialRowsEight ++
          (v15VoightPolynomialRowsNine ++
            v15VoightPolynomialRowsTen))))

/-- The combined archive contains exactly `2773` defining polynomials. -/
theorem v15_allVoightPolynomialRows_length :
    v15AllVoightPolynomialRows.length = 2773 := by
  native_decide

set_option maxRecDepth 100000 in
-- The statement combines six generated lists containing 2773 rows.
/-- Every one of the `2773` archived defining polynomials is irreducible over
the integers. -/
theorem v15_allVoightPolynomialRows_irreducible :
    ∀ row ∈ v15AllVoightPolynomialRows,
      Irreducible row.polynomial := by
  dsimp [v15AllVoightPolynomialRows]
  exact v15_forall_mem_append
    v15_voightPolynomialRowsFive_irreducible
    (v15_forall_mem_append
      v15_voightPolynomialRowsSix_irreducible
      (v15_forall_mem_append
        v15_voightPolynomialRowsSeven_irreducible
        (v15_forall_mem_append
          v15_voightPolynomialRowsEight_irreducible
          (v15_forall_mem_append
            v15_voightPolynomialRowsNine_irreducible
            v15_voightPolynomialRowsTen_irreducible))))

end TraceEuclidean
