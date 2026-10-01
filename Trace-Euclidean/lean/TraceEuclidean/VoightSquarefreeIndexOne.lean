import TraceEuclidean.VoightSquarefreeIndexOneCore
import TraceEuclidean.VoightOrderIndexBridge
import Mathlib.Data.Nat.Squarefree

/-!
# Exact field discriminants for squarefree index-one Voight rows

If the checked polynomial discriminant is squarefree, no nontrivial square
can occur as the index factor between the power order and the full ring of
integers.  This closes the recorded field discriminant for every archived row
whose recorded index is one and whose recorded discriminant is squarefree.
-/

namespace TraceEuclidean

noncomputable section

open NumberField Polynomial
open scoped Matrix NumberField

/-- Executable selector for the archived rows closed by the squarefree
index-one argument. -/
def VoightPolynomialRow.squarefreeIndexOne
    (row : VoightPolynomialRow) : Bool :=
  row.index == 1 && decide (Squarefree row.fieldDiscriminant)

/-- The selector states exactly index one and squarefreeness. -/
theorem voightPolynomialRow_squarefreeIndexOne_iff
    (row : VoightPolynomialRow) :
    row.squarefreeIndexOne = true ↔
      row.index = 1 ∧ Squarefree row.fieldDiscriminant := by
  simp [VoightPolynomialRow.squarefreeIndexOne]

/-- The archived rows whose actual field discriminants follow immediately
from the squarefree index-one criterion. -/
def voightSquarefreeIndexOneRows : List VoightPolynomialRow :=
  allVoightPolynomialRows.filter
    VoightPolynomialRow.squarefreeIndexOne

/-- Exactly 1,108 archived rows satisfy the squarefree index-one criterion. -/
theorem voightSquarefreeIndexOneRows_length :
    voightSquarefreeIndexOneRows.length = 1108 := by
  native_decide

/-- Every row selected by the squarefree index-one certificate presents an
actual totally real number field with the recorded field discriminant. -/
theorem voightSquarefreeIndexOneRows_present_exactTotallyRealNumberField :
    ∀ row ∈ voightSquarefreeIndexOneRows,
      row.PresentsExactTotallyRealNumberField := by
  intro row hrow
  have hfiltered := List.mem_filter.mp hrow
  have hcondition :=
    (voightPolynomialRow_squarefreeIndexOne_iff row).mp hfiltered.2
  have hdata :=
    allVoightPolynomialRows_recordedIndexData row hfiltered.1
  exact
    (allVoightPolynomialRows_present_indexedTotallyRealNumberField
      row hfiltered.1).exact_of_index_one_squarefree row
        hcondition.1 hcondition.2 hdata.2.2

end

end TraceEuclidean
