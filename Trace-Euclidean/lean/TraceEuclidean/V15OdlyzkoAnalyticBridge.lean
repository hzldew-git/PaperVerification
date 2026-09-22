import TraceEuclidean.V15OdlyzkoBridge
import TraceEuclidean.V15OdlyzkoPrimeCorrection

/-!
# Explicit Odlyzko correction to the Table 4 interface

This file replaces the existential nonnegative correction in the literature
interface by the complete prime-ideal correction formalized in
`V15OdlyzkoPrimeCorrection`.  The remaining premise is precisely the analytic
discriminant inequality with that explicit correction.
-/

namespace TraceEuclidean

noncomputable section

/-- The exact-error `b = 4` Table 4 inequality with the source's complete
prime-ideal correction substituted for the existential correction term. -/
def V15OdlyzkoTable4ExplicitCorrectionInput : Prop :=
  ∀ K : CodedNumberField,
    (36347 / 1000 : ℝ) ^ NumberField.InfinitePlace.nrRealPlaces K.1 *
          (16593 / 1000 : ℝ) ^
            (2 * NumberField.InfinitePlace.nrComplexPlaces K.1) *
          Real.exp (v15OdlyzkoPrimeCorrection K.1 - (32 / 3 : ℝ)) <
      ((|K.discriminant| : ℤ) : ℝ)

/-- The explicit analytic inequality supplies the exact-error literature
interface, with correction nonnegativity discharged internally. -/
theorem v15_odlyzkoTable4ExactErrorInput_of_explicitCorrection
    (hExplicit : V15OdlyzkoTable4ExplicitCorrectionInput) :
    V15OdlyzkoTable4ExactErrorInput := by
  refine ⟨fun K ↦ v15OdlyzkoPrimeCorrection K.1, ?_, hExplicit⟩
  intro K
  exact v15OdlyzkoPrimeCorrection_nonneg K.1

/-- The explicit analytic inequality implies the published rounded Table 4
description used by all downstream v15 finiteness theorems. -/
theorem v15_odlyzkoTable4DescriptionInput_of_explicitCorrection
    (hExplicit : V15OdlyzkoTable4ExplicitCorrectionInput) :
    V15OdlyzkoTable4DescriptionInput :=
  v15_odlyzkoTable4DescriptionInput_of_exactError
    (v15_odlyzkoTable4ExactErrorInput_of_explicitCorrection hExplicit)

end

end TraceEuclidean
