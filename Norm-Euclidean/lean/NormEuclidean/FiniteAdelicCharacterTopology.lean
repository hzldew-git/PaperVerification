import NormEuclidean.FiniteAdelicCharacter
import Mathlib.Topology.LocallyConstant.Basic

/-! Local constancy of the actual finite adelic trace character. -/

noncomputable section

namespace NormEuclidean.FiniteAdelicCharacterTopology

open NumberField IsDedekindDomain Bong.NumberFieldCompletion
open scoped NumberField Topology WithZero

variable {F : Type*} [Field F] [NumberField F]

/-- The full integral finite adele set is open for the original restricted-product topology. -/
theorem integral_open :
    IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ integerRing v} :=
  RestrictedProduct.isOpen_forall_mem (fun v ↦
    Valued.isOpen_valuationSubring (Γ₀ := ℤᵐ⁰) (v.adicCompletion F))

/-- A single open integral subgroup makes the actual finite adelic character locally constant. -/
theorem locallyConstant :
    IsLocallyConstant (FiniteAdelicCharacter.character (F := F)) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro a
  refine ⟨{b | ∀ v, (b - a) v ∈ integerRing v},
    integral_open.preimage (continuous_id.sub continuous_const), ?_, ?_⟩
  · intro v
    change (a v - a v) ∈ integerRing v
    rw [sub_self]
    exact (integerRing v).zero_mem
  · intro b hb
    have h := FiniteAdelicCharacter.integral_zero (b - a) hb
    rwa [map_sub, sub_eq_zero] at h

/-- Continuity is for the unchanged actual finite adele topology. -/
theorem continuous : Continuous (FiniteAdelicCharacter.character (F := F)) :=
  locallyConstant.continuous

end NormEuclidean.FiniteAdelicCharacterTopology
