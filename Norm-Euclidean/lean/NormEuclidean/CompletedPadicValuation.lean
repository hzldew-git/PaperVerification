import NormEuclidean.CompletedPadicBase
import ValuedFieldTheory.LocalField.DiscreteValuationField.PadicField

/-!
# The original completed valuation extends the actual p-adic valuation

Both integral-ring predicates are clopen. Their equality on the dense
rational subfield therefore gives equality on all of Q_p. This proves
the valuation-extension property for the actual completed valuation,
without requiring equality of the two chosen absolute-value norms.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.CompletedPadicValuation

open Set IsDedekindDomain CompletedPadicBase
open LocalFieldTheory.DiscreteValuationField.Examples
open scoped NumberField WithZero Topology

variable {F : Type*} [Field F] [NumberField F]
attribute [local instance] padicAlgebra

/-- The actual p-adic coefficient map pulls back completed integrality to Z_p. -/
theorem integral_iff (v : HeightOneSpectrum (𝓞 F)) (x : ℚ_[rationalPrime v]) :
    algebraMap ℚ_[rationalPrime v] (v.adicCompletion F) x ∈
        (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).valuationSubring ↔ ‖x‖ ≤ 1 := by
  let S : Set ℚ_[rationalPrime v] :=
    (algebraMap ℚ_[rationalPrime v] (v.adicCompletion F)) ⁻¹'
      ((Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).valuationSubring : Set _)
  let T : Set ℚ_[rationalPrime v] := {x | ‖x‖ ≤ 1}
  have hS : IsClopen S :=
    (Valued.isClopen_valuationSubring (v.adicCompletion F)).preimage
      (algebraMap_continuous v)
  have hT : IsClopen T := by
    refine ⟨isClosed_le continuous_norm continuous_const, ?_⟩
    simpa only [T, Metric.closedBall, dist_eq_norm_sub, sub_zero] using
      IsUltrametricDist.isOpen_closedBall (0 : ℚ_[rationalPrime v]) one_ne_zero
  have hclosed : IsClosed {x | x ∈ S ↔ x ∈ T} := by
    have he : {x | x ∈ S ↔ x ∈ T} = (S ∩ T) ∪ (Sᶜ ∩ Tᶜ) := by
      ext x
      simp only [mem_setOf_eq, mem_union, mem_inter_iff, mem_compl_iff]
      tauto
    rw [he]
    exact ((hS.inter hT).union (hS.compl.inter hT.compl)).isClosed
  refine (Padic.denseRange_ratCast (rationalPrime v)).induction_on
    (p := fun x ↦ x ∈ S ↔ x ∈ T) x hclosed ?_
  intro q
  change algebraMap ℚ_[rationalPrime v] (v.adicCompletion F) (q : ℚ_[rationalPrime v]) ∈
    (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).valuationSubring ↔
      ‖(q : ℚ_[rationalPrime v])‖ ≤ 1
  rw [algebraMap_rat]
  exact ((localField v).ratCast_mem_valuationSubring_iff_padicValuation_le_one q).trans
    (Padic.norm_rat_le_one_iff_padicValuation_le_one (rationalPrime v)).symm

/-- The chosen DVR valuation on Q_p has precisely the usual integral unit ball. -/
theorem base_integral_iff (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) :
    x ∈ (Qp.padicDVRValuation p).valuationSubring ↔ ‖x‖ ≤ 1 := by
  let e := Qp.padicIntEquivValuationSubring p
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := e.surjective ⟨x, hx⟩
    have hc : (z : ℚ_[p]) = x := by
      exact congrArg (fun a : (Qp.padicDVRValuation p).valuationSubring ↦ (a : ℚ_[p])) hz
    exact hc ▸ z.property
  · intro hx
    have hz := (e ⟨x, hx⟩).property
    exact hz

/-- The original completed valuation is an actual extension of the p-adic DVR valuation. -/
theorem hasExtension (v : HeightOneSpectrum (𝓞 F)) :
    (Qp.padicDVRValuation (rationalPrime v)).HasExtension
      (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) := by
  apply Valuation.HasExtension.ofComapInteger
  ext x
  change (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)
      (algebraMap ℚ_[rationalPrime v] (v.adicCompletion F) x) ≤ 1 ↔
    Qp.padicDVRValuation (rationalPrime v) x ≤ 1
  exact (integral_iff v x).trans (base_integral_iff (rationalPrime v) x).symm

end NormEuclidean.CompletedPadicValuation
