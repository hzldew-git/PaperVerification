import NormEuclidean.ChapterX.SUnitSquareArithmetic

/-!
# O'Meara 65:10: the exact S-unit norm index

The rank defect, actual S-unit Hilbert 90 and square-index calculation
prove both the precise norm index and positivity of the nonsplit count.
Neither conclusion is assumed as an arithmetic premise.
-/

noncomputable section

namespace NormEuclidean.SUnitExactIndex

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm SUnitNormArithmetic
open SUnitNormFiniteness SUnitFixedPart SUnitSquareArithmetic
open scoped NumberField

/-- Cancellation of the square-index balance also forces a nonsplit place. -/
theorem numeric_index (d rA rT b : ℕ)
    (hbalance : d * 2 ^ (rT + 1) = 2 ^ (rA + 1))
    (hrank : rT + b = rA + 1) : 0 < b ∧ d = 2 ^ (b - 1) := by
  have hd : 0 < d := by
    by_contra h
    have hz : d = 0 := by omega
    rw [hz, zero_mul] at hbalance
    exact (pow_ne_zero (rA + 1) (by decide : (2 : ℕ) ≠ 0)) hbalance.symm
  have hle : 2 ^ (rT + 1) ≤ 2 ^ (rA + 1) := by
    calc
      _ ≤ d * 2 ^ (rT + 1) := Nat.le_mul_of_pos_left _ hd
      _ = _ := hbalance
  have he : rT + 1 ≤ rA + 1 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hle
  have hb : 0 < b := by omega
  refine ⟨hb, ?_⟩
  have hr : rA + 1 = (b - 1) + (rT + 1) := by omega
  have hp : (2 : ℕ) ^ (rA + 1) = 2 ^ (b - 1) * 2 ^ (rT + 1) := by
    rw [hr, pow_add]
  exact Nat.mul_right_cancel (by positivity : 0 < (2 : ℕ) ^ (rT + 1))
    (hbalance.trans hp)

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- The actual S-unit norm index is exactly the required power of two,
and its exponent uses a strictly positive actual nonsplit-place count. -/
theorem norm_index (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite)
    (htwo : ∀ p ∈ S, (2 : 𝓞 K) ∉ p.asIdeal)
    (hunit : ∀ p ∈ S, p.valuation K theta.val = 1)
    (hprincipal : idelePrincipalEmbedding.range ⊔ finitePlaceSIdeleSubgroup S = ⊤) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    0 < SNormIndex.nonsplitCount theta S hS ∧
      (normSUnits theta htheta S).range.index =
        2 ^ (SNormIndex.nonsplitCount theta S hS - 1) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  let E := QuadraticAlgebra K theta.val 0
  let A := sUnitSubgroup S
  let G := sUnitSubgroup (finitePlacesOverSet (E := E) S)
  let f := baseEmbedding theta htheta S
  let N := normSUnits theta htheta S
  let T := differenceEnd (QuadraticStableKernel.conjugation theta.val) S
  letI : Module.Finite ℤ (Additive A) := SUnitFiniteness.moduleFinite_sUnits S hS
  have hcof : (finitePlacesOverSet (E := E) S)ᶜ.Finite :=
    NormFiberAssembly.finite_preimage_under Sᶜ hS
  letI : Module.Finite ℤ (Additive G) := SUnitFiniteness.moduleFinite_sUnits _ hcof
  letI : Group.FG A := GroupFG.iff_add_fg.mpr
    (Module.Finite.iff_addGroup_fg.mp inferInstance)
  letI : Group.FG G := GroupFG.iff_add_fg.mpr
    (Module.Finite.iff_addGroup_fg.mp inferInstance)
  have hker : T.range = N.ker := by
    rw [show T.range = (normEnd (QuadraticStableKernel.conjugation theta.val) S).ker from
      SUnitHilbert90Exact.difference_range_eq_norm_kernel theta htheta S
        htwo hunit hprincipal]
    ext x
    change normEnd (QuadraticStableKernel.conjugation theta.val) S x = 1 ↔ N x = 1
    rw [normEnd_eq_comp]
    change f (N x) = 1 ↔ N x = 1
    constructor
    · intro h
      exact baseEmbedding_injective theta htheta S (h.trans (map_one f).symm)
    · intro h
      rw [h, map_one]
  have hbase (a : A) : N (f a) = a ^ 2 := by
    apply Subtype.ext
    apply Units.ext
    change Algebra.norm K (algebraMap K E a.val.val) = _
    rw [algebra_norm_eq_quadraticAlgebra_norm, QuadraticAlgebra.norm_algebraMap]
    rfl
  have hbalance := NormSquareBalance.square_balance f N T
    (base_range_eq_difference_kernel theta htheta S) hker hbase
    (difference_twice theta htheta S)
  let nA : A := ⟨-1, fun p _ ↦ by simp⟩
  have hA := FieldSquareIndex.square_index A.subtype A.subtype_injective nA rfl
  let j : T.range →* Eˣ := G.subtype.comp T.range.subtype
  have hj : Function.Injective j := G.subtype_injective.comp T.range.subtype_injective
  let nT : T.range := ⟨⟨-1, fun w _ ↦ by simp⟩,
    minus_one_mem_difference theta htheta S htwo hunit hprincipal⟩
  have hT := FieldSquareIndex.square_index j hj nT rfl
  rw [hA, hT] at hbalance
  have hR := difference_rank theta htheta S hS
  have hD := SUnitRankDefect.rank_defect theta htheta S hS
  change Module.finrank ℤ (Additive T.range) + Module.finrank ℤ (Additive A) =
    Module.finrank ℤ (Additive G) at hR
  change Module.finrank ℤ (Additive G) + SNormIndex.nonsplitCount theta S hS =
    2 * Module.finrank ℤ (Additive A) + 1 at hD
  apply numeric_index _ _ _ _ hbalance
  omega

end NormEuclidean.SUnitExactIndex
