import NormEuclidean.ChapterX.QuadraticPlaceCounts
import NormEuclidean.ChapterX.SUnitRanks
import NormEuclidean.ChapterX.SNormIndex

/-!
# The S-unit rank defect and the actual nonsplit count

Flattening the actual finite and infinite place fibers identifies the
excluded extension places. Each split base place contributes two places
and each nonsplit place one. Together with Dirichlet this gives the rank
identity used in the numerical part of O'Meara 65:10.
-/

noncomputable section

namespace NormEuclidean.SUnitRankDefect

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm NormIndexProduct
open SUnitNormArithmetic
open scoped NumberField NormEuclidean.NormIndexProduct

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- The actual fiber of places above each excluded finite or infinite place. -/
abbrev Fiber (theta : Kˣ) (htheta : ¬ IsSquare theta)
    {S : Set (HeightOneSpectrum (𝓞 K))} : Index S → Type u :=
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  fun q ↦ match q with
  | .inl p => FinitePlacesAbove (E := QuadraticAlgebra K theta.val 0) p.1
  | .inr v => InfinitePlacesAbove (E := QuadraticAlgebra K theta.val 0) v

scoped instance fiberFintype (theta : Kˣ) (htheta : ¬ IsSquare theta)
    {S : Set (HeightOneSpectrum (𝓞 K))} (q : Index S) : Fintype (Fiber theta htheta q) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  cases q <;> dsimp only [Fiber] <;> infer_instance

open scoped NormEuclidean.SUnitRankDefect

/-- The counted extension places are exactly the flattened actual fibers. -/
def flattenEquiv (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    (Σ q : Index S, Fiber theta htheta q) ≃
      Index (finitePlacesOverSet (E := QuadraticAlgebra K theta.val 0) S) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  exact
    { toFun := fun ⟨q, w⟩ ↦ match q, w with
        | .inl p, w => .inl ⟨w.1, by change w.1.under (𝓞 K) ∉ S; rw [w.2]; exact p.2⟩
        | .inr _, w => .inr w.1
      invFun := fun q ↦ match q with
        | .inl w => ⟨.inl ⟨w.1.under (𝓞 K), w.2⟩, ⟨w.1, rfl⟩⟩
        | .inr w => ⟨.inr (w.comap (algebraMap K _)), ⟨w, rfl⟩⟩
      left_inv := by
        rintro ⟨q, w⟩
        cases q with
        | inl p =>
            rcases p with ⟨p, hp⟩
            rcases w with ⟨w, hw⟩
            change w.under (𝓞 K) = p at hw
            subst p
            rfl
        | inr v =>
            rcases w with ⟨w, hw⟩
            subst v
            rfl
      right_inv := by intro q; cases q <;> rfl }

/-- The actual number of places in each local fiber. -/
theorem fiber_card (theta : Kˣ) (htheta : ¬ IsSquare theta)
    {S : Set (HeightOneSpectrum (𝓞 K))} (q : Index S) :
    Nat.card (Fiber theta htheta q) = (by
      classical
      exact if IsSquare (SNormIndex.localParameter theta q) then 2 else 1) := by
  cases q with
  | inl p => exact QuadraticPlaceCounts.finite_card theta htheta p.1
  | inr v => exact QuadraticPlaceCounts.infinite_card theta htheta v

/-- Counting actual extension places gives the split/nonsplit defect. -/
theorem excluded_place_count (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    Nat.card (Index (finitePlacesOverSet (E := QuadraticAlgebra K theta.val 0) S)) +
      SNormIndex.nonsplitCount theta S hS = 2 * Nat.card (Index S) := by
  classical
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  letI : Fintype ↥(Sᶜ) := hS.fintype
  rw [← Nat.card_congr (flattenEquiv theta htheta S), Nat.card_sigma]
  have hsum :
      ∑ q : Index S, (Nat.card (Fiber theta htheta q) +
        if IsSquare (SNormIndex.localParameter theta q) then 0 else 1) =
          ∑ _q : Index S, (2 : ℕ) := by
    apply Finset.sum_congr rfl
    intro q _
    rw [fiber_card]
    split_ifs <;> rfl
  simpa [Finset.sum_add_distrib, Finset.sum_ite, Nat.card_eq_fintype_card,
    SNormIndex.nonsplitCount, mul_comm] using hsum

/-- The exact rank relation before the final Herbrand index calculation.
It does not by itself assert positivity of b. -/
theorem rank_defect (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    Module.finrank ℤ (Additive (sUnitSubgroup
        (finitePlacesOverSet (E := QuadraticAlgebra K theta.val 0) S))) +
      SNormIndex.nonsplitCount theta S hS =
        2 * Module.finrank ℤ (Additive (sUnitSubgroup S)) + 1 := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  have hcof : (finitePlacesOverSet (E := QuadraticAlgebra K theta.val 0) S)ᶜ.Finite :=
    NormFiberAssembly.finite_preimage_under Sᶜ hS
  have hc := excluded_place_count theta htheta S hS
  letI : Finite ↥(Sᶜ) := hS.to_subtype
  letI : Finite ↥((finitePlacesOverSet (E := QuadraticAlgebra K theta.val 0) S)ᶜ) :=
    hcof.to_subtype
  change Nat.card (↥((finitePlacesOverSet (E := QuadraticAlgebra K theta.val 0) S)ᶜ) ⊕
      NumberField.InfinitePlace (QuadraticAlgebra K theta.val 0)) + _ =
    2 * Nat.card (↥(Sᶜ) ⊕ NumberField.InfinitePlace K) at hc
  rw [Nat.card_sum, Nat.card_sum] at hc
  rw [SUnitRanks.finrank_sUnits _ hcof, SUnitRanks.finrank_sUnits S hS]
  have hK : 0 < Nat.card (NumberField.InfinitePlace K) := Nat.card_pos
  have hE : 0 < Nat.card (NumberField.InfinitePlace (QuadraticAlgebra K theta.val 0)) :=
    Nat.card_pos
  simp only [NumberField.Units.rank, ← Nat.card_eq_fintype_card]
  omega

end NormEuclidean.SUnitRankDefect
