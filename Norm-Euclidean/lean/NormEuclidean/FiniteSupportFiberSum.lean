import Mathlib.Algebra.BigOperators.Finprod

/-! Finite-support sums may be grouped into genuinely finite fibers. -/

noncomputable section

namespace NormEuclidean.FiniteSupportFiberSum

open scoped Classical

variable {I : Type*} {J : I → Type*} [∀ i, Fintype (J i)]
variable {M : Type*} [AddCommMonoid M]

/-- Grouping a finitely supported sum into finite fibers preserves the actual sum. -/
theorem sigma_sum (f : (Σ i, J i) → M) (hf : Function.HasFiniteSupport f) :
    ∑ᶠ z : (Σ i, J i), f z = ∑ᶠ i : I, ∑ j : J i, f ⟨i, j⟩ := by
  let S : Finset I := hf.toFinset.image Sigma.fst
  have hs : Function.support f ⊆
      (S.sigma (fun i ↦ (Finset.univ : Finset (J i))) : Set (Σ i, J i)) := by
    intro z hz
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_image.mpr ⟨z, hf.mem_toFinset.mpr hz, rfl⟩, Finset.mem_univ _⟩
  have ho : Function.support (fun i ↦ ∑ j : J i, f ⟨i, j⟩) ⊆ (S : Set I) := by
    intro i hi
    by_contra hn
    apply hi
    apply Finset.sum_eq_zero
    intro j _
    by_contra hj
    have h := hs hj
    exact hn (Finset.mem_sigma.mp h).1
  rw [finsum_eq_sum_of_support_subset f hs,
    finsum_eq_sum_of_support_subset (fun i ↦ ∑ j : J i, f ⟨i, j⟩) ho,
    Finset.sum_sigma]

end NormEuclidean.FiniteSupportFiberSum
