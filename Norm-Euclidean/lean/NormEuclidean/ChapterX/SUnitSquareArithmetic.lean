import NormEuclidean.ChapterX.NormSquareBalance
import NormEuclidean.ChapterX.SUnitFixedPart
import NormEuclidean.ChapterX.SUnitRankDefect

/-!
# Actual S-unit square indices and rank-nullity

This supplies the numerical inputs to the norm-square balance. The minus-one
element of the difference image comes from the proved S-unit Hilbert 90
construction, including its exceptional branch.
-/

noncomputable section

namespace NormEuclidean.SUnitSquareArithmetic

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm SUnitNormArithmetic
open SUnitNormFiniteness SUnitFixedPart
open scoped NumberField

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- Rank-nullity for the actual difference map, with its fixed kernel identified. -/
theorem difference_rank (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    Module.finrank ℤ (Additive
        (differenceEnd (QuadraticStableKernel.conjugation theta.val) S).range) +
      Module.finrank ℤ (Additive (sUnitSubgroup S)) =
        Module.finrank ℤ (Additive (sUnitSubgroup
          (finitePlacesOverSet (E := QuadraticAlgebra K theta.val 0) S))) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  let G := sUnitSubgroup (finitePlacesOverSet (E := QuadraticAlgebra K theta.val 0) S)
  let T := differenceEnd (QuadraticStableKernel.conjugation theta.val) S
  let f := (MonoidHom.toAdditive T).toIntLinearMap
  let l := (MonoidHom.toAdditive (baseEmbedding theta htheta S)).toIntLinearMap
  have hcof : (finitePlacesOverSet (E := QuadraticAlgebra K theta.val 0) S)ᶜ.Finite :=
    NormFiberAssembly.finite_preimage_under Sᶜ hS
  letI : Module.Finite ℤ (Additive G) := SUnitFiniteness.moduleFinite_sUnits _ hcof
  have hk : f.ker = l.range := by
    ext x
    exact (show x.toMul ∈ T.ker ↔ x.toMul ∈ (baseEmbedding theta htheta S).range from
      (base_range_eq_difference_kernel theta htheta S ▸ Iff.rfl))
  have hl : Function.Injective l := by
    intro x y h
    apply Additive.toMul.injective
    exact baseEmbedding_injective theta htheta S (congrArg Additive.toMul h)
  let er : f.range ≃+ Additive T.range :=
    { toFun := fun x ↦ Additive.ofMul ⟨x.val.toMul, x.property⟩
      invFun := fun x ↦ ⟨Additive.ofMul x.toMul.val, x.toMul.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  have h := f.ker.finrank_quotient_add_finrank
  rw [f.quotKerEquivRange.finrank_eq, er.toIntLinearEquiv.finrank_eq, hk,
    LinearMap.finrank_range_of_inj hl] at h
  exact h

/-- The actual difference satisfies the square identity on its own image. -/
theorem difference_twice (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    ∀ x, differenceEnd (QuadraticStableKernel.conjugation theta.val) S
        (differenceEnd (QuadraticStableKernel.conjugation theta.val) S x) =
      differenceEnd (QuadraticStableKernel.conjugation theta.val) S x ^ 2 := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  intro x
  change (x / conjugationEnd _ S x) /
    conjugationEnd _ S (x / conjugationEnd _ S x) = (x / conjugationEnd _ S x) ^ 2
  rw [map_div, conjugationEnd_involutive _ (fun x ↦ star_star x) S]
  simp [pow_two, div_eq_mul_inv, mul_comm, mul_left_comm]

/-- Minus one belongs to the actual S-unit difference image. -/
theorem minus_one_mem_difference (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K)))
    (htwo : ∀ p ∈ S, (2 : 𝓞 K) ∉ p.asIdeal)
    (hunit : ∀ p ∈ S, p.valuation K theta.val = 1)
    (hprincipal : idelePrincipalEmbedding.range ⊔ finitePlaceSIdeleSubgroup S = ⊤) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    (⟨-1, fun w _ ↦ by simp⟩ : sUnitSubgroup
      (finitePlacesOverSet (E := QuadraticAlgebra K theta.val 0) S)) ∈
        (differenceEnd (QuadraticStableKernel.conjugation theta.val) S).range := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  let H : sUnitSubgroup (finitePlacesOverSet (E := QuadraticAlgebra K theta.val 0) S) :=
    ⟨-1, fun w _ ↦ by simp⟩
  have hn : Algebra.norm K H.val.val = 1 := by
    change Algebra.norm K (-1 : QuadraticAlgebra K theta.val 0) = 1
    rw [show (-1 : QuadraticAlgebra K theta.val 0) =
      algebraMap K (QuadraticAlgebra K theta.val 0) (-1 : K) by simp]
    rw [algebra_norm_eq_quadraticAlgebra_norm, QuadraticAlgebra.norm_algebraMap]
    norm_num
  obtain ⟨z, hz⟩ := SUnitHilbert90Exact.exists_sUnit_preimage theta htheta S
    htwo hunit hprincipal H hn
  exact ⟨z, Subtype.ext hz⟩

end NormEuclidean.SUnitSquareArithmetic
