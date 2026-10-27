import NormEuclidean.ChapterX.NormDifferenceCore

/-!
# The actual fixed S-units and the numerical Herbrand comparison

Fixed extension S-units descend to base S-units. The norm endomorphism is
the actual field norm followed by this embedding. Its relative index in
the fixed part is therefore the actual S-unit norm index. S-unit Hilbert 90
removes the second global index from Herbrand's equality.
-/

noncomputable section

namespace NormEuclidean.SUnitFixedPart

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm SUnitNormArithmetic
open SUnitNormFiniteness NormDifferenceCore
open scoped NumberField

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- The actual base S-units embed in the extension S-units. -/
def baseEmbedding (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    sUnitSubgroup S →*
      sUnitSubgroup (finitePlacesOverSet (E := QuadraticAlgebra K theta.val 0) S) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  exact
    { toFun := fun x ↦ ⟨Units.map (algebraMap K _).toMonoidHom x.val,
        base_embedding_mem S x.val x.property⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' x y := Subtype.ext (map_mul _ x.val y.val) }

/-- The base S-unit embedding is injective. -/
theorem baseEmbedding_injective (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    Function.Injective (baseEmbedding theta htheta S) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  intro x y h
  apply Subtype.ext
  apply Units.ext
  apply FaithfulSMul.algebraMap_injective K (QuadraticAlgebra K theta.val 0)
  exact congrArg (fun z ↦ z.val.val) h

/-- Every fixed extension S-unit is the image of an actual base S-unit. -/
theorem base_range_eq_difference_kernel (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    (baseEmbedding theta htheta S).range =
      (differenceEnd (QuadraticStableKernel.conjugation theta.val) S).ker := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    apply Units.ext
    change (((baseEmbedding theta htheta S) y).val /
      Units.map (QuadraticStableKernel.conjugation theta.val).toMonoidHom
        ((baseEmbedding theta htheta S) y).val).val = 1
    rw [Units.val_div_eq_div_val]
    change (algebraMap K (QuadraticAlgebra K theta.val 0) y.val.val) /
      (QuadraticStableKernel.conjugation theta.val)
        (algebraMap K (QuadraticAlgebra K theta.val 0) y.val.val) = 1
    rw [(QuadraticStableKernel.conjugation theta.val).commutes]
    exact div_self ((map_ne_zero (algebraMap K (QuadraticAlgebra K theta.val 0))).mpr
      y.val.ne_zero)
  · intro hx
    have h := congrArg (fun z ↦ z.val) (show differenceEnd
      (QuadraticStableKernel.conjugation theta.val) S x = 1 from hx)
    change x.val /
      Units.map (QuadraticStableKernel.conjugation theta.val).toMonoidHom x.val = 1 at h
    have he : x.val.val = star x.val.val := congrArg Units.val (div_eq_one.mp h)
    have hi : x.val.val.im = 0 := by
      have h' := congrArg QuadraticAlgebra.im he
      simp only [QuadraticAlgebra.im_star] at h'
      have h2 : (2 : K) * x.val.val.im = 0 := by linear_combination h'
      exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
    have hr : x.val.val = algebraMap K (QuadraticAlgebra K theta.val 0) x.val.val.re := by
      ext <;> simp [hi]
    have ha0 : x.val.val.re ≠ 0 := by
      intro hzero
      exact x.val.ne_zero (by rw [hr, hzero, map_zero])
    let a := Units.mk0 x.val.val.re ha0
    have ha : a ∈ sUnitSubgroup S := by
      intro p hp
      have hn := global_norm_mem theta htheta S x p hp
      change p.valuation K (Algebra.norm K x.val.val) = 1 at hn
      rw [hr, algebra_norm_eq_quadraticAlgebra_norm, QuadraticAlgebra.norm_algebraMap,
        map_pow] at hn
      exact (pow_eq_one_iff_of_nonneg bot_le (by decide : 2 ≠ 0)).mp hn
    exact ⟨⟨a, ha⟩, Subtype.ext (Units.ext hr.symm)⟩

/-- The norm endomorphism is the actual S-unit norm followed by base embedding. -/
theorem normEnd_eq_comp (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    normEnd (QuadraticStableKernel.conjugation theta.val) S =
      (baseEmbedding theta htheta S).comp (normSUnits theta htheta S) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  apply Units.ext
  exact normEnd_actual theta htheta S x

/-- The norm-image index in the fixed part is the actual base S-unit norm index. -/
theorem norm_index_eq (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    (normEnd (QuadraticStableKernel.conjugation theta.val) S).range.relIndex
      (differenceEnd (QuadraticStableKernel.conjugation theta.val) S).ker =
        (normSUnits theta htheta S).range.index := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  let f := baseEmbedding theta htheta S
  have hpre : (normEnd (QuadraticStableKernel.conjugation theta.val) S).range.comap f =
      (normSUnits theta htheta S).range := by
    rw [normEnd_eq_comp, ← MonoidHom.map_range, Subgroup.comap_map_eq,
      MonoidHom.ker_eq_bot f (baseEmbedding_injective theta htheta S), sup_bot_eq]
  have h := Subgroup.index_comap
    (normEnd (QuadraticStableKernel.conjugation theta.val) S).range f
  rw [hpre, base_range_eq_difference_kernel] at h
  exact h.symm

/-- Herbrand's comparison for the actual S-unit norm, with the finite core,
both side finiteness conditions and S-unit Hilbert 90 discharged. The two
indices on the core remain actual indices, not asserted powers of two. -/
theorem actual_norm_index_balance (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite)
    (htwo : ∀ p ∈ S, (2 : 𝓞 K) ∉ p.asIdeal)
    (hunit : ∀ p ∈ S, p.valuation K theta.val = 1)
    (hprincipal : idelePrincipalEmbedding.range ⊔ finitePlaceSIdeleSubgroup S = ⊤) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    let N := normEnd (QuadraticStableKernel.conjugation theta.val) S
    let T := differenceEnd (QuadraticStableKernel.conjugation theta.val) S
    let P := imageCore N T
    (normSUnits theta htheta S).range.index * (P.map T).relIndex (P ⊓ N.ker) =
      (P.map N).relIndex (P ⊓ T.ker) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  have h := (actual_sUnit_herbrand theta htheta S hS).1
  rw [norm_index_eq, SUnitHilbert90Exact.difference_range_eq_norm_kernel theta htheta S
    htwo hunit hprincipal, Subgroup.relIndex_self, one_mul] at h
  exact h

end NormEuclidean.SUnitFixedPart
