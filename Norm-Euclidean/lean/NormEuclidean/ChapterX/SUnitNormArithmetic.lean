import NormEuclidean.ChapterX.CompletedFiberAutomorphism
import NormEuclidean.ChapterX.QuadraticExtensionNorm
import NormEuclidean.ChapterX.QuadraticStableKernel
import NormEuclidean.ChapterX.QuadraticPrincipalNorm

/-!
# Actual S-unit endomorphisms in O'Meara 65:10

Conjugation preserves S-unit support above the base primes. Its norm and
difference endomorphisms satisfy the identities required by Herbrand. The
quadratic Hilbert 90 preimage is constructed explicitly in the field; its
adjustment to an S-unit and the S-unit ranks remain separate arithmetic work.
-/

noncomputable section

namespace NormEuclidean.SUnitNormArithmetic

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm
open scoped NumberField WithZero QuadraticAlgebra

universe u
variable {K E : Type u} [Field K] [NumberField K]
  [Field E] [NumberField E] [Algebra K E]

/-- O'Meara's S-units, with S the primes where valuations must be zero. -/
def sUnitSubgroup (S : Set (HeightOneSpectrum (𝓞 K))) : Subgroup Kˣ where
  carrier := {x | ∀ p ∈ S, p.valuation K x.val = 1}
  one_mem' := by intro p _; simp
  mul_mem' := by
    intro x y hx hy p hp
    simp only [Units.val_mul, map_mul, hx p hp, hy p hp, one_mul]
  inv_mem' := by
    intro x hx p hp
    simp only [Units.val_inv_eq_inv_val, map_inv₀, hx p hp, inv_one]

/-- The literal valuation condition for membership in the actual S-unit group. -/
theorem mem_sUnitSubgroup (S : Set (HeightOneSpectrum (𝓞 K))) (x : Kˣ) :
    x ∈ sUnitSubgroup S ↔ ∀ p ∈ S, p.valuation K x.val = 1 := Iff.rfl

/-- The S-unit group is exactly the pullback of the actual S-idele group
under the principal embedding. -/
theorem sUnitSubgroup_eq_comap (S : Set (HeightOneSpectrum (𝓞 K))) :
    sUnitSubgroup S = (finitePlaceSIdeleSubgroup S).comap idelePrincipalEmbedding := by
  ext x
  constructor
  · intro hx p hp
    change Valued.v (x.val : p.adicCompletion K) = 1
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' p x.val).trans (hx p hp)
  · intro hx p hp
    have hv := hx p hp
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' p x.val).symm.trans hv

/-- An automorphism over the base preserves S-unit support above base primes. -/
theorem automorphism_mem (e : E ≃ₐ[K] E) (S : Set (HeightOneSpectrum (𝓞 K)))
    (x : Eˣ) (hx : x ∈ sUnitSubgroup (finitePlacesOverSet (E := E) S)) :
    Units.map e.toMonoidHom x ∈ sUnitSubgroup (finitePlacesOverSet (E := E) S) := by
  intro w hw
  change w.valuation E (e x.val) = 1
  have hp : AdicAutomorphism.prime e.toRingEquiv w ∈ finitePlacesOverSet (E := E) S := by
    change (AdicAutomorphism.prime e.toRingEquiv w).under (𝓞 K) ∈ S
    rw [CompletedFiberAutomorphism.prime_under_eq]
    exact hw
  exact (AdicAutomorphism.valuation_map e.toRingEquiv w x.val).trans (hx _ hp)

/-- Conjugation as an endomorphism of the actual extension S-unit group. -/
def conjugationEnd (e : E ≃ₐ[K] E) (S : Set (HeightOneSpectrum (𝓞 K))) :
    sUnitSubgroup (finitePlacesOverSet (E := E) S) →*
      sUnitSubgroup (finitePlacesOverSet (E := E) S) where
  toFun x := ⟨Units.map e.toMonoidHom x.val, automorphism_mem e S x.val x.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)

/-- The norm endomorphism x maps to x times its conjugate. -/
def normEnd (e : E ≃ₐ[K] E) (S : Set (HeightOneSpectrum (𝓞 K))) :
    sUnitSubgroup (finitePlacesOverSet (E := E) S) →*
      sUnitSubgroup (finitePlacesOverSet (E := E) S) :=
  MonoidHom.id _ * conjugationEnd e S

/-- O'Meara's difference endomorphism x maps to x divided by its conjugate. -/
def differenceEnd (e : E ≃ₐ[K] E) (S : Set (HeightOneSpectrum (𝓞 K))) :
    sUnitSubgroup (finitePlacesOverSet (E := E) S) →*
      sUnitSubgroup (finitePlacesOverSet (E := E) S) :=
  MonoidHom.id _ / conjugationEnd e S

/-- An involution of fields induces an involution of the actual S-unit group. -/
theorem conjugationEnd_involutive (e : E ≃ₐ[K] E) (he : Function.Involutive e)
    (S : Set (HeightOneSpectrum (𝓞 K))) : Function.Involutive (conjugationEnd e S) := by
  intro x
  apply Subtype.ext
  apply Units.ext
  exact he x.val.val

/-- N composed with T is trivial on the actual S-unit group. -/
theorem norm_difference (e : E ≃ₐ[K] E) (he : Function.Involutive e)
    (S : Set (HeightOneSpectrum (𝓞 K)))
    (x : sUnitSubgroup (finitePlacesOverSet (E := E) S)) :
    normEnd e S (differenceEnd e S x) = 1 := by
  change (x / conjugationEnd e S x) * conjugationEnd e S (x / conjugationEnd e S x) = 1
  rw [map_div, conjugationEnd_involutive e he S]
  simp [div_eq_mul_inv, mul_assoc]

/-- T composed with N is trivial on the actual S-unit group. -/
theorem difference_norm (e : E ≃ₐ[K] E) (he : Function.Involutive e)
    (S : Set (HeightOneSpectrum (𝓞 K)))
    (x : sUnitSubgroup (finitePlacesOverSet (E := E) S)) :
    differenceEnd e S (normEnd e S x) = 1 := by
  change (x * conjugationEnd e S x) / conjugationEnd e S (x * conjugationEnd e S x) = 1
  rw [map_mul, conjugationEnd_involutive e he S]
  simp [mul_comm]

/-- The square identity used to construct the Herbrand finite-index subgroup. -/
theorem square_eq_norm_mul_difference (e : E ≃ₐ[K] E)
    (S : Set (HeightOneSpectrum (𝓞 K)))
    (x : sUnitSubgroup (finitePlacesOverSet (E := E) S)) :
    x ^ 2 = normEnd e S x * differenceEnd e S x := by
  change x ^ 2 = (x * conjugationEnd e S x) * (x / conjugationEnd e S x)
  simp [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm]

omit [Field E] [NumberField E] [Algebra K E] in
/-- In the concrete quadratic extension this is the actual determinant norm,
embedded back in the extension field, not an abstract norm operation. -/
theorem normEnd_actual (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    ∀ x : sUnitSubgroup (finitePlacesOverSet (E := QuadraticAlgebra K theta.val 0) S),
      (normEnd (QuadraticStableKernel.conjugation theta.val) S x).val.val =
        algebraMap K (QuadraticAlgebra K theta.val 0) (Algebra.norm K x.val.val) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  intro x
  change x.val.val * star x.val.val = _
  rw [algebra_norm_eq_quadraticAlgebra_norm, QuadraticAlgebra.algebraMap_norm_eq_mul_star]

omit [Field E] [NumberField E] [Algebra K E] in
/-- The actual global determinant norm sends extension S-units to base S-units. -/
theorem global_norm_mem (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    ∀ x : sUnitSubgroup (finitePlacesOverSet (E := QuadraticAlgebra K theta.val 0) S),
      PrincipalNormComponents.globalNormUnits (K := K) x.val ∈ sUnitSubgroup S := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  intro x
  rw [sUnitSubgroup_eq_comap]
  have hx : idelePrincipalEmbedding x.val ∈ finitePlaceSIdeleSubgroup
      (finitePlacesOverSet (E := QuadraticAlgebra K theta.val 0) S) := by
    intro w hw
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x.val.val).trans
      (x.property w hw)
  have hn := extensionIdeleNorm_mem_S S (idelePrincipalEmbedding x.val) hx
  rw [QuadraticPrincipalNorm.principal_norm theta htheta] at hn
  exact hn

section Hilbert90

variable {F : Type*} [Field F] [CharZero F]

/-- The explicit quadratic Hilbert 90 construction: use 1 plus H, or the
quadratic generator when H is minus one. The preimage is a field unit. -/
theorem exists_field_preimage (theta : Fˣ) (htheta : ¬ IsSquare theta) :
    letI := quadraticExtensionField theta htheta
    ∀ H : (QuadraticAlgebra F theta.val 0)ˣ,
      Algebra.norm F H.val = 1 →
      ∃ z : (QuadraticAlgebra F theta.val 0)ˣ,
        z / Units.map (QuadraticStableKernel.conjugation theta.val).toMonoidHom z = H := by
  letI := quadraticExtensionField theta htheta
  intro H hH
  have hn : H.val * star H.val = 1 := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star,
      ← algebra_norm_eq_quadraticAlgebra_norm theta H.val, hH, map_one]
  by_cases hm : H.val = -1
  · have ho : (ω : QuadraticAlgebra F theta.val 0) ≠ 0 := by
      intro h
      have hh := congrArg QuadraticAlgebra.im h
      simp [QuadraticAlgebra.omega] at hh
    let z := Units.mk0 (ω : QuadraticAlgebra F theta.val 0) ho
    refine ⟨z, ?_⟩
    apply Units.ext
    rw [Units.val_div_eq_div_val]
    change (ω : QuadraticAlgebra F theta.val 0) / star ω = H.val
    have hs : star (ω : QuadraticAlgebra F theta.val 0) = -ω := by
      ext <;> simp [QuadraticAlgebra.omega]
    rw [hm, hs]
    simp [ho]
  · have hz : 1 + H.val ≠ 0 := by
      intro h
      exact hm (eq_neg_of_add_eq_zero_right h)
    let z := Units.mk0 (1 + H.val) hz
    refine ⟨z, ?_⟩
    apply Units.ext
    rw [Units.val_div_eq_div_val]
    change (1 + H.val) / star (1 + H.val) = H.val
    have hs : star (1 + H.val) ≠ 0 :=
      (map_ne_zero (QuadraticStableKernel.conjugation theta.val).toRingHom).mpr hz
    apply (div_eq_iff hs).mpr
    rw [star_add, star_one, mul_add, mul_one, hn]
    exact add_comm _ _

end Hilbert90

omit [Field E] [NumberField E] [Algebra K E] in
/-- A norm-one S-unit has an explicit field preimage whose valuations at
conjugate primes over S agree. This does not assert that the preimage is an S-unit. -/
theorem exists_preimage_balanced (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    ∀ H : sUnitSubgroup (finitePlacesOverSet (E := QuadraticAlgebra K theta.val 0) S),
      Algebra.norm K H.val.val = 1 →
      ∃ z : (QuadraticAlgebra K theta.val 0)ˣ,
        z / Units.map (QuadraticStableKernel.conjugation theta.val).toMonoidHom z = H.val ∧
        ∀ w : HeightOneSpectrum (𝓞 (QuadraticAlgebra K theta.val 0)),
          w ∈ finitePlacesOverSet (E := QuadraticAlgebra K theta.val 0) S →
          w.valuation _ z.val =
            (AdicAutomorphism.prime
              (QuadraticStableKernel.conjugation theta.val).toRingEquiv w).valuation _ z.val := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  intro H hH
  obtain ⟨z, hz⟩ := exists_field_preimage theta htheta H.val hH
  refine ⟨z, hz, fun w hw ↦ ?_⟩
  have hf := congrArg Units.val hz
  rw [Units.val_div_eq_div_val] at hf
  change z.val / QuadraticStableKernel.conjugation theta.val z.val = H.val.val at hf
  have hv : w.valuation _ (z.val /
      QuadraticStableKernel.conjugation theta.val z.val) = 1 := by
    rw [hf]
    exact H.property w hw
  rw [map_div₀] at hv
  have hn : w.valuation _ (QuadraticStableKernel.conjugation theta.val z.val) ≠ 0 := by
    apply (Valuation.ne_zero_iff _).mpr
    exact (map_ne_zero (QuadraticStableKernel.conjugation theta.val).toRingHom).mpr z.ne_zero
  have heq : w.valuation _ z.val =
      w.valuation _ (QuadraticStableKernel.conjugation theta.val z.val) := by
    calc
      _ = _ / _ * w.valuation _ (QuadraticStableKernel.conjugation theta.val z.val) :=
        (div_mul_cancel₀ _ hn).symm
      _ = _ := by rw [hv, one_mul]
  exact heq.trans (AdicAutomorphism.valuation_map
    (QuadraticStableKernel.conjugation theta.val).toRingEquiv w z.val)

end NormEuclidean.SUnitNormArithmetic
