import NormEuclidean.ChapterX.SUnitHilbert90

/-!
# Exact Hilbert 90 on actual S-units

Base principalization and the balanced-coordinate envelope turn the field
preimage into an actual S-unit. The difference image is consequently the
kernel of the actual quadratic norm endomorphism on S-units.
-/

noncomputable section

namespace NormEuclidean.SUnitHilbert90Exact

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm SUnitNormArithmetic
open SUnitHilbert90
open scoped NumberField QuadraticAlgebra

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- Every norm-one S-unit has an S-unit Hilbert 90 preimage. The scalar
adjustment is constructed internally from actual base principalization. -/
theorem exists_sUnit_preimage (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K)))
    (htwo : ∀ p ∈ S, (2 : 𝓞 K) ∉ p.asIdeal)
    (hunit : ∀ p ∈ S, p.valuation K theta.val = 1)
    (hprincipal : idelePrincipalEmbedding.range ⊔ finitePlaceSIdeleSubgroup S = ⊤) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    ∀ H : sUnitSubgroup (finitePlacesOverSet (E := QuadraticAlgebra K theta.val 0) S),
      Algebra.norm K H.val.val = 1 →
      ∃ z : sUnitSubgroup (finitePlacesOverSet (E := QuadraticAlgebra K theta.val 0) S),
        z.val / Units.map (QuadraticStableKernel.conjugation theta.val).toMonoidHom z.val =
          H.val := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  intro H hH
  obtain ⟨z, hz, hbalanced⟩ := exists_preimage_balanced theta htheta S H hH
  let c : K × K := (z.val.re, z.val.im)
  have hc : c ≠ 0 := by
    intro h
    apply z.ne_zero
    apply QuadraticAlgebra.ext
    · simpa [c] using congrArg Prod.fst h
    · simpa [c] using congrArg Prod.snd h
  obtain ⟨a, ha⟩ := exists_scalar_envelope S hprincipal c hc
  let aE := Units.map (algebraMap K (QuadraticAlgebra K theta.val 0)).toMonoidHom a
  let q := z / aE
  have hq : q ∈ sUnitSubgroup (finitePlacesOverSet (E := QuadraticAlgebra K theta.val 0) S) := by
    intro w hw
    let p := w.under (𝓞 K)
    letI : w.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
    have hp : p ∈ S := hw
    have hb : w.valuation _ z.val = w.valuation _ (star z.val) := by
      exact (hbalanced w hw).trans (AdicAutomorphism.valuation_map
        (QuadraticStableKernel.conjugation theta.val).toRingEquiv w z.val).symm
    have he := balanced_value_envelope theta htheta p (htwo p hp) (hunit p hp) w rfl z.val hb
    have hva : w.valuation _ (algebraMap K (QuadraticAlgebra K theta.val 0) a.val) =
        w.valuation _ z.val := by
      rw [← HeightOneSpectrum.valuation_liesOver _ p w a.val, ha p hp]
      exact he.symm
    dsimp only [q]
    rw [Units.val_div_eq_div_val, map_div₀]
    change w.valuation _ z.val /
      w.valuation _ (algebraMap K (QuadraticAlgebra K theta.val 0) a.val) = 1
    rw [hva]
    exact div_self ((Valuation.ne_zero_iff _).mpr z.ne_zero)
  refine ⟨⟨q, hq⟩, ?_⟩
  have hconja : Units.map (QuadraticStableKernel.conjugation theta.val).toMonoidHom aE = aE := by
    apply Units.ext
    exact (QuadraticStableKernel.conjugation theta.val).commutes a.val
  change q / Units.map (QuadraticStableKernel.conjugation theta.val).toMonoidHom q = H.val
  calc
    _ = z / Units.map (QuadraticStableKernel.conjugation theta.val).toMonoidHom z := by
      dsimp only [q]
      rw [map_div, hconja]
      simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    _ = H.val := hz

/-- The actual S-unit difference image equals the actual norm kernel. -/
theorem difference_range_eq_norm_kernel (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K)))
    (htwo : ∀ p ∈ S, (2 : 𝓞 K) ∉ p.asIdeal)
    (hunit : ∀ p ∈ S, p.valuation K theta.val = 1)
    (hprincipal : idelePrincipalEmbedding.range ⊔ finitePlaceSIdeleSubgroup S = ⊤) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    (differenceEnd (QuadraticStableKernel.conjugation theta.val) S).range =
      (normEnd (QuadraticStableKernel.conjugation theta.val) S).ker := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  ext H
  constructor
  · rintro ⟨z, rfl⟩
    exact norm_difference _ (fun x ↦ star_star x) S z
  · intro h
    have hv := congrArg (fun x ↦ x.val.val) (show normEnd
      (QuadraticStableKernel.conjugation theta.val) S H = 1 from h)
    have hnorm : Algebra.norm K H.val.val = 1 := by
      apply FaithfulSMul.algebraMap_injective K (QuadraticAlgebra K theta.val 0)
      exact (normEnd_actual theta htheta S H).symm.trans hv
    obtain ⟨z, hz⟩ := exists_sUnit_preimage theta htheta S htwo hunit hprincipal H hnorm
    exact ⟨z, Subtype.ext hz⟩

end NormEuclidean.SUnitHilbert90Exact
