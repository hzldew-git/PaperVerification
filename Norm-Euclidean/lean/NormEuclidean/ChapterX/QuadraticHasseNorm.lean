import NormEuclidean.ChapterX.QuadraticGlobalNormIndex

/-!
# O'Meara 65:22--23: the quadratic Hasse norm theorem

The proved indices in 65:13 and 65:21 force the principal S-norm
intersection index to be one. An admissible core avoiding the nonunit
places of the proposed norm then recovers a genuine global field norm.
-/

noncomputable section

namespace NormEuclidean.QuadraticHasseNorm

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm
open PrincipalNormComponents
open scoped NumberField

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- O'Meara 65:22 as an equality of actual principal and S-idele norm subgroups. -/
theorem principal_intersection (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite)
    (htwo : ∀ p ∈ S, (2 : 𝓞 K) ∉ p.asIdeal)
    (hunit : ∀ p ∈ S, p.valuation K theta.val = 1) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    idelePrincipalEmbedding.range ⊔ finitePlaceSIdeleSubgroup S = ⊤ →
      idelePrincipalEmbedding.range ⊔ finitePlaceSIdeleSubgroup
        (finitePlacesOverSet (E := QuadraticAlgebra K theta.val 0) S) = ⊤ →
      (idelePrincipalEmbedding.range ⊓ finitePlaceSIdeleSubgroup S) ⊓
        sIdeleNormSubgroup (E := QuadraticAlgebra K theta.val 0) S =
          principalSNormSubgroup (E := QuadraticAlgebra K theta.val 0) S := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  intro hb he
  obtain ⟨hf, _⟩ := QuadraticNormIndexExact.index_formula theta htheta S hS htwo hunit hb he
  rw [QuadraticGlobalNormIndex.index_two theta htheta] at hf
  have hi : (principalSNormSubgroup (E := QuadraticAlgebra K theta.val 0) S).relIndex
      ((idelePrincipalEmbedding.range ⊓ finitePlaceSIdeleSubgroup S) ⊓
        sIdeleNormSubgroup (E := QuadraticAlgebra K theta.val 0) S) = 1 := by omega
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hi)
    (QuadraticPrincipalNorm.principalSNorm_le_intersection theta htheta S)

/-- O'Meara 65:23 for a nonsquare parameter and all actual completions.
No Hasse, norm-index or principalization premise remains. -/
theorem of_all_places (theta alpha : Kˣ) (htheta : ¬ IsSquare theta)
    (hf : ∀ p : HeightOneSpectrum (𝓞 K), Bong.Dyadic.IsQuadraticNorm
      (p.adicCompletion K) (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta)
      (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom alpha))
    (hi : ∀ v : NumberField.InfinitePlace K, Bong.Dyadic.IsQuadraticNorm
      v.Completion (Units.map (algebraMap K v.Completion).toMonoidHom theta)
      (Units.map (algebraMap K v.Completion).toMonoidHom alpha)) :
    Bong.Dyadic.IsQuadraticNorm K theta alpha := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  let T : Set (HeightOneSpectrum (𝓞 K)) := {p | p.valuation K alpha.val ≠ 1}
  have hT : T.Finite := CofiniteLocalIsotropy.finite_nonunit_valuations alpha.val alpha.ne_zero
  obtain ⟨S, hS, _, hdis, htwo, hunit, hprincipal⟩ :=
    exists_admissible_common_core (E := QuadraticAlgebra K theta.val 0) theta T hT
  have haS : idelePrincipalEmbedding alpha ∈ finitePlaceSIdeleSubgroup S := by
    intro p hp
    have hnot : p ∉ T := fun ht ↦ Set.disjoint_left.mp hdis hp ht
    have hu : p.valuation K alpha.val = 1 := not_ne_iff.mp hnot
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' p alpha.val).trans hu
  have hnorm : idelePrincipalEmbedding alpha ∈
      sIdeleNormSubgroup (E := QuadraticAlgebra K theta.val 0) S :=
    (NormFiberAssembly.mem_sNorm_iff_quadraticNorm theta htheta S hS _).mpr ⟨haS, hf, hi⟩
  have heq := principal_intersection theta htheta S hS htwo hunit
    (hprincipal S le_rfl).1 (hprincipal S le_rfl).2
  have hc : idelePrincipalEmbedding alpha ∈
      principalSNormSubgroup (E := QuadraticAlgebra K theta.val 0) S :=
    heq ▸ (show idelePrincipalEmbedding alpha ∈
      (idelePrincipalEmbedding.range ⊓ finitePlaceSIdeleSubgroup S) ⊓
        sIdeleNormSubgroup (E := QuadraticAlgebra K theta.val 0) S from
          ⟨⟨⟨alpha, rfl⟩, haS⟩, hnorm⟩)
  obtain ⟨z, hz⟩ := QuadraticPrincipalNorm.principalSNorm_le_global theta htheta S hc
  have hza : globalNormUnits (K := K) z = alpha := SUnitIdeleIndex.principal_injective hz
  apply (quadraticNorm_iff_quadraticAlgebra_unit_norm theta alpha).mpr
  exact ⟨z, congrArg Units.val hza⟩

/-- The all-place norm principle also includes split quadratic algebras. -/
theorem of_all_places_all (theta alpha : Kˣ)
    (hf : ∀ p : HeightOneSpectrum (𝓞 K), Bong.Dyadic.IsQuadraticNorm
      (p.adicCompletion K) (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta)
      (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom alpha))
    (hi : ∀ v : NumberField.InfinitePlace K, Bong.Dyadic.IsQuadraticNorm
      v.Completion (Units.map (algebraMap K v.Completion).toMonoidHom theta)
      (Units.map (algebraMap K v.Completion).toMonoidHom alpha)) :
    Bong.Dyadic.IsQuadraticNorm K theta alpha := by
  by_cases htheta : IsSquare theta
  · exact Bong.Dyadic.isQuadraticNorm_of_isSquare_left K htheta
  · exact of_all_places theta alpha htheta hf hi

omit [NumberField K] in
/-- A solved quadratic norm equation maps to any field extension. -/
theorem map_norm {F : Type*} [Field F] (f : K →+* F) (theta alpha : Kˣ)
    (h : Bong.Dyadic.IsQuadraticNorm K theta alpha) :
    Bong.Dyadic.IsQuadraticNorm F (Units.map f.toMonoidHom theta)
      (Units.map f.toMonoidHom alpha) := by
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨f x, f y, ?_⟩
  change f x ^ 2 - f theta.val * f y ^ 2 = f alpha.val
  simpa only [map_sub, map_pow, map_mul] using congrArg f hxy

/-- A quadratic norm equation is solvable globally exactly when it is solvable
at every actual finite and infinite completion, also in the split case. -/
theorem iff_all_places (theta alpha : Kˣ) :
    Bong.Dyadic.IsQuadraticNorm K theta alpha ↔
      (∀ p : HeightOneSpectrum (𝓞 K), Bong.Dyadic.IsQuadraticNorm
        (p.adicCompletion K) (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta)
        (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom alpha)) ∧
      (∀ v : NumberField.InfinitePlace K, Bong.Dyadic.IsQuadraticNorm
        v.Completion (Units.map (algebraMap K v.Completion).toMonoidHom theta)
        (Units.map (algebraMap K v.Completion).toMonoidHom alpha)) :=
  ⟨fun h ↦ ⟨fun p ↦ map_norm (algebraMap K (p.adicCompletion K)) theta alpha h,
      fun v ↦ map_norm (algebraMap K v.Completion) theta alpha h⟩,
    fun h ↦ of_all_places_all theta alpha h.1 h.2⟩

end NormEuclidean.QuadraticHasseNorm
