import NormEuclidean.ChapterX.SeparatingSUnitPrimes
import NormEuclidean.ChapterX.SquareIdeles

/-!
# Strictness of the actual prime-idele chain in O'Meara 65:21

The chain starts with principal times square S-ideles and enlarges the
allowed finite support. A uniformizer at a newly added separating prime
cannot belong to the preceding subgroup: such membership would yield a
global square with odd valuation.
-/

noncomputable section

namespace NormEuclidean.NormPrimeChain

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm SUnitNormArithmetic
open PrimeSquareDetection SquareIdeles
open scoped NumberField WithZero

variable {K : Type*} [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι]

/-- Principal times square S-ideles, enlarged by the specified finite support. -/
def group (S T : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (NumberFieldIdele K) :=
  idelePrincipalEmbedding.range ⊔ (squareS S ⊔ supported T)

/-- Increasing the support increases the actual chain subgroup. -/
theorem group_mono (S : Set (HeightOneSpectrum (𝓞 K)))
    {T U : Set (HeightOneSpectrum (𝓞 K))} (h : T ⊆ U) : group S T ≤ group S U :=
  sup_le_sup_left (sup_le_sup_left (supported_mono h) _) _

/-- The chain starts with the literal principal-times-square S-idele subgroup. -/
theorem group_empty (S : Set (HeightOneSpectrum (𝓞 K))) :
    group S ∅ = idelePrincipalEmbedding.range ⊔ squareS S := by
  rw [group, supported_empty, sup_bot_eq]

/-- A unit with uniformizer valuation is not a square in the global field. -/
theorem not_square_uniformizer (q : HeightOneSpectrum (𝓞 K)) (a : Kˣ)
    (ha : q.valuation K a.val = WithZero.exp (-1 : ℤ)) : ¬ IsSquare a := by
  rintro ⟨r, hr⟩
  have he : a.val = r.val * r.val := congrArg Units.val hr
  rw [he, map_mul] at ha
  have hn : q.valuation K r.val ≠ 0 := (Valuation.ne_zero_iff _).mpr r.ne_zero
  have hl := congrArg (fun z : ℤᵐ⁰ ↦ WithZero.log z) ha
  rw [WithZero.log_mul hn hn, WithZero.log_exp] at hl
  omega

/-- A new separating-prime uniformizer lies outside the preceding subgroup. -/
theorem uniformizer_not_mem (S : Set (HeightOneSpectrum (𝓞 K)))
    (e : ι → sUnitSubgroup S) (p : ι → HeightOneSpectrum (𝓞 K))
    (hsep : Separates S e p) (htwo : ∀ p ∈ S, (2 : 𝓞 K) ∉ p.asIdeal)
    (hprincipal : idelePrincipalEmbedding.range ⊔ finitePlaceSIdeleSubgroup S = ⊤)
    (T : Set (HeightOneSpectrum (𝓞 K))) (hT : T ⊆ Set.range p)
    (q : HeightOneSpectrum (𝓞 K)) (hqP : q ∈ Set.range p) (hqS : q ∈ S) (hqT : q ∉ T)
    (pi : (q.adicCompletion K)ˣ) (hpi : Valued.v pi.val = WithZero.exp (-1 : ℤ)) :
    single q pi ∉ group S T := by
  classical
  intro hmem
  obtain ⟨_, ⟨a, rfl⟩, _, hrest, heq⟩ := Subgroup.mem_sup.mp hmem
  obtain ⟨j, hj, k, hk, rfl⟩ := Subgroup.mem_sup.mp hrest
  have hf (r : HeightOneSpectrum (𝓞 K)) :
      Units.map (algebraMap K (r.adicCompletion K)).toMonoidHom a *
        (ideleFiniteComponent r j * ideleFiniteComponent r k) =
          Pi.mulSingle (M := FiniteUnits) q pi r := by
    have h := congrArg (ideleFiniteComponent r) heq
    simpa only [map_mul, PrincipalNormComponents.finiteComponent_principal,
      finite_single] using h
  have hi (v : NumberField.InfinitePlace K) :
      Units.map (algebraMap K v.Completion).toMonoidHom a *
        ideleInfiniteComponent v j = 1 := by
    have h := congrArg (ideleInfiniteComponent v) heq
    simpa only [map_mul, PrincipalNormComponents.infiniteComponent_principal,
      hk.2 v, mul_one, infinite_single] using h
  have haf (r : HeightOneSpectrum (𝓞 K)) (hrS : r ∉ S) :
      IsSquare (algebraMap K (r.adicCompletion K) a.val) := by
    have hrq : r ≠ q := fun h ↦ hrS (h.symm ▸ hqS)
    have hrT : r ∉ T := by
      intro hr
      obtain ⟨i, rfl⟩ := hT hr
      exact hrS (hsep.1 i)
    have h := hf r
    rw [hk.1 r hrT, mul_one, Pi.mulSingle_eq_of_ne hrq] at h
    have he : Units.map (algebraMap K (r.adicCompletion K)).toMonoidHom a =
        (ideleFiniteComponent r j)⁻¹ := mul_eq_one_iff_eq_inv.mp h
    apply (GlobalSquare.unit_square_iff
      (Units.map (algebraMap K (r.adicCompletion K)).toMonoidHom a)).mp
    rw [he]
    exact (hj.2.1 r hrS).inv
  have hai (v : NumberField.InfinitePlace K) : IsSquare (algebraMap K v.Completion a.val) := by
    have he : Units.map (algebraMap K v.Completion).toMonoidHom a =
        (ideleInfiniteComponent v j)⁻¹ := mul_eq_one_iff_eq_inv.mp (hi v)
    apply (GlobalSquare.unit_square_iff
      (Units.map (algebraMap K v.Completion).toMonoidHom a)).mp
    rw [he]
    exact (hj.2.2 v).inv
  have hau (r : HeightOneSpectrum (𝓞 K)) (hrS : r ∈ S) (hr : r ∉ Set.range p) :
      r.valuation K a.val = 1 := by
    by_cases hrq : r = q
    · subst r
      exact False.elim (hr hqP)
    · have hrT : r ∉ T := fun h ↦ hr (hT h)
      have h := hf r
      rw [hk.1 r hrT, mul_one, Pi.mulSingle_eq_of_ne hrq] at h
      have hv := congrArg (fun z : (r.adicCompletion K)ˣ ↦ Valued.v z.val) h
      simp only [Units.val_mul, map_mul, Units.val_one, map_one] at hv
      rw [hj.1 r hrS, mul_one] at hv
      exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' r a.val).symm.trans hv
  have hasq := isSquare_of_punctured_units S e p hsep htwo hprincipal a hau haf hai
  have hq := hf q
  rw [hk.1 q hqT, mul_one, Pi.mulSingle_eq_same] at hq
  have hv := congrArg (fun z : (q.adicCompletion K)ˣ ↦ Valued.v z.val) hq
  simp only [Units.val_mul, map_mul] at hv
  rw [hj.1 q hqS, mul_one, hpi] at hv
  exact not_square_uniformizer q a
    ((HeightOneSpectrum.valuedAdicCompletion_eq_valuation' q a.val).symm.trans hv) hasq

/-- Adding a new separating-prime support makes the actual subgroup strictly larger. -/
theorem group_strict (S : Set (HeightOneSpectrum (𝓞 K)))
    (e : ι → sUnitSubgroup S) (p : ι → HeightOneSpectrum (𝓞 K))
    (hsep : Separates S e p) (htwo : ∀ p ∈ S, (2 : 𝓞 K) ∉ p.asIdeal)
    (hprincipal : idelePrincipalEmbedding.range ⊔ finitePlaceSIdeleSubgroup S = ⊤)
    (T U : Set (HeightOneSpectrum (𝓞 K))) (hT : T ⊆ Set.range p) (hTU : T ⊆ U)
    (q : HeightOneSpectrum (𝓞 K)) (hqP : q ∈ Set.range p) (hqS : q ∈ S)
    (hqT : q ∉ T) (hqU : q ∈ U) : group S T < group S U := by
  obtain ⟨pi, hpi⟩ := LocalNormIndices.exists_uniformizer q
  refine lt_of_le_of_ne (group_mono S hTU) ?_
  intro heq
  apply uniformizer_not_mem S e p hsep htwo hprincipal T hT q hqP hqS hqT pi hpi
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_sup_right (single_mem_supported q pi U hqU))

end NormEuclidean.NormPrimeChain
