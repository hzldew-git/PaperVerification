import NormEuclidean.ChapterX.NormFiberAssembly
import Mathlib.GroupTheory.Index

/-!
# The actual finite product of local norm indices

Evaluation at the excluded finite primes and all infinite places is
surjective on the actual S-idele group. Its local norm preimage is the
actual extension S-idele norm subgroup when S consists of good primes.
Thus its relative index is the product of the actual local indices.
No numerical local norm-index value is assumed in this comparison.
-/

noncomputable section

namespace NormEuclidean.NormIndexProduct

/-- The index of a subgroup in a finite dependent product is the product
of the indices. The groups, as well as the subgroups, may vary with the index. -/
theorem index_dependent_pi {ι : Type*} [Fintype ι] (G : ι → Type*)
    [∀ i, CommGroup (G i)] (H : (i : ι) → Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  let f : ((i : ι) → G i) →* ((i : ι) → G i ⧸ H i) := {
    toFun x i := QuotientGroup.mk (x i)
    map_one' := by funext i; exact map_one (QuotientGroup.mk' (H i))
    map_mul' x y := by funext i; exact map_mul (QuotientGroup.mk' (H i)) (x i) (y i) }
  have hf : Function.Surjective f := by
    intro y
    choose x hx using fun i ↦ QuotientGroup.mk'_surjective (H i) (y i)
    exact ⟨x, funext hx⟩
  have hk : f.ker = Subgroup.pi Set.univ H := by
    ext x
    simp only [MonoidHom.mem_ker, f, MonoidHom.coe_mk, OneHom.coe_mk,
      funext_iff, Pi.one_apply, QuotientGroup.eq_one_iff, Subgroup.mem_pi,
      Set.mem_univ, forall_const]
  have hi := Subgroup.index_comap_of_surjective (H := (⊥ : Subgroup ((i : ι) → G i ⧸ H i))) hf
  change f.ker.index = (⊥ : Subgroup ((i : ι) → G i ⧸ H i)).index at hi
  rw [hk, Subgroup.index_bot, Nat.card_pi] at hi
  exact hi

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm
open scoped NumberField WithZero

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- Places whose unconstrained components occur in the 65:8 finite product. -/
abbrev Index (S : Set (HeightOneSpectrum (𝓞 K))) := ↥(Sᶜ) ⊕ NumberField.InfinitePlace K

/-- The actual local unit group at an excluded finite or infinite place. -/
abbrev UnitsAt {S : Set (HeightOneSpectrum (𝓞 K))} : Index S → Type u
  | .inl p => (p.1.adicCompletion K)ˣ
  | .inr v => v.Completionˣ

scoped instance unitsAtCommGroup {S : Set (HeightOneSpectrum (𝓞 K))} (q : Index S) :
    CommGroup (UnitsAt q) := by cases q <;> dsimp only [UnitsAt] <;> infer_instance

open scoped NormEuclidean.NormIndexProduct

/-- The local quadratic norm subgroup at each factor. -/
def localNormGroup (theta : Kˣ) {S : Set (HeightOneSpectrum (𝓞 K))}
    (q : Index S) : Subgroup (UnitsAt q) := match q with
  | .inl p => Bong.Dyadic.quadraticNormGroup (p.1.adicCompletion K)
      (Units.map (algebraMap K (p.1.adicCompletion K)).toMonoidHom theta)
  | .inr v => Bong.Dyadic.quadraticNormGroup v.Completion
      (Units.map (algebraMap K v.Completion).toMonoidHom theta)

/-- Evaluation of an actual S-idele on precisely these factors. -/
def evaluation (S : Set (HeightOneSpectrum (𝓞 K))) :
    finitePlaceSIdeleSubgroup S →* ((q : Index S) → UnitsAt q) where
  toFun x q := match q with
    | .inl p => ideleFiniteComponent p.1 x.val
    | .inr v => ideleInfiniteComponent v x.val
  map_one' := by funext q; cases q <;> exact map_one _
  map_mul' x y := by funext q; cases q <;> exact map_mul _ x.val y.val

/-- Arbitrary components on the excluded finite set and all infinite places
are attained by an actual S-idele. -/
theorem evaluation_surjective (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite) :
    Function.Surjective (evaluation S) := by
  classical
  intro a
  let f (p : HeightOneSpectrum (𝓞 K)) : (p.adicCompletion K)ˣ :=
    if h : p ∉ S then a (.inl ⟨p, h⟩) else 1
  have hf : ∀ᶠ p in Filter.cofinite, Valued.v (f p).val = 1 := by
    filter_upwards [Filter.eventually_cofinite.mpr hS] with p hp
    change p ∈ S at hp
    simp [f, hp]
  let j := NormFiberAssembly.ofComponents f hf (fun v ↦ a (.inr v))
  have hj : j ∈ finitePlaceSIdeleSubgroup S := by
    intro p hp
    rw [NormFiberAssembly.finiteComponent_ofComponents]
    simp [f, hp]
  refine ⟨⟨j, hj⟩, ?_⟩
  funext q
  cases q with
  | inl p =>
      change ideleFiniteComponent p.1 j = a (.inl p)
      rw [NormFiberAssembly.finiteComponent_ofComponents]
      exact dif_pos p.2
  | inr v => exact NormFiberAssembly.infiniteComponent_ofComponents f hf _ v

/-- The preimage of the local norm product is exactly the actual S-norm
subgroup inside the S-idele group, with good-place arithmetic discharged. -/
theorem norm_preimage (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite)
    (htwo : ∀ p ∈ S, (2 : 𝓞 K) ∉ p.asIdeal)
    (hunit : ∀ p ∈ S, p.valuation K theta.val = 1) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    (Subgroup.pi Set.univ (localNormGroup theta (S := S))).comap (evaluation S) =
      (sIdeleNormSubgroup (E := QuadraticAlgebra K theta.val 0) S).subgroupOf
        (finitePlaceSIdeleSubgroup S) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  ext x
  change (∀ q ∈ Set.univ, evaluation S x q ∈ localNormGroup theta q) ↔ _
  simp only [Set.mem_univ, forall_const]
  rw [Subgroup.mem_subgroupOf,
    NormFiberAssembly.mem_sNorm_iff_outside theta htheta S hS htwo hunit]
  constructor
  · intro h
    exact ⟨x.property, fun p hp ↦ h (.inl ⟨p, hp⟩), fun v ↦ h (.inr v)⟩
  · rintro ⟨_, hf, hinf⟩ q
    cases q with
    | inl p => exact hf p.1 p.2
    | inr v => exact hinf v

/-- The actual 65:8 relative index equals the finite dependent product of
the local indices. This equality also uses the natural zero convention for
an infinite index; no finiteness or numerical local index is assumed. -/
theorem index_product (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite)
    (htwo : ∀ p ∈ S, (2 : 𝓞 K) ∉ p.asIdeal)
    (hunit : ∀ p ∈ S, p.valuation K theta.val = 1) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    letI : Fintype ↥(Sᶜ) := hS.fintype
    (sIdeleNormSubgroup (E := QuadraticAlgebra K theta.val 0) S).relIndex
        (finitePlaceSIdeleSubgroup S) =
      ∏ q : Index S, (localNormGroup theta q).index := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  letI : Fintype ↥(Sᶜ) := hS.fintype
  change ((sIdeleNormSubgroup (E := QuadraticAlgebra K theta.val 0) S).subgroupOf
    (finitePlaceSIdeleSubgroup S)).index = _
  rw [← norm_preimage theta htheta S hS htwo hunit]
  exact (Subgroup.index_comap_of_surjective _ (evaluation_surjective S hS)).trans
    (index_dependent_pi _ _)

end NormEuclidean.NormIndexProduct
