import NormEuclidean.ChapterX.CompletedNormUnitLifting
import NormEuclidean.ChapterX.ExtensionNormPrincipalization
import NormEuclidean.ChapterX.GoodPlaceNorms
import Mathlib.Data.Set.Finite.Lattice

/-!
# Assembling actual norm fibers into ideles

Finite fibers of the prime restriction map preserve finite exceptional
support. The actual local unit preimage theorem therefore suffices to glue
component norm equations into an extension S-idele on a cofinite set S.
-/

noncomputable section

namespace NormEuclidean.NormFiberAssembly

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm
open scoped NumberField WithZero

universe u
variable {K E : Type u} [Field K] [NumberField K]
  [Field E] [NumberField E] [Algebra K E]

/-- A finite set of base primes has finitely many extension primes above it. -/
theorem finite_preimage_under (T : Set (HeightOneSpectrum (𝓞 K))) (hT : T.Finite) :
    ((fun w : HeightOneSpectrum (𝓞 E) ↦ w.under (𝓞 K)) ⁻¹' T).Finite := by
  let f := fun w : HeightOneSpectrum (𝓞 E) ↦ w.under (𝓞 K)
  apply Set.Finite.of_finite_fibers f (hT.subset (Set.image_preimage_subset f T))
  intro p _
  have hp : {w : HeightOneSpectrum (𝓞 E) | f w = p}.Finite := by
    exact Set.finite_coe_iff.mp (inferInstanceAs (Finite (FinitePlacesAbove (E := E) p)))
  exact hp.subset (fun _ h ↦ h.2)

/-- Flatten finite norm fibers without making arbitrary choices of places above p. -/
def flattenFinite (z : (p : HeightOneSpectrum (𝓞 K)) →
    (w : FinitePlacesAbove (E := E) p) → (w.1.adicCompletion E)ˣ)
    (w : HeightOneSpectrum (𝓞 E)) : (w.adicCompletion E)ˣ :=
  z (w.under (𝓞 K)) ⟨w, rfl⟩

omit [NumberField K] in
/-- Evaluation recovers the original finite fiber, including its dependent field. -/
theorem flattenFinite_fiber (z : (p : HeightOneSpectrum (𝓞 K)) →
    (w : FinitePlacesAbove (E := E) p) → (w.1.adicCompletion E)ˣ)
    (p : HeightOneSpectrum (𝓞 K)) (w : FinitePlacesAbove (E := E) p) :
    flattenFinite z w.1 = z p w := by
  rcases w with ⟨w, hw⟩
  subst p
  rfl

/-- Flatten the analogous finite fibers of the infinite-place restriction map. -/
def flattenInfinite (z : (v : NumberField.InfinitePlace K) →
    (w : InfinitePlacesAbove (E := E) v) → w.1.Completionˣ)
    (w : NumberField.InfinitePlace E) : w.Completionˣ :=
  z (w.comap (algebraMap K E)) ⟨w, rfl⟩

omit [NumberField K] [NumberField E] in
/-- Evaluation recovers the original infinite fiber. -/
theorem flattenInfinite_fiber (z : (v : NumberField.InfinitePlace K) →
    (w : InfinitePlacesAbove (E := E) v) → w.1.Completionˣ)
    (v : NumberField.InfinitePlace K) (w : InfinitePlacesAbove (E := E) v) :
    flattenInfinite z w.1 = z v w := by
  rcases w with ⟨w, hw⟩
  subst v
  rfl

/-- Assemble prescribed local units into an actual full idele when the
finite coordinates are valuation units almost everywhere. -/
def ofComponents (f : (w : HeightOneSpectrum (𝓞 E)) → (w.adicCompletion E)ˣ)
    (hf : ∀ᶠ w in Filter.cofinite, Valued.v (f w).val = 1)
    (g : (w : NumberField.InfinitePlace E) → w.Completionˣ) : NumberFieldIdele E :=
  MulEquiv.prodUnits.symm (MulEquiv.piUnits.symm g, RestrictedProduct.mkUnit f (by
    filter_upwards [hf] with w hw
    exact (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one).mpr hw))

/-- The prescribed finite coordinates of the assembled idele. -/
theorem finiteComponent_ofComponents
    (f : (w : HeightOneSpectrum (𝓞 E)) → (w.adicCompletion E)ˣ)
    (hf : ∀ᶠ w in Filter.cofinite, Valued.v (f w).val = 1)
    (g : (w : NumberField.InfinitePlace E) → w.Completionˣ)
    (w : HeightOneSpectrum (𝓞 E)) : ideleFiniteComponent w (ofComponents f hf g) = f w := by
  apply Units.ext
  rfl

/-- The prescribed infinite coordinates of the assembled idele. -/
theorem infiniteComponent_ofComponents
    (f : (w : HeightOneSpectrum (𝓞 E)) → (w.adicCompletion E)ˣ)
    (hf : ∀ᶠ w in Filter.cofinite, Valued.v (f w).val = 1)
    (g : (w : NumberField.InfinitePlace E) → w.Completionˣ)
    (w : NumberField.InfinitePlace E) : ideleInfiniteComponent w (ofComponents f hf g) = g w := by
  apply Units.ext
  rfl

omit [Field E] [NumberField E] [Algebra K E] in
/-- Literal characterization of the actual quadratic S-idele norm image.
The complement of S is finite; no local norm-index formula is an input. -/
theorem mem_sNorm_iff (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite) (i : NumberFieldIdele K) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    i ∈ sIdeleNormSubgroup (E := QuadraticAlgebra K (theta : K) 0) S ↔
      i ∈ finitePlaceSIdeleSubgroup S ∧
      (∀ p, ideleFiniteComponent p i ∈
        (finitePlaceFiberNormUnits (E := QuadraticAlgebra K (theta : K) 0) p).range) ∧
      (∀ v, ideleInfiniteComponent v i ∈
        (infinitePlaceFiberNormUnits (E := QuadraticAlgebra K (theta : K) 0) v).range) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨extensionIdeleNorm_mem_S S j hj, ?_, ?_⟩
    · intro p
      exact ⟨fun w ↦ ideleFiniteComponent w.1 j, rfl⟩
    · intro v
      exact ⟨fun w ↦ ideleInfiniteComponent w.1 j, rfl⟩
  · rintro ⟨hiS, hfinite, hinfinite⟩
    have hpre (p : HeightOneSpectrum (𝓞 K)) :
        ∃ z : (w : FinitePlacesAbove (E := QuadraticAlgebra K (theta : K) 0) p) →
            (w.1.adicCompletion (QuadraticAlgebra K (theta : K) 0))ˣ,
          finitePlaceFiberNormUnits p z = ideleFiniteComponent p i ∧
            (p ∈ S → ∀ w, Valued.v (z w).val = 1) := by
      by_cases hp : p ∈ S
      · obtain ⟨z, hz, hu⟩ := CompletedNormUnitLifting.exists_unit_preimage
          theta htheta p (ideleFiniteComponent p i) (hiS p hp) (hfinite p)
        exact ⟨z, hz, fun _ ↦ hu⟩
      · obtain ⟨z, hz⟩ := hfinite p
        exact ⟨z, hz, fun h ↦ (hp h).elim⟩
    choose z hz hu using hpre
    choose t ht using hinfinite
    let f := flattenFinite z
    have hf : ∀ᶠ w in Filter.cofinite, Valued.v (f w).val = 1 := by
      have hbad := finite_preimage_under (E := QuadraticAlgebra K (theta : K) 0) Sᶜ hS
      filter_upwards [Filter.eventually_cofinite.mpr hbad] with w hw
      exact hu (w.under (𝓞 K)) hw ⟨w, rfl⟩
    let j := ofComponents f hf (flattenInfinite t)
    refine ⟨j, ?_, ?_⟩
    · intro w hw
      rw [finiteComponent_ofComponents]
      exact hu (w.under (𝓞 K)) hw ⟨w, rfl⟩
    · apply Units.ext
      apply Prod.ext
      · funext v
        have hv : infinitePlaceFiberNormUnits v (fun w ↦ ideleInfiniteComponent w.1 j) =
            ideleInfiniteComponent v i := by
          convert ht v using 1
          congr 1
          funext w
          exact (infiniteComponent_ofComponents f hf (flattenInfinite t) w.1).trans
            (flattenInfinite_fiber t v w)
        exact congrArg Units.val hv
      · apply DFunLike.ext
        intro p
        have hp : finitePlaceFiberNormUnits p (fun w ↦ ideleFiniteComponent w.1 j) =
            ideleFiniteComponent p i := by
          convert hz p using 1
          congr 1
          funext w
          exact (finiteComponent_ofComponents f hf (flattenInfinite t) w.1).trans
            (flattenFinite_fiber z p w)
        exact congrArg Units.val hp

omit [Field E] [NumberField E] [Algebra K E] in
/-- Quadratic norm equations characterize the actual cofinite S-idele norm
image, with the integrality support retained in the conclusion. -/
theorem mem_sNorm_iff_quadraticNorm (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite) (i : NumberFieldIdele K) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    i ∈ sIdeleNormSubgroup (E := QuadraticAlgebra K theta.val 0) S ↔
      i ∈ finitePlaceSIdeleSubgroup S ∧
      (∀ p, Bong.Dyadic.IsQuadraticNorm (p.adicCompletion K)
        (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta)
        (ideleFiniteComponent p i)) ∧
      (∀ v, Bong.Dyadic.IsQuadraticNorm v.Completion
        (Units.map (algebraMap K v.Completion).toMonoidHom theta)
        (ideleInfiniteComponent v i)) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  rw [mem_sNorm_iff theta htheta S hS i]
  simp_rw [CompletedNormImages.finite_norm_range_iff theta htheta,
    CompletedNormImages.infinite_norm_range_iff theta htheta]

omit [Field E] [NumberField E] [Algebra K E] in
/-- At good primes in S all unit norm conditions are automatic. Thus only
the excluded finite primes and the infinite places impose norm equations. -/
theorem mem_sNorm_iff_outside (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite)
    (htwo : ∀ p ∈ S, (2 : 𝓞 K) ∉ p.asIdeal)
    (hunit : ∀ p ∈ S, p.valuation K theta.val = 1) (i : NumberFieldIdele K) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    i ∈ sIdeleNormSubgroup (E := QuadraticAlgebra K theta.val 0) S ↔
      i ∈ finitePlaceSIdeleSubgroup S ∧
      (∀ p ∉ S, Bong.Dyadic.IsQuadraticNorm (p.adicCompletion K)
        (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta)
        (ideleFiniteComponent p i)) ∧
      (∀ v, Bong.Dyadic.IsQuadraticNorm v.Completion
        (Units.map (algebraMap K v.Completion).toMonoidHom theta)
        (ideleInfiniteComponent v i)) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  rw [mem_sNorm_iff_quadraticNorm theta htheta S hS i]
  constructor
  · exact fun h ↦ ⟨h.1, fun p _ ↦ h.2.1 p, h.2.2⟩
  · rintro ⟨hi, hf, hinf⟩
    refine ⟨hi, fun p ↦ ?_, hinf⟩
    by_cases hp : p ∈ S
    · apply (CompletedNormImages.finite_norm_range_iff theta htheta p _).mp
      exact GoodPlaceNorms.mem_actual_norm_range theta htheta p (htwo p hp)
        (hunit p hp) _ (hi p hp)
    · exact hf p hp

omit [Field E] [NumberField E] [Algebra K E] in
/-- All local quadratic norm equations characterize the actual full idele
norm image. This is an idele assembly theorem, not a Hasse norm theorem for
global field elements. -/
theorem mem_full_norm_range_iff (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (i : NumberFieldIdele K) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    i ∈ (extensionIdeleNorm (K := K) (E := QuadraticAlgebra K theta.val 0)).range ↔
      (∀ p, Bong.Dyadic.IsQuadraticNorm (p.adicCompletion K)
        (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta)
        (ideleFiniteComponent p i)) ∧
      (∀ v, Bong.Dyadic.IsQuadraticNorm v.Completion
        (Units.map (algebraMap K v.Completion).toMonoidHom theta)
        (ideleInfiniteComponent v i)) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  constructor
  · rintro ⟨j, rfl⟩
    constructor
    · intro p
      exact (CompletedNormImages.finite_norm_range_iff theta htheta p _).mp
        ⟨fun w ↦ ideleFiniteComponent w.1 j, rfl⟩
    · intro v
      exact (CompletedNormImages.infinite_norm_range_iff theta htheta v _).mp
        ⟨fun w ↦ ideleInfiniteComponent w.1 j, rfl⟩
  · rintro ⟨hf, hinf⟩
    let S : Set (HeightOneSpectrum (𝓞 K)) :=
      {p | Valued.v (ideleFiniteComponent p i).val = 1}
    have hS : Sᶜ.Finite :=
      Filter.eventually_cofinite.mp (ideleFiniteComponent_eventually_valuation_one i)
    have hmem := (mem_sNorm_iff_quadraticNorm theta htheta S hS i).mpr
      ⟨fun _ hp ↦ hp, hf, hinf⟩
    exact (sIdeleNormSubgroup_le S hmem).2

end NormEuclidean.NormFiberAssembly
