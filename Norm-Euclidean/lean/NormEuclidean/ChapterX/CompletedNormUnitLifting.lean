import NormEuclidean.ChapterX.CompletedNormImages
import NormEuclidean.ChapterX.LocalNormReflection
import NormEuclidean.ChapterX.SplitNormUnits

/-!
# Unit preimages for actual quadratic completion norms

For nonsplit fibers the product has one field factor, so norm reflection
applies. For split fibers the explicit quadratic preimage has each field
image equal to one or the embedded target. A unit target therefore has a
simultaneous unit preimage in every factor. This includes dyadic places.
-/

noncomputable section

namespace NormEuclidean.CompletedNormUnitLifting

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm CompletedNormImages
open scoped NumberField WithZero NormEuclidean.CompletedExtensionProduct

universe u
variable {K E : Type u} [Field K] [NumberField K]
  [Field E] [NumberField E] [Algebra K E]

/-- The actual continuous completion embedding preserves valuation units. -/
theorem completionMap_valuation_one (p : HeightOneSpectrum (𝓞 K))
    (w : FinitePlacesAbove (E := E) p) (a : (p.adicCompletion K)ˣ)
    (ha : Valued.v (a : p.adicCompletion K) = 1) :
    Valued.v (finitePlaceAboveCompletionMap p w (a : p.adicCompletion K)) = 1 := by
  letI : NontriviallyNormedField (w.1.adicCompletion E) :=
    Valued.toNontriviallyNormedField (w.1.adicCompletion E) ℤᵐ⁰
  let S : Subring (p.adicCompletion K) := (p.adicCompletionIntegers K).toSubring
  letI : CompactSpace S := CompletionHensel.compact_completed_integers p
  have hi : ((a⁻¹ : (p.adicCompletion K)ˣ) : p.adicCompletion K) ∈ S := by
    change Valued.v (((a⁻¹ : (p.adicCompletion K)ˣ) : p.adicCompletion K)) ≤ 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, ha, inv_one]
  have hn := LocalNormUnits.norm_eq_one_of_unit_in_compact_subring
    (finitePlaceAboveCompletionMap p w).toMonoidHom
    (finitePlaceAboveCompletionMap_continuous p w) S a ha.le hi
  exact le_antisymm (Valued.toNormedField.norm_le_one_iff.mp hn.le)
    (Valued.toNormedField.one_le_norm_iff.mp hn.ge)

omit [Field E] [NumberField E] [Algebra K E] in
/-- A nonsplit actual quadratic fiber has exactly one place above it,
expressed as subsingletonness together with the already proved nonemptiness. -/
theorem finite_fiber_subsingleton (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 K))
    (hlocal : ¬ IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta)) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    Subsingleton (FinitePlacesAbove (E := QuadraticAlgebra K (theta : K) 0) p) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  let thetap : (p.adicCompletion K)ˣ :=
    Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta
  letI : Fact (∀ r : p.adicCompletion K,
      r ^ 2 ≠ algebraMap K (p.adicCompletion K) (theta : K) + 0 * r) :=
    ⟨nonsquare_quadraticAlgebra_field_fact thetap hlocal⟩
  let e := finiteEquiv theta htheta p
  letI : IsDomain (CompletedExtensionProduct.Product
      (E := QuadraticAlgebra K (theta : K) 0) p) :=
    e.symm.toRingEquiv.toMulEquiv.isDomain _
  exact SplitNormUnits.subsingleton_of_pi_domain
    (fun w : FinitePlacesAbove (E := QuadraticAlgebra K (theta : K) 0) p ↦
      w.1.adicCompletion (QuadraticAlgebra K (theta : K) 0))

omit [Field E] [NumberField E] [Algebra K E] in
/-- A unit target in the actual finite norm image has a preimage which is
a valuation unit in every extension factor, with no good-place hypothesis. -/
theorem exists_unit_preimage (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 K)) (a : (p.adicCompletion K)ˣ)
    (ha : Valued.v (a : p.adicCompletion K) = 1) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    a ∈ (finitePlaceFiberNormUnits (E := QuadraticAlgebra K (theta : K) 0) p).range →
      ∃ z : (w : FinitePlacesAbove (E := QuadraticAlgebra K (theta : K) 0) p) →
          (w.1.adicCompletion (QuadraticAlgebra K (theta : K) 0))ˣ,
        finitePlaceFiberNormUnits p z = a ∧ ∀ w, Valued.v (z w).val = 1 := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  intro hnorm
  let thetap : (p.adicCompletion K)ˣ :=
    Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta
  by_cases hlocal : IsSquare thetap
  · obtain ⟨z, hz, hfield⟩ := SplitNormUnits.exists_split_preimage thetap a hlocal
    let e := finiteEquiv theta htheta p
    let y := MulEquiv.piUnits (Units.map e.toMonoidHom z)
    refine ⟨y, ?_, ?_⟩
    · apply Units.ext
      rw [show ((finitePlaceFiberNormUnits p y : (p.adicCompletion K)ˣ) :
          p.adicCompletion K) = ∏ w, Algebra.norm (p.adicCompletion K) (e z.val w) by
        change ((∏ w, finitePlaceAboveNormUnits p w (y w) : (p.adicCompletion K)ˣ) :
          p.adicCompletion K) = _
        rw [Units.coe_prod]
        rfl]
      rw [← ProductNorm.norm_pi]
      exact (Algebra.norm_eq_of_algEquiv e z.val).trans hz
    · intro w
      let f := (Pi.evalAlgHom (p.adicCompletion K) _ w).comp e.toAlgHom
      rcases hfield _ f with h | h
      · change Valued.v (e z.val w) = 1
        rw [show e z.val w = 1 from h, map_one]
      · change Valued.v (e z.val w) = 1
        rw [show e z.val w = finitePlaceAboveCompletionMap p w a.val from h]
        exact completionMap_valuation_one p w a ha
  · letI := finite_fiber_subsingleton theta htheta p hlocal
    obtain ⟨z, hz⟩ := hnorm
    refine ⟨z, hz, fun w ↦ ?_⟩
    apply (LocalNormReflection.finitePlaceAboveNormUnits_valuation_one_iff p w (z w)).mp
    have hw : finitePlaceAboveNormUnits p w (z w) = a := by
      rw [← hz]
      exact (Fintype.prod_subsingleton (fun v ↦ finitePlaceAboveNormUnits p v (z v)) w).symm
    rw [hw]
    exact ha

end NormEuclidean.CompletedNormUnitLifting
