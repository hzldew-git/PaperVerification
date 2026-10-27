import NormEuclidean.ChapterX.ExtensionNormComponents
import NormEuclidean.ChapterX.FiniteWeakApproximation

/-!
# The actual product comparison for completed number-field extensions

The canonical map from the scalar extension into all completion factors
above a finite base place is constructed as an algebra map. Weak approximation
and finite-dimensional closedness prove surjectivity. Injectivity and the
local-degree equality are not assumed or inferred from this argument.
-/

noncomputable section

namespace NormEuclidean.CompletedExtensionProduct

open IsDedekindDomain ExtensionIdeleNorm
open scoped NumberField TensorProduct WithZero

universe u
variable {K E : Type u} [Field K] [NumberField K]
  [Field E] [NumberField E] [Algebra K E]

scoped instance componentAlgebra (p : HeightOneSpectrum (𝓞 K))
    (w : FinitePlacesAbove (E := E) p) :
    Algebra (p.adicCompletion K) (w.1.adicCompletion E) := finitePlaceAboveAlgebra p w

scoped instance componentContinuousSMul (p : HeightOneSpectrum (𝓞 K))
    (w : FinitePlacesAbove (E := E) p) :
    ContinuousSMul (p.adicCompletion K) (w.1.adicCompletion E) :=
  ⟨((finitePlaceAboveCompletionMap_continuous p w).comp continuous_fst).mul continuous_snd⟩

scoped instance componentTower (p : HeightOneSpectrum (𝓞 K))
    (w : FinitePlacesAbove (E := E) p) :
    IsScalarTower K (p.adicCompletion K) (w.1.adicCompletion E) := by
  letI : w.1.asIdeal.LiesOver p.asIdeal :=
    ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩
  exact ExtensionPlaces.finitePlaceCompletion_isScalarTower p w.1

scoped instance componentFinite (p : HeightOneSpectrum (𝓞 K))
    (w : FinitePlacesAbove (E := E) p) :
    Module.Finite (p.adicCompletion K) (w.1.adicCompletion E) :=
  finitePlaceAbove_moduleFinite p w

/-- The product of all actual extension completions above a fixed finite place. -/
abbrev Product (p : HeightOneSpectrum (𝓞 K)) :=
  (w : FinitePlacesAbove (E := E) p) → w.1.adicCompletion E

/-- The canonical algebra map into all factors above the finite base place. -/
def comparison (p : HeightOneSpectrum (𝓞 K)) :
    p.adicCompletion K ⊗[K] E →ₐ[p.adicCompletion K] Product (E := E) p :=
  AlgHom.pi fun w ↦ Algebra.TensorProduct.lift
    (Algebra.algHom (p.adicCompletion K) (p.adicCompletion K) (w.1.adicCompletion E))
    (Algebra.algHom K E (w.1.adicCompletion E)) (fun _ _ ↦ mul_comm ..)

/-- On a pure tensor, comparison is the expected product of the two embeddings. -/
theorem comparison_tmul (p : HeightOneSpectrum (𝓞 K)) (a : p.adicCompletion K) (x : E)
    (w : FinitePlacesAbove (E := E) p) :
    comparison p (a ⊗ₜ[K] x) w =
      finitePlaceAboveCompletionMap p w a * algebraMap E (w.1.adicCompletion E) x := by
  change algebraMap (p.adicCompletion K) (w.1.adicCompletion E) a *
    algebraMap E (w.1.adicCompletion E) x = _
  rfl

/-- Weak approximation for the diagonal of the extension field into the entire fiber. -/
theorem denseRange_diagonal (p : HeightOneSpectrum (𝓞 K)) :
    DenseRange (fun x : E ↦ fun w : FinitePlacesAbove (E := E) p ↦
      algebraMap E (w.1.adicCompletion E) x) := by
  let v : FinitePlacesAbove (E := E) p → AbsoluteValue E ℝ :=
    fun w ↦ NumberField.HeightOneSpectrum.adicAbv E w.1
  have hn : ∀ w, (v w).IsNontrivial := by
    intro w
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.1.ne_bot
    have hlt : v w (algebraMap (𝓞 E) E a) < 1 := by
      have h := (NumberField.FinitePlace.norm_lt_one_iff_mem E w.1 a).mpr ha
      rwa [NumberField.FinitePlace.norm_embedding] at h
    refine ⟨algebraMap (𝓞 E) E a, ?_, hlt.ne⟩
    intro hz
    exact ha0 ((FaithfulSMul.algebraMap_injective (𝓞 E) E)
      (hz.trans (map_zero _).symm))
  have he : Pairwise fun w z ↦ ¬ (v w).IsEquiv (v z) := by
    intro w z hwz h
    apply hwz
    apply Subtype.ext
    apply HeightOneSpectrum.ext_iff.mpr
    apply Ideal.ext
    intro a
    have hw := NumberField.FinitePlace.norm_lt_one_iff_mem E w.1 a
    have hz := NumberField.FinitePlace.norm_lt_one_iff_mem E z.1 a
    rw [NumberField.FinitePlace.norm_embedding] at hw hz
    exact hw.symm.trans (h.lt_one_iff.trans hz)
  have hd := AbsoluteValue.denseRange_algebraMap_pi hn he
  let f (w : FinitePlacesAbove (E := E) p) : WithAbs (v w) →+* w.1.adicCompletion E :=
    (algebraMap E (w.1.adicCompletion E)).comp (WithAbs.equiv (v w)).toRingHom
  have hf (w : FinitePlacesAbove (E := E) p) : Isometry (f w) := by
    apply Isometry.of_dist_eq
    intro x y
    rw [dist_eq_norm_sub, dist_eq_norm_sub, ← map_sub]
    exact NumberField.FinitePlace.norm_embedding w.1 _
  have hfd (w : FinitePlacesAbove (E := E) p) : DenseRange (f w) := by
    apply (HeightOneSpectrum.denseRange_algebraMap (K := E) w.1).mono
    rintro _ ⟨x, rfl⟩
    exact ⟨(WithAbs.equiv (v w)).symm x, rfl⟩
  have hp := DenseRange.piMap hfd
  have hc : Continuous (Pi.map (fun w ↦ f w)) :=
    continuous_pi (fun w ↦ (hf w).continuous.comp (continuous_apply w))
  convert hp.comp hd hc using 1
  funext x w
  rfl

/-- The comparison map has dense image in the actual product. -/
theorem comparison_denseRange (p : HeightOneSpectrum (𝓞 K)) :
    DenseRange (comparison (E := E) p) := by
  apply (denseRange_diagonal (E := E) p).mono
  rintro _ ⟨x, rfl⟩
  refine ⟨1 ⊗ₜ[K] x, ?_⟩
  funext w
  simp [comparison_tmul]

/-- Weak approximation and closedness give surjectivity, without a degree or
injectivity premise. This theorem does not assert an algebra equivalence. -/
theorem comparison_surjective (p : HeightOneSpectrum (𝓞 K)) :
    Function.Surjective (comparison (E := E) p) := by
  letI : NontriviallyNormedField (p.adicCompletion K) :=
    Valued.toNontriviallyNormedField (p.adicCompletion K) ℤᵐ⁰
  rw [← Set.range_eq_univ]
  have hclosed : IsClosed (Set.range (comparison (E := E) p)) := by
    change IsClosed ((comparison (E := E) p).toLinearMap.range : Set (Product (E := E) p))
    exact (comparison p).toLinearMap.range.closed_of_finiteDimensional
  exact hclosed.closure_eq.symm.trans (comparison_denseRange (E := E) p).closure_range

/-- In particular the sum of the local degrees is at most the global extension degree.
The reverse inequality, and hence equality, require a separate argument. -/
theorem local_degrees_le (p : HeightOneSpectrum (𝓞 K)) :
    (∑ w : FinitePlacesAbove (E := E) p,
      Module.finrank (p.adicCompletion K) (w.1.adicCompletion E)) ≤ Module.finrank K E := by
  have h := LinearMap.finrank_le_finrank_of_surjective
    (f := (comparison (E := E) p).toLinearMap) (comparison_surjective p)
  simpa only [Product, Module.finrank_pi_fintype, Module.finrank_baseChange] using h

end NormEuclidean.CompletedExtensionProduct
