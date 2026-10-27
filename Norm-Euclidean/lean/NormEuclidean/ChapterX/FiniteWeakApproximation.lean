import NormEuclidean.ChapterX.CompletedTopology
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Weak approximation at actual finite completions

The abstract absolute-value weak approximation theorem is connected to
the actual valued completions used by the project. Nontriviality and
inequivalence of distinct prime absolute values are proved here.
This theorem controls finitely many places, without integrality elsewhere.
-/

noncomputable section

namespace NormEuclidean.FiniteWeakApproximation

open IsDedekindDomain CompletedIntegralLattice Filter Topology
open scoped NormEuclidean.OrthogonalTopology
open scoped TensorProduct

variable {K : Type*} [Field K]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]
  [Module.Finite ℤ R] [Module.Free ℤ R]

/-- The prime absolute values used for scalar weak approximation are nontrivial. -/
theorem adicAbv_isNontrivial (v : HeightOneSpectrum R) :
    (NumberField.HeightOneSpectrum.adicAbv K v).IsNontrivial := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hlt : NumberField.HeightOneSpectrum.adicAbv K v (algebraMap R K a) < 1 := by
    have h := (NumberField.FinitePlace.norm_lt_one_iff_mem K v a).mpr ha
    rwa [NumberField.FinitePlace.norm_embedding] at h
  refine ⟨algebraMap R K a, ?_, hlt.ne⟩
  intro hzero
  exact ha0 ((FaithfulSMul.algebraMap_injective R K) (hzero.trans (map_zero _).symm))

/-- Equivalent prime absolute values have the same prime ideal. -/
theorem eq_of_adicAbv_isEquiv {v w : HeightOneSpectrum R}
    (h : (NumberField.HeightOneSpectrum.adicAbv K v).IsEquiv
      (NumberField.HeightOneSpectrum.adicAbv K w)) : v = w := by
  apply HeightOneSpectrum.ext_iff.mpr
  apply Ideal.ext
  intro a
  have hv := NumberField.FinitePlace.norm_lt_one_iff_mem K v a
  have hw := NumberField.FinitePlace.norm_lt_one_iff_mem K w a
  rw [NumberField.FinitePlace.norm_embedding] at hv hw
  exact hv.symm.trans (h.lt_one_iff.trans hw)

/-- The normed absolute-value copy maps to the same actual valued completion. -/
def completionMap (v : HeightOneSpectrum R) :
    WithAbs (NumberField.HeightOneSpectrum.adicAbv K v) →+* LocalField R v :=
  (algebraMap K (LocalField R v)).comp
    (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v)).toRingHom

theorem norm_completionMap (v : HeightOneSpectrum R)
    (x : WithAbs (NumberField.HeightOneSpectrum.adicAbv K v)) :
    ‖completionMap R v x‖ = ‖x‖ := by
  change ‖NumberField.FinitePlace.embedding v
    (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v) x)‖ = ‖x‖
  rw [NumberField.FinitePlace.norm_embedding]
  rfl

theorem isometry_completionMap (v : HeightOneSpectrum R) : Isometry (completionMap R v) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm_sub, dist_eq_norm_sub, ← map_sub, norm_completionMap]

theorem denseRange_completionMap (v : HeightOneSpectrum R) :
    DenseRange (completionMap R v) := by
  have hr : Set.range (algebraMap K (LocalField R v)) ⊆ Set.range (completionMap R v) := by
    rintro _ ⟨x, rfl⟩
    refine ⟨(WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v)).symm x, ?_⟩
    change algebraMap K (LocalField R v)
      (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v)
        ((WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v)).symm x)) = _
    rfl
  intro y
  exact closure_mono hr (HeightOneSpectrum.denseRange_algebraMap (K := K) v y)

/-- Scalar weak approximation for any finite set of actual finite places,
including dyadic places. No simultaneous density premise is supplied. -/
theorem denseRange_finite_diagonal (T : Finset (HeightOneSpectrum R)) :
    DenseRange (fun x : K ↦ fun v : T ↦ algebraMap K (LocalField R v.1) x) := by
  let w : T → AbsoluteValue K ℝ := fun v ↦ NumberField.HeightOneSpectrum.adicAbv K v.1
  have hn : ∀ v : T, (w v).IsNontrivial := fun v ↦ adicAbv_isNontrivial R v.1
  have he : Pairwise fun v u : T ↦ ¬ (w v).IsEquiv (w u) := by
    intro v u hvu h
    exact hvu (Subtype.ext (eq_of_adicAbv_isEquiv R h))
  have hd := AbsoluteValue.denseRange_algebraMap_pi hn he
  have hp : DenseRange (Pi.map (fun v : T ↦ completionMap R v.1)) :=
    DenseRange.piMap (fun v ↦ denseRange_completionMap R v.1)
  have hc : Continuous (Pi.map (fun v : T ↦ completionMap R v.1)) :=
    continuous_pi (fun v ↦ (isometry_completionMap R v.1).continuous.comp (continuous_apply v))
  convert hp.comp hd hc using 1
  funext x v
  rfl

section Vectors

open OrthogonalTopology

variable {V ι : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Fintype ι]

omit [Module.Finite ℤ R] [Module.Free ℤ R] [FiniteDimensional K V] in
theorem baseChange_equivFun_inclusion (b : Module.Basis ι K V) (v : HeightOneSpectrum R)
    (x : V) :
    (b.baseChange (LocalField R v)).equivFun (inclusion R v x) =
      fun i ↦ algebraMap K (LocalField R v) (b.equivFun x i) := by
  funext i
  change (b.baseChange (LocalField R v)).repr (1 ⊗ₜ[K] x) i =
    algebraMap K (LocalField R v) (b.repr x i)
  rw [Module.Basis.baseChange_repr_tmul]
  simp only [Algebra.smul_def, mul_one]

omit [Module.Finite ℤ R] [Module.Free ℤ R] [FiniteDimensional K V] in
theorem inclusion_equivFun_symm (b : Module.Basis ι K V) (v : HeightOneSpectrum R)
    (c : ι → K) :
    inclusion R v (b.equivFun.symm c) =
      (b.baseChange (LocalField R v)).equivFun.symm
        (fun i ↦ algebraMap K (LocalField R v) (c i)) := by
  apply (b.baseChange (LocalField R v)).equivFun.injective
  rw [baseChange_equivFun_inclusion, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

omit [FiniteDimensional K V] in
/-- Weak approximation in the actual tensor-product vector spaces follows
coordinatewise from the proved scalar theorem. The basis is a field basis. -/
theorem denseRange_inclusion_of_basis (b : Module.Basis ι K V)
    (T : Finset (HeightOneSpectrum R)) :
    DenseRange (fun x : V ↦ fun v : T ↦ inclusion R v.1 x) := by
  let dc : (ι → K) → (ι → ((v : T) → LocalField R v.1)) :=
    fun c i v ↦ algebraMap K (LocalField R v.1) (c i)
  have hdc : DenseRange dc := DenseRange.piMap (fun _ ↦ denseRange_finite_diagonal R T)
  let h : (ι → ((v : T) → LocalField R v.1)) → ((v : T) → Space (V := V) R v.1) :=
    fun c v ↦ (b.baseChange (LocalField R v.1)).equivFun.symm (fun i ↦ c i v)
  have hs : Function.Surjective h := by
    intro z
    refine ⟨fun i v ↦ (b.baseChange (LocalField R v.1)).equivFun (z v) i, ?_⟩
    funext v
    exact LinearEquiv.symm_apply_apply _ (z v)
  have hc : Continuous h := continuous_pi (fun v ↦
    (basisHomeomorph (b.baseChange (LocalField R v.1))).symm.continuous.comp
      (continuous_pi (fun i ↦ (continuous_apply v).comp (continuous_apply i))))
  let d : (ι → K) → ((v : T) → Space (V := V) R v.1) :=
    fun c v ↦ inclusion R v.1 (b.equivFun.symm c)
  have hd : DenseRange d := by
    convert hs.denseRange.comp hdc hc using 1
    funext c v
    exact inclusion_equivFun_symm R b v.1 c
  have hr : Set.range d ⊆ Set.range (fun x : V ↦ fun v : T ↦ inclusion R v.1 x) := by
    rintro _ ⟨c, rfl⟩
    exact ⟨b.equivFun.symm c, rfl⟩
  intro z
  exact closure_mono hr (hd z)

/-- Simultaneous weak approximation for arbitrary finite-dimensional
vectors, with the actual completion topologies and no chosen-basis premise. -/
theorem denseRange_inclusion (T : Finset (HeightOneSpectrum R)) :
    DenseRange (fun x : V ↦ fun v : T ↦ inclusion R v.1 x) := by
  let b := Module.Free.chooseBasis K V
  letI := Module.Finite.finite_basis b
  letI := Fintype.ofFinite (Module.Free.ChooseBasisIndex K V)
  exact denseRange_inclusion_of_basis R b T

end Vectors

section NumberField

variable [NumberField K]

theorem numberField_denseRange_finite_diagonal
    (T : Finset (HeightOneSpectrum (integerSubring K))) :
    DenseRange (fun x : K ↦ fun v : T ↦ algebraMap K (LocalField (integerSubring K) v.1) x) := by
  letI : Module.Finite ℤ (integerSubring K) :=
    inferInstanceAs (Module.Finite ℤ (NumberField.RingOfIntegers K))
  letI : Module.Free ℤ (integerSubring K) :=
    inferInstanceAs (Module.Free ℤ (NumberField.RingOfIntegers K))
  exact denseRange_finite_diagonal (integerSubring K) T

theorem numberField_denseRange_inclusion {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Finset (HeightOneSpectrum (integerSubring K))) :
    DenseRange (fun x : V ↦ fun v : T ↦ inclusion (integerSubring K) v.1 x) := by
  letI : Module.Finite ℤ (integerSubring K) :=
    inferInstanceAs (Module.Finite ℤ (NumberField.RingOfIntegers K))
  letI : Module.Free ℤ (integerSubring K) :=
    inferInstanceAs (Module.Free ℤ (NumberField.RingOfIntegers K))
  exact denseRange_inclusion (integerSubring K) T

end NumberField

end NormEuclidean.FiniteWeakApproximation
