import NormEuclidean.TraceTensorDuality
import NormEuclidean.CompletedIntegerDensity
import ClassFieldTheory.AlgebraicNumberTheory.Completion.AdicCompletionComparison
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# The completed tensor algebra with original number-field completion factors

The separable completion decomposition is transported to the original
adic completions by the proved canonical ring comparisons. All factor
embeddings, traces and topologies are the actual ones. The integral
lattice comparison is a further theorem, not an input to this decomposition.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.CompletedTensorProduct

open NumberField IsDedekindDomain AlgebraicNumberTheory.Valuations
open Bong.NumberFieldCompletion ValuationTheory.Completion
open scoped NumberField TensorProduct

variable (F : Type*) [Field F] [NumberField F]

/-- The rational-place completion in the absolute-value model. -/
abbrev Base (q : HeightOneSpectrum (𝓞 ℚ)) := (HeightOneSpectrum.adicAbv ℚ q).Completion

scoped instance baseRatModule (q : HeightOneSpectrum (𝓞 ℚ)) : Module ℚ (Base q) :=
  (inferInstance : Algebra ℚ (Base q)).toModule

open scoped NormEuclidean.CompletedTensorProduct

/-- All exact extensions of this rational finite absolute value. -/
abbrev Place (q : HeightOneSpectrum (𝓞 ℚ)) :=
  AbsoluteValueExtension (HeightOneSpectrum.adicAbv ℚ q) F

/-- The actual global prime underlying the chosen completion factor. -/
def prime (q : HeightOneSpectrum (𝓞 ℚ)) (w : Place F q) : HeightOneSpectrum (𝓞 F) :=
  finitePlaceExtensionCentre (K := ℚ) (L := F) q w

scoped instance placeFintype (q : HeightOneSpectrum (𝓞 ℚ)) : Fintype (Place F q) :=
  completionTensorDecomposition_extensionFintype (K := ℚ) (L := F)
    (HeightOneSpectrum.adicAbv ℚ q) (RayClass.adicAbv_isNontrivial q)

scoped instance absoluteAlgebra (q : HeightOneSpectrum (𝓞 ℚ)) (w : Place F q) :
    Algebra (Base q) w.1.Completion :=
  AbsoluteValue.completionAlgebra (HeightOneSpectrum.adicAbv ℚ q) w.1 w.2

/-- The coefficient embedding into the original adic completion. -/
@[implicit_reducible]
def coefficientAlgebra (q : HeightOneSpectrum (𝓞 ℚ)) (w : Place F q) :
    Algebra (Base q) ((prime F q w).adicCompletion F) :=
  ((finitePlaceExtensionAdicCompletionRingEquiv (K := ℚ) (L := F) q w).toRingHom.comp
    (AbsoluteValue.completionMap (HeightOneSpectrum.adicAbv ℚ q) w.1 w.2)).toAlgebra

attribute [local instance] coefficientAlgebra

open scoped NormEuclidean.CompletedTensorProduct

/-- The factor comparison is an equivalence over the actual rational-place completion. -/
def factorEquiv (q : HeightOneSpectrum (𝓞 ℚ)) (w : Place F q) :
    w.1.Completion ≃ₐ[Base q] ((prime F q w).adicCompletion F) where
  __ := finitePlaceExtensionAdicCompletionRingEquiv (K := ℚ) (L := F) q w
  commutes' _ := rfl

theorem factorEquiv_coe (q : HeightOneSpectrum (𝓞 ℚ)) (w : Place F q) (x : F) :
    factorEquiv F q w (AbsoluteValue.toCompletion w.1 x) =
      algebraMap F ((prime F q w).adicCompletion F) x :=
  finitePlaceExtensionAdicCompletionRingEquiv_toCompletion q w x

theorem factorEquiv_continuous (q : HeightOneSpectrum (𝓞 ℚ)) (w : Place F q) :
    Continuous (factorEquiv F q w) :=
  (relativeFinitePlaceCompletionRingHom_isometry (prime F q w)).continuous.comp
    (finitePlaceExtensionCompletionRingEquiv_continuous q w)

theorem coefficient_continuous (q : HeightOneSpectrum (𝓞 ℚ)) (w : Place F q) :
    Continuous (algebraMap (Base q) ((prime F q w).adicCompletion F)) :=
  (factorEquiv_continuous F q w).comp
    (AbsoluteValue.completionMap_isometry (HeightOneSpectrum.adicAbv ℚ q) w.1 w.2).continuous

scoped instance factorContinuousSMul (q : HeightOneSpectrum (𝓞 ℚ)) (w : Place F q) :
    ContinuousSMul (Base q) ((prime F q w).adicCompletion F) :=
  continuousSMul_of_algebraMap _ _ (coefficient_continuous F q w)

scoped instance factorFinite (q : HeightOneSpectrum (𝓞 ℚ)) (w : Place F q) :
    Module.Finite (Base q) ((prime F q w).adicCompletion F) := by
  letI := completionModuleFinite (K := ℚ) (L := F)
    (HeightOneSpectrum.adicAbv ℚ q) (RayClass.adicAbv_isNontrivial q) w
  exact Module.Finite.equiv (factorEquiv F q w).toLinearEquiv

/-- The product consists of the original adic completion fields. -/
abbrev Product (q : HeightOneSpectrum (𝓞 ℚ)) :=
  (w : Place F q) → (prime F q w).adicCompletion F

/-- The actual scalar-extension algebra. -/
abbrev Tensor (q : HeightOneSpectrum (𝓞 ℚ)) := Base q ⊗[ℚ] F

/-- The canonical decomposition into original completion fields. -/
def equiv (q : HeightOneSpectrum (𝓞 ℚ)) : Tensor F q ≃ₐ[Base q] Product F q := by
  let e : Tensor F q ≃ₐ[Base q] ((w : Place F q) → w.1.Completion) :=
    completionTensorDecomposition_left (K := ℚ) (L := F)
      (HeightOneSpectrum.adicAbv ℚ q) (RayClass.adicAbv_isNontrivial q)
  exact e.trans (AlgEquiv.piCongrRight fun w ↦ factorEquiv F q w)

theorem equiv_tmul (q : HeightOneSpectrum (𝓞 ℚ)) (a : Base q) (x : F) (w : Place F q) :
    equiv F q (a ⊗ₜ[ℚ] x) w =
      algebraMap (Base q) ((prime F q w).adicCompletion F) a *
        algebraMap F ((prime F q w).adicCompletion F) x := by
  change factorEquiv F q w
    (completionTensorDecomposition_left (K := ℚ) (L := F)
      (HeightOneSpectrum.adicAbv ℚ q) (RayClass.adicAbv_isNontrivial q)
        (a ⊗ₜ[ℚ] x) w) = _
  rw [completionTensorDecomposition_left_tmul_apply, map_mul]
  exact congrArg₂ (· * ·) ((factorEquiv F q w).commutes a) (factorEquiv_coe F q w x)

/-- Actual tensor trace is the sum of actual original completion traces. -/
theorem trace_eq_sum (q : HeightOneSpectrum (𝓞 ℚ)) (x : Tensor F q) :
    Algebra.trace (Base q) (Tensor F q) x =
      ∑ w : Place F q, Algebra.trace (Base q) ((prime F q w).adicCompletion F)
        (equiv F q x w) := by
  rw [← Algebra.trace_eq_of_algEquiv (equiv F q) x, algebra_trace_pi_apply]

/-- Global trace agrees with the sum over all original completed factors. -/
theorem global_trace_eq_sum (q : HeightOneSpectrum (𝓞 ℚ)) (x : F) :
    algebraMap ℚ (Base q) (Algebra.trace ℚ F x) =
      ∑ w : Place F q, Algebra.trace (Base q) ((prime F q w).adicCompletion F)
        (algebraMap F ((prime F q w).adicCompletion F) x) := by
  rw [← TraceTensorDuality.trace_tmul, trace_eq_sum]
  simp only [equiv_tmul, map_one, one_mul]

scoped instance tensorTopology (q : HeightOneSpectrum (𝓞 ℚ)) : TopologicalSpace (Tensor F q) :=
  moduleTopology (Base q) (Tensor F q)

scoped instance tensorTopologicalAddGroup (q : HeightOneSpectrum (𝓞 ℚ)) :
    IsTopologicalAddGroup (Tensor F q) :=
  IsModuleTopology.topologicalAddGroup (Base q) (Tensor F q)

/-- The canonical decomposition is continuous for the finite-dimensional module topology. -/
theorem equiv_continuous (q : HeightOneSpectrum (𝓞 ℚ)) : Continuous (equiv F q) :=
  IsModuleTopology.continuous_of_linearMap (equiv F q).toLinearMap

end NormEuclidean.CompletedTensorProduct
