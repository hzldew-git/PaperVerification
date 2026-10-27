import NormEuclidean.CompletedTensorProduct
import NormEuclidean.CompletedIntegralApproximation
import NormEuclidean.GlobalTraceLattice
import Mathlib.Topology.Algebra.Module.Compact

/-!
# The integral tensor lattice equals the product of original completed integer rings

Compactness of the scalar-extended global integral basis and actual
simultaneous integral approximation prove the comparison at every
prime, including the ramified and dyadic primes. No integral tensor
decomposition or local trace-different equality is supplied as a premise.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.CompletedTensorIntegers

open NumberField IsDedekindDomain Bong.NumberFieldCompletion
open CompletedTensorProduct Set
open scoped NumberField TensorProduct NormEuclidean.CompletedTensorProduct

variable (F : Type*) [Field F] [NumberField F]

attribute [local instance] coefficientAlgebra

def baseEquiv (q : HeightOneSpectrum (𝓞 ℚ)) : Base q ≃+* q.adicCompletion ℚ :=
  relativeFinitePlaceCompletionRingEquiv q

theorem baseEquiv_symm_norm (q : HeightOneSpectrum (𝓞 ℚ)) (x : q.adicCompletion ℚ) :
    ‖(baseEquiv q).symm x‖ = ‖x‖ := by
  have h := relativeFinitePlaceCompletionRingEquiv_norm q ((baseEquiv q).symm x)
  change ‖baseEquiv q ((baseEquiv q).symm x)‖ = _ at h
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

/-- The actual original rational completed integer ring acts on its absolute-value model. -/
@[implicit_reducible]
def baseIntegerAlgebra (q : HeightOneSpectrum (𝓞 ℚ)) : Algebra (integerRing q) (Base q) :=
  ((baseEquiv q).symm.toRingHom.comp (integerRing q).subtype).toAlgebra

attribute [local instance] baseIntegerAlgebra

theorem baseInteger_continuous (q : HeightOneSpectrum (𝓞 ℚ)) :
    Continuous (algebraMap (integerRing q) (Base q)) :=
  (AddMonoidHomClass.isometry_of_norm (baseEquiv q).symm
    (baseEquiv_symm_norm q)).continuous.comp continuous_subtype_val

/-- Integral coefficients act on each original extension completion through its actual base map. -/
@[implicit_reducible]
def factorIntegerAlgebra (q : HeightOneSpectrum (𝓞 ℚ)) (w : Place F q) :
    Algebra (integerRing q) ((prime F q w).adicCompletion F) :=
  ((algebraMap (Base q) ((prime F q w).adicCompletion F)).comp
    (algebraMap (integerRing q) (Base q))).toAlgebra

attribute [local instance] factorIntegerAlgebra

theorem factorIntegerTower (q : HeightOneSpectrum (𝓞 ℚ)) (w : Place F q) :
    IsScalarTower (integerRing q) (Base q) ((prime F q w).adicCompletion F) :=
  IsScalarTower.of_algebraMap_eq' rfl

attribute [local instance] factorIntegerTower

/-- The actual integral coefficients land in each original completed integer ring. -/
theorem coefficient_integral (q : HeightOneSpectrum (𝓞 ℚ)) (w : Place F q)
    (r : integerRing q) :
    algebraMap (integerRing q) ((prime F q w).adicCompletion F) r ∈ integerRing (prime F q w) := by
  apply (finitePlaceExtensionAdicCompletionRingEquiv_mem_integers_iff q w _).mpr
  rw [mem_absoluteValueCompletionIntegers_iff]
  change ‖AbsoluteValue.completionMap (HeightOneSpectrum.adicAbv ℚ q) w.1 w.2
    ((baseEquiv q).symm (r : q.adicCompletion ℚ))‖ ≤ 1
  have hm := AbsoluteValue.completionMap_isometry (HeightOneSpectrum.adicAbv ℚ q) w.1 w.2
  rw [hm.norm_map_of_map_zero (map_zero _), baseEquiv_symm_norm]
  exact norm_le_one_of_mem_adicCompletionIntegers q r.property

scoped instance tensorIntegerContinuousSMul (q : HeightOneSpectrum (𝓞 ℚ)) :
    ContinuousSMul (integerRing q) (Tensor F q) := by
  constructor
  have he : (fun z : integerRing q × Tensor F q ↦ z.1 • z.2) =
      (fun z ↦ (algebraMap (integerRing q) (Base q) z.1) • z.2) :=
    funext fun z ↦ (IsScalarTower.algebraMap_smul (Base q) z.1 z.2).symm
  rw [he]
  exact ((baseInteger_continuous q).comp continuous_fst).smul continuous_snd

open scoped NormEuclidean.CompletedTensorIntegers

/-- The actual product of all original completed integer lattices above the rational place. -/
def integerProduct (q : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule (integerRing q) (Product F q) where
  carrier := {x | ∀ w, x w ∈ integerRing (prime F q w)}
  zero_mem' _ := (integerRing _).zero_mem
  add_mem' hx hy w := (integerRing _).add_mem (hx w) (hy w)
  smul_mem' r x hx w := by
    change algebraMap (integerRing q) ((prime F q w).adicCompletion F) r * x w ∈ _
    exact (integerRing _).mul_mem (coefficient_integral F q w r) (hx w)

/-- The global integral lattice in the actual tensor algebra. -/
def integralLattice (q : HeightOneSpectrum (𝓞 ℚ)) : Submodule (integerRing q) (Tensor F q) :=
  GlobalTraceLattice.extend F (Base q) (integerRing q) (GlobalTraceLattice.integers F)

/-- Its image under the actual canonical decomposition. -/
def integralImage (q : HeightOneSpectrum (𝓞 ℚ)) : Submodule (integerRing q) (Product F q) :=
  (integralLattice F q).map ((equiv F q).toLinearMap.restrictScalars (integerRing q))

theorem integralImage_le (q : HeightOneSpectrum (𝓞 ℚ)) :
    integralImage F q ≤ integerProduct F q := by
  rw [integralImage, Submodule.map_le_iff_le_comap]
  change GlobalTraceLattice.extend F (Base q) (integerRing q)
    (GlobalTraceLattice.integers F) ≤ _
  rw [GlobalTraceLattice.extend, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  change x ∈ (1 : Submodule (𝓞 F) F) at hx
  obtain ⟨a, rfl⟩ := Submodule.mem_one.mp hx
  intro w
  change equiv F q (GlobalTraceLattice.inclusion F (Base q) (algebraMap (𝓞 F) F a)) w ∈ _
  rw [GlobalTraceLattice.inclusion_apply, equiv_tmul, map_one, one_mul]
  exact (integerEmbedding (prime F q w) a).property

/-- Compactness comes from the actual scalar-extended integral basis. -/
theorem integralImage_compact (q : HeightOneSpectrum (𝓞 ℚ)) :
    IsCompact (integralImage F q : Set (Product F q)) := by
  letI := CompletedHaarDensity.completedCompact q
  have hfg : (integralLattice F q).FG := by
    rw [integralLattice, GlobalTraceLattice.extend_integers]
    exact Submodule.fg_span (Set.finite_range _)
  have hc := Submodule.isCompact_of_fg (R := integerRing q) hfg
  rw [integralImage, Submodule.map_coe]
  exact hc.image (equiv_continuous F q)

/-- The integral tensor comparison is proved using compactness and integral Chinese remainders. -/
theorem integralImage_eq (q : HeightOneSpectrum (𝓞 ℚ)) :
    integralImage F q = integerProduct F q := by
  apply le_antisymm (integralImage_le F q)
  intro x hx
  let y : (w : Place F q) → integerRing (prime F q w) := fun w ↦ ⟨x w, hx w⟩
  have hd := CompletedIntegralApproximation.denseRange (prime F q)
    (finitePlaceExtensionCentre_injective (K := ℚ) (L := F) q)
  have hc : IsClosed {z : (w : Place F q) → integerRing (prime F q w) |
      (fun w ↦ (z w : (prime F q w).adicCompletion F)) ∈ integralImage F q} :=
    (integralImage_compact F q).isClosed.preimage
      (continuous_pi fun w ↦ continuous_subtype_val.comp (continuous_apply w))
  refine hd.induction_on
    (p := fun z ↦ (fun w ↦ (z w : (prime F q w).adicCompletion F)) ∈ integralImage F q) y hc ?_
  intro a
  apply Submodule.mem_map.mpr
  refine ⟨GlobalTraceLattice.inclusion F (Base q) (a : F), ?_, ?_⟩
  · apply Submodule.subset_span
    refine ⟨(a : F), ?_, rfl⟩
    exact Submodule.mem_one.mpr ⟨a, rfl⟩
  · funext w
    change equiv F q (1 ⊗ₜ[ℚ] (a : F)) w =
      ((integerEmbedding (prime F q w) a : integerRing (prime F q w)) :
        (prime F q w).adicCompletion F)
    rw [equiv_tmul, map_one, one_mul]
    rfl

end NormEuclidean.CompletedTensorIntegers
