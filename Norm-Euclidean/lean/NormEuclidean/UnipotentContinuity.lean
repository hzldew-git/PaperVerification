import NormEuclidean.TernaryKernelGeneration
import NormEuclidean.ChapterX.OrthogonalTopology

/-!
# Continuous scalar parameters in both actual unipotent families
-/

noncomputable section

namespace NormEuclidean.UnipotentContinuity

open ProperSpinor TernaryKernelGeneration QuadraticMap OrthogonalTopology
open scoped NormEuclidean.OrthogonalTopology

variable {F E : Type*} [Field F] [CharZero F] [TopologicalSpace F]
  [IsTopologicalRing F] [ContinuousInv₀ F] [AddCommGroup E] [Module F E]
  [FiniteDimensional F E] [TopologicalSpace E] [IsModuleTopology F E]
  (Q : QuadraticForm F E) (hQ : Q.polarBilin.Nondegenerate) (hA : Q.Anisotropic)

/-- The scalar parameter varies continuously, including zero and residue characteristic two. -/
theorem continuous_family (b : Bool) (u : E) :
    Continuous (fun t : F ↦ family Q hQ hA b (t • u)) := by
  letI := IsModuleTopology.topologicalAddGroup F E
  apply (isInducing_properLinearMap (Hyperbolic.form Q)).continuous_iff.mpr
  apply (continuous_end_iff_apply _).mpr
  intro z
  cases b
  · change Continuous (fun t : F ↦
      (HyperbolicUnipotent.element Q hQ hA (t • u)).1.1 z)
    simp only [
      HyperbolicUnipotent.element_apply, Hyperbolic.transvection,
      polar_smul_right, Q.map_smul, smul_eq_mul]
    exact (continuous_const.sub (continuous_const.smul
      (continuous_id.smul continuous_const))).prodMk
      (continuous_const.prodMk ((continuous_const.add
        (continuous_id.mul continuous_const)).sub
          (continuous_const.mul ((continuous_id.mul continuous_id).mul continuous_const))))
  · change Continuous (fun t : F ↦
      (OppositeHyperbolicUnipotent.element Q hQ hA (t • u)).1.1 z)
    simp only [
      OppositeHyperbolicUnipotent.element_apply,
      polar_smul_right, Q.map_smul, smul_eq_mul]
    exact (continuous_const.sub (continuous_const.smul
      (continuous_id.smul continuous_const))).prodMk
      (((continuous_const.add (continuous_id.mul continuous_const)).sub
        (continuous_const.mul ((continuous_id.mul continuous_id).mul continuous_const))).prodMk
          continuous_const)

end NormEuclidean.UnipotentContinuity
