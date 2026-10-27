import NormEuclidean.ChapterX.CompletionHensel
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Continuous field norms preserve local units

The powers of an element of a compact multiplicative set stay bounded after
any continuous multiplicative map to a normed field. Applied to the determinant
norm and the compact completed valuation ring, this supplies the local unit
property needed to assemble an extension idèle norm. No Hasse principle or
norm-index formula is an input.
-/

noncomputable section

namespace NormEuclidean.LocalNormUnits

/-- A continuous multiplicative map is norm bounded by one on a compact submonoid. -/
theorem norm_le_one_on_compact_submonoid
    {M F : Type*} [Monoid M] [TopologicalSpace M] [NormedField F]
    (f : M →* F) (hf : Continuous f) (S : Submonoid M)
    (hS : IsCompact (S : Set M)) {x : M} (hx : x ∈ S) : ‖f x‖ ≤ 1 := by
  obtain ⟨C, hC⟩ := hS.bddAbove_image hf.norm.continuousOn
  by_contra! h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
  have hbound := hC ⟨x ^ n, S.pow_mem hx n, rfl⟩
  dsimp only at hbound
  rw [map_pow, norm_pow] at hbound
  exact (not_le_of_gt hn) hbound

/-- The determinant norm is continuous in a finite-dimensional topological field extension. -/
theorem continuous_algebra_norm
    {F E : Type*} [NontriviallyNormedField F] [CompleteSpace F]
    [Field E] [TopologicalSpace E] [IsTopologicalRing E] [T2Space E]
    [Algebra F E] [ContinuousSMul F E] [FiniteDimensional F E] :
    Continuous (Algebra.norm F : E → F) := by
  let b := Module.finBasis F E
  change Continuous fun x : E ↦ Algebra.norm F x
  simp_rw [Algebra.norm_eq_matrix_det b]
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [Algebra.leftMulMatrix_eq_repr_mul]
  have hcoord : Continuous (fun x : E ↦ b.repr x i) :=
    (b.coord i).continuous_of_finiteDimensional
  exact hcoord.comp (continuous_id.mul continuous_const)

/-- If a unit and its inverse belong to a compact subring, their multiplicative image
has norm exactly one. No relation between normalizations of the two fields is needed. -/
theorem norm_eq_one_of_unit_in_compact_subring
    {E F : Type*} [Field E] [TopologicalSpace E] [NormedField F]
    (f : E →* F) (hf : Continuous f) (S : Subring E) [CompactSpace S]
    (z : Eˣ) (hz : (z : E) ∈ S) (hzinv : ((z⁻¹ : Eˣ) : E) ∈ S) :
    ‖f (z : E)‖ = 1 := by
  have hS : IsCompact (S : Set E) := isCompact_iff_compactSpace.mpr inferInstance
  have hle := norm_le_one_on_compact_submonoid f hf S.toSubmonoid hS hz
  have hile := norm_le_one_on_compact_submonoid f hf S.toSubmonoid hS hzinv
  have hmul : f (z : E) * f ((z⁻¹ : Eˣ) : E) = 1 := by
    rw [← map_mul]
    simp
  have hnorm : ‖f (z : E)‖ * ‖f ((z⁻¹ : Eˣ) : E)‖ = 1 := by
    rw [← norm_mul, hmul, norm_one]
  apply le_antisymm hle
  calc
    1 = ‖f (z : E)‖ * ‖f ((z⁻¹ : Eˣ) : E)‖ := hnorm.symm
    _ ≤ ‖f (z : E)‖ * 1 := mul_le_mul_of_nonneg_left hile (norm_nonneg _)
    _ = ‖f (z : E)‖ := mul_one _

end NormEuclidean.LocalNormUnits
