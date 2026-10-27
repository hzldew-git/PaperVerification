import NormEuclidean.MixedTracePairing

/-!
# Actual rational bases and their archimedean trace duals

Every rational basis of the original number field becomes a real basis
under the mixed embedding. The archimedean trace dual basis is proved
to consist of the images of the actual algebraic trace dual basis.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.MixedTraceBasis

open NumberField NumberField.mixedEmbedding Module
open MixedTracePairing
open scoped NumberField Classical

variable (F : Type*) [Field F] [NumberField F]
variable {ι : Type*} [Fintype ι] (b : Basis ι ℚ F)

/-- Extend the actual mixed images of a rational basis to a real basis. -/
def realBasis : Basis ι ℝ (mixedSpace F) := by
  let e : Free.ChooseBasisIndex ℤ (𝓞 F) ≃ ι := Fintype.equivOfCardEq (by
    rw [← finrank_eq_card_chooseBasisIndex, NumberField.RingOfIntegers.rank,
      finrank_eq_card_basis b])
  let B := (latticeBasis F).reindex e
  have hdet : B.det (fun i ↦ mixedEmbedding F (b i)) =
      (((integralBasis F).reindex e).det b : ℝ) := by
    rw [Basis.det_apply, Basis.det_apply]
    change _ = algebraMap ℚ ℝ (((integralBasis F).reindex e).toMatrix b).det
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp only [B, Basis.toMatrix_apply, Basis.repr_reindex_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, latticeBasis_repr_apply, eq_ratCast]
  have hunit : IsUnit (B.det (fun i ↦ mixedEmbedding F (b i))) := by
    rw [hdet, isUnit_iff_ne_zero, Rat.cast_ne_zero]
    exact (((integralBasis F).reindex e).isUnit_det b).ne_zero
  have hb := B.is_basis_iff_det.mpr hunit
  exact Basis.mk hb.1 (by rw [hb.2])

@[simp]
theorem realBasis_apply (i : ι) : realBasis F b i = mixedEmbedding F (b i) := by
  simp only [realBasis, Basis.coe_mk]

/-- Rational coordinates in the original basis become their literal real casts. -/
theorem realBasis_repr (x : F) (i : ι) :
    (realBasis F b).repr (mixedEmbedding F x) i = (b.repr x i : ℝ) := by
  have hx : mixedEmbedding F x =
      ∑ j, ((b.repr x j : ℝ) • realBasis F b j) := by
    conv_lhs => rw [← b.sum_repr x, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [realBasis_apply, map_rat_smul]
    rfl
  rw [hx, map_sum]
  simp only [map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
  simp

/-- Archimedean and algebraic trace dual bases agree on actual vectors. -/
theorem dualBasis_eq :
    (form F).dualBasis (nondegenerate F) (realBasis F b) = realBasis F b.traceDual := by
  have he : ((form F).dualBasis (nondegenerate F) (realBasis F b) : ι → mixedSpace F) =
      fun i ↦ mixedEmbedding F (b.traceDual i) := by
    apply ((form F).dualBasis_eq_iff (nondegenerate F) (realBasis F b) _).mpr
    intro i j
    rw [realBasis_apply, diagonal, b.trace_traceDual_mul]
    by_cases h : j = i <;> simp [h]
  apply DFunLike.ext
  intro i
  rw [realBasis_apply]
  exact congrFun he i

/-- Dualizing an integer span in the mixed space transports the actual trace dual basis. -/
theorem dual_span :
    (form F).dualSubmodule (Submodule.span ℤ (Set.range (realBasis F b))) =
      Submodule.span ℤ (Set.range (realBasis F b.traceDual)) := by
  rw [LinearMap.BilinForm.dualSubmodule_span_of_basis _ (nondegenerate F), dualBasis_eq]

/-- Coordinates in the actual dual basis are the original mixed trace pairings. -/
theorem dual_repr (x : mixedSpace F) (i : ι) :
    (realBasis F b.traceDual).repr x i = form F x (mixedEmbedding F (b i)) := by
  rw [← dualBasis_eq, LinearMap.BilinForm.dualBasis_repr_apply, realBasis_apply]

end NormEuclidean.MixedTraceBasis
