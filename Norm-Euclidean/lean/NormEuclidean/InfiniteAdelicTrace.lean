import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import Mathlib.RingTheory.Trace.Basic

/-!
# The actual archimedean trace and its global diagonal comparison

Real places have multiplicity one; complex places contribute twice
the real part. Grouping the actual complex embeddings by infinite
place proves the global trace identity for arbitrary number fields.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.InfiniteAdelicTrace

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField Classical

variable {F : Type*} [Field F] [NumberField F]

/-- The actual archimedean local trace, with the correct complex multiplicity. -/
def localTrace (w : InfinitePlace F) : w.Completion →+ ℝ where
  toFun z := (w.mult : ℝ) * (extensionEmbedding w z).re
  map_zero' := by simp
  map_add' x y := by simp [mul_add]

theorem localTrace_continuous (w : InfinitePlace F) : Continuous (localTrace w) :=
  continuous_const.mul (Complex.continuous_re.comp (isometry_extensionEmbedding w).continuous)

theorem localTrace_diagonal (w : InfinitePlace F) (x : F) :
    localTrace w (algebraMap F w.Completion x) = (w.mult : ℝ) * (w.embedding x).re := by
  change (w.mult : ℝ) *
    (extensionEmbedding w ((WithAbs.equiv w.1).symm x : w.Completion)).re = _
  rw [extensionEmbedding_coe, RingEquiv.apply_symm_apply]

/-- The continuous actual trace on the full infinite adele ring. -/
def trace : InfiniteAdeleRing F →+ ℝ where
  toFun a := ∑ w : InfinitePlace F, localTrace w (a w)
  map_zero' := by
    change (∑ w : InfinitePlace F, localTrace w 0) = 0
    simp
  map_add' a b := by
    change (∑ w : InfinitePlace F, localTrace w (a w + b w)) = _
    simp only [map_add, Finset.sum_add_distrib]

theorem trace_continuous : Continuous (trace (F := F)) := by
  apply continuous_finsetSum
  intro w _
  exact (localTrace_continuous w).comp (continuous_apply w)

/-- Embeddings giving the same infinite place have the same real part. -/
theorem embedding_re_eq (w : InfinitePlace F) (φ : F →+* ℂ) (hφ : mk φ = w) (x : F) :
    (φ x).re = (w.embedding x).re := by
  rcases mk_eq_iff.mp (hφ.trans (mk_embedding w).symm) with h | h
  · rw [h]
  · rw [← h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]

/-- The sum over actual infinite places, including complex multiplicities, is the global trace. -/
theorem sum_local_trace (x : F) :
    (∑ w : InfinitePlace F, (w.mult : ℝ) * (w.embedding x).re) =
      (Algebra.trace ℚ F x : ℝ) := by
  have he : (∑ φ : F →+* ℂ, (φ x).re) = (Algebra.trace ℚ F x : ℝ) := by
    calc
      _ = ∑ φ : F →ₐ[ℚ] ℂ, (φ x).re :=
        Fintype.sum_equiv RingHom.equivRatAlgHom _ _ fun _ ↦ rfl
      _ = _ := by
        have h := congrArg Complex.re
          (trace_eq_sum_embeddings ℂ (K := ℚ) (L := F) (x := x))
        have hs : (∑ φ : F →ₐ[ℚ] ℂ, φ x).re = ∑ φ : F →ₐ[ℚ] ℂ, (φ x).re :=
          map_sum Complex.reAddGroupHom _ _
        have hr : ((algebraMap ℚ ℂ) (Algebra.trace ℚ F x)).re =
            (Algebra.trace ℚ F x : ℝ) := by simp
        exact hs.symm.trans (h.symm.trans hr)
  rw [← he, ← Finset.sum_fiberwise Finset.univ mk (fun φ : F →+* ℂ ↦ (φ x).re)]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.sum_congr rfl (fun φ hφ ↦ embedding_re_eq w φ (Finset.mem_filter.mp hφ).2 x),
    Finset.sum_const, nsmul_eq_mul, card_filter_mk_eq]

/-- The actual infinite adelic trace agrees with the original global trace on principal adeles. -/
theorem diagonal (x : F) :
    trace (algebraMap F (InfiniteAdeleRing F) x) = (Algebra.trace ℚ F x : ℝ) := by
  change (∑ w : InfinitePlace F, localTrace w (algebraMap F w.Completion x)) = _
  simp_rw [localTrace_diagonal]
  exact sum_local_trace x

end NormEuclidean.InfiniteAdelicTrace
