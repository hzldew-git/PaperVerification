import NormEuclidean.ChapterX.RealResidualValues
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# Residual value neighborhoods at actual infinite completions

The real and complex comparison maps are the proved isomorphisms of the
actual infinite completions. Square-root rescaling constructs the vectors;
no archimedean value-set or local representation law is an input.
-/

noncomputable section

namespace NormEuclidean.ArchimedeanResidualValues

open Filter Topology

variable {F E : Type*} [Field F] [AddCommGroup E] [Module F E]

/-- A real comparison map transfers a nonnegative value ratio to an actual
represented vector in the original space. -/
theorem represents_of_nonnegative_ratio (Q : QuadraticForm F E) (e : F ≃+* ℝ)
    (x : E) (hx : Q x ≠ 0) (t : F) (ht : 0 ≤ e (t / Q x)) :
    ∃ y : E, Q y = t := by
  let s := e.symm (Real.sqrt (e (t / Q x)))
  have hs : s ^ 2 = t / Q x := by
    apply e.injective
    simp only [map_pow, s, RingEquiv.apply_symm_apply, Real.sq_sqrt ht]
  refine ⟨s • x, ?_⟩
  rw [Q.map_smul, smul_eq_mul, ← pow_two, hs, div_mul_cancel₀ _ hx]

/-- A nonzero complex quadratic value suffices to represent every scalar,
using an actual square root in the comparison field. -/
theorem represents_of_complex_comparison (Q : QuadraticForm F E) (e : F ≃+* ℂ)
    (x : E) (hx : Q x ≠ 0) (t : F) : ∃ y : E, Q y = t := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (e (t / Q x)) (by decide : 0 < 2)
  have hsF : e.symm s ^ 2 = t / Q x := by
    apply e.injective
    simpa only [map_pow, RingEquiv.apply_symm_apply] using hs
  refine ⟨e.symm s • x, ?_⟩
  rw [Q.map_smul, smul_eq_mul, ← pow_two, hsF, div_mul_cancel₀ _ hx]

variable [TopologicalSpace F] [IsTopologicalRing F]

/-- At a real completion, a nonzero value supplies a whole residual-value
neighborhood centered at zero or at twice the inverse denominator. -/
theorem exists_real_residual_neighborhood (Q : QuadraticForm F E) (e : F ≃+* ℝ)
    (he : Continuous e) (x : E) (hx : Q x ≠ 0) (a : F) (ha : a ≠ 0)
    (c : F) (hc : c ≠ 0) :
    ∃ (t : F) (A : Set F), A ∈ 𝓝 t ∧
      ∀ β ∈ A, ∃ y : E, Q y = a * (1 - c ^ 2 * β ^ 2) := by
  let f (β : F) := e (a * (1 - c ^ 2 * β ^ 2) / Q x)
  have hf : Continuous f := by
    apply he.comp
    exact (continuous_const.mul (continuous_const.sub
      (continuous_const.mul (continuous_id.pow 2)))).div_const _
  have hr : e (a / Q x) ≠ 0 := (map_ne_zero e).mpr (div_ne_zero ha hx)
  by_cases hpos : 0 < e (a / Q x)
  · have hcenter : 0 < f 0 := by simpa only [f, zero_pow (by decide : 2 ≠ 0),
      mul_zero, sub_zero, mul_one] using hpos
    refine ⟨0, {β | 0 < f β}, (isOpen_Ioi.preimage hf).mem_nhds hcenter, ?_⟩
    intro β hβ
    exact represents_of_nonnegative_ratio Q e x hx _ hβ.le
  · have hneg : e (a / Q x) < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hr
    have hcenter : f (2 / c) = -3 * e (a / Q x) := by
      dsimp only [f]
      have h : a * (1 - c ^ 2 * (2 / c) ^ 2) / Q x = -3 * (a / Q x) := by
        field_simp
        <;> ring
      have hthree : e (3 : F) = 3 := map_ofNat e 3
      rw [h, map_mul, map_neg, hthree]
    have hcenterpos : 0 < f (2 / c) := by rw [hcenter]; nlinarith
    refine ⟨2 / c, {β | 0 < f β},
      (isOpen_Ioi.preimage hf).mem_nhds hcenterpos, ?_⟩
    intro β hβ
    exact represents_of_nonnegative_ratio Q e x hx _ hβ.le

section Infinite

variable {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
variable [Invertible (2 : K)]
open scoped TensorProduct
open NumberField.InfinitePlace

/-- Any nonzero global represented value supplies actual residual-value
neighborhoods at every infinite completion, including complex places. -/
theorem exists_completed_residual_neighborhood (Q : QuadraticForm K V)
    (x : V) (hx : Q x ≠ 0) (a c : K) (ha : a ≠ 0) (hc : c ≠ 0)
    (w : NumberField.InfinitePlace K) :
    ∃ (t : w.Completion) (A : Set w.Completion), A ∈ 𝓝 t ∧
      ∀ β ∈ A, ∃ y, Q.baseChange w.Completion y =
        algebraMap K w.Completion a *
          (1 - (algebraMap K w.Completion c) ^ 2 * β ^ 2) := by
  let y := (1 : w.Completion) ⊗ₜ[K] x
  have hy : Q.baseChange w.Completion y ≠ 0 := by
    simpa only [y, QuadraticForm.baseChange_tmul, Algebra.smul_def, mul_one, one_mul]
      using (map_ne_zero (algebraMap K w.Completion)).mpr hx
  rcases w.isReal_or_isComplex with hw | hw
  · exact exists_real_residual_neighborhood (Q.baseChange w.Completion)
      (Completion.ringEquivRealOfIsReal hw)
      (Completion.isometryEquivRealOfIsReal hw).continuous y hy
      (algebraMap K w.Completion a) ((map_ne_zero _).mpr ha)
      (algebraMap K w.Completion c) ((map_ne_zero _).mpr hc)
  · exact ⟨0, Set.univ, Filter.univ_mem, fun β _ ↦
      represents_of_complex_comparison _ (Completion.ringEquivComplexOfIsComplex hw) y hy _⟩

end Infinite

end NormEuclidean.ArchimedeanResidualValues
