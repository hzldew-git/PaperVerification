import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.GroupTheory.Index

/-!
# Normalized invariant measure and actual finite congruence counts

A surjective additive map to a finite group has equimeasurable fibers.
For a normalized invariant measure their measure is exactly the reciprocal
of the actual quotient order. Every congruence locus is therefore counted
with its literal cardinality. No orthogonal-group measure or global mass
identity is asserted by this additive normalization theorem.
-/

noncomputable section

namespace NormEuclidean.UniformCongruenceMeasure

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

variable {G H : Type*} [AddGroup G] [AddGroup H] [Finite H]
  [MeasurableSpace G] [MeasurableAdd G]
variable (μ : Measure G) [IsAddLeftInvariant μ] [IsProbabilityMeasure μ]
variable (f : G →+ H) (hf : Function.Surjective f) (hk : MeasurableSet (f.ker : Set G))

/-- Translation identifies each actual quotient fiber with the actual additive kernel. -/
theorem fiber_translate (a : G) :
    f ⁻¹' {f a} = (fun x : G ↦ -a + x) ⁻¹' (f.ker : Set G) := by
  ext x
  change f x = f a ↔ f (-a + x) = 0
  rw [map_add, map_neg, neg_add_eq_zero]
  exact eq_comm

include hf hk

/-- All fibers are measurable once the actual congruence kernel is measurable. -/
theorem fiber_measurable (h : H) : MeasurableSet (f ⁻¹' {h}) := by
  obtain ⟨a, rfl⟩ := hf h
  rw [fiber_translate f a]
  exact hk.preimage (measurable_const_add (-a))

/-- The normalized invariant measure of the actual kernel is the reciprocal quotient order. -/
theorem kernel_measure : μ (f.ker : Set G) = (Nat.card H : ℝ≥0∞)⁻¹ := by
  have hi : f.ker.index = Nat.card H := by
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hf]
    exact Nat.card_congr (AddSubgroup.topEquiv : (⊤ : AddSubgroup H) ≃+ H).toEquiv
  letI : f.ker.FiniteIndex := AddSubgroup.finiteIndex_iff.mpr (by
    rw [hi]
    exact Nat.card_pos.ne')
  have hm := AddSubgroup.index_mul_measure f.ker hk μ
  rw [hi, measure_univ] at hm
  exact ENNReal.eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using hm)

/-- The measure of each congruence class is derived from its actual finite quotient. -/
theorem fiber_measure (h : H) : μ (f ⁻¹' {h}) = (Nat.card H : ℝ≥0∞)⁻¹ := by
  obtain ⟨a, rfl⟩ := hf h
  rw [fiber_translate f a, measure_preimage_add, kernel_measure μ f hf hk]

/-- Every finite congruence condition has measure equal to its actual counting proportion. -/
theorem preimage_measure (S : Set H) :
    μ (f ⁻¹' S) = (Nat.card S : ℝ≥0∞) / Nat.card H := by
  letI : Fintype S := Fintype.ofFinite S
  rw [← tsum_measure_preimage_singleton (Set.toFinite S).countable
    (fun h _ ↦ fiber_measurable f hf hk h)]
  simp only [fiber_measure μ f hf hk, tsum_fintype, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.card_eq_fintype_card, div_eq_mul_inv]

/-- The same exact normalization in real-valued local-density notation. -/
theorem preimage_real_measure (S : Set H) :
    (μ (f ⁻¹' S)).toReal = (Nat.card S : ℝ) / Nat.card H := by
  rw [preimage_measure μ f hf hk S, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast]

end NormEuclidean.UniformCongruenceMeasure
