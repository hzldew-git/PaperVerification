import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Uniform small vectors from actual bounded fundamental domains

An actual upper bound on fundamental-domain measure gives one norm bound
for a nonzero vector in every such real integer lattice. The proof uses
Minkowski's convex body theorem and large metric balls. Zero dimension is
excluded by the explicit nontriviality assumption.
-/

noncomputable section

namespace NormEuclidean.MinkowskiBound

open MeasureTheory MeasureTheory.Measure Module Filter Metric
open scoped ENNReal

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι]

/-- Uniform bounded fundamental-domain measures give uniform nonzero small
vectors in their actual integer spans, with no approximation law supplied. -/
theorem exists_uniform_norm_bound (μ : Measure E) [IsAddHaarMeasure μ]
    (C : ℝ≥0∞) (hC : C < ⊤) :
    ∃ R : ℝ, 0 < R ∧ ∀ b : Basis ι ℝ E, μ (ZSpan.fundamentalDomain b) ≤ C →
      ∃ x ∈ Submodule.span ℤ (Set.range b), x ≠ 0 ∧ ‖x‖ ≤ R := by
  classical
  let s : ℕ → Set E := fun n ↦ ball 0 (n : ℝ)
  have hmono : Monotone s := by
    intro a b hab
    exact ball_subset_ball (by exact_mod_cast hab)
  have hlim : Tendsto (fun n ↦ μ (s n)) atTop (nhds ⊤) := by
    simpa only [s, Function.comp_def, iUnion_ball_nat,
      measure_univ_of_isAddLeftInvariant] using
      (tendsto_measure_iUnion_atTop (μ := μ) hmono)
  have hbound : C * 2 ^ Module.finrank ℝ E < ⊤ :=
    ENNReal.mul_lt_top hC (by finiteness)
  obtain ⟨n, hn⟩ := (hlim.eventually (Ioi_mem_nhds hbound)).exists
  refine ⟨max (n : ℝ) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro b hb
  let L := (Submodule.span ℤ (Set.range b)).toAddSubgroup
  haveI : Countable L := by
    change Countable (Submodule.span ℤ (Set.range b))
    infer_instance
  have hfund : IsAddFundamentalDomain L (ZSpan.fundamentalDomain b) μ :=
    ZSpan.isAddFundamentalDomain' b μ
  have hvol : μ (ZSpan.fundamentalDomain b) * 2 ^ Module.finrank ℝ E < μ (s n) :=
    (mul_le_mul_left hb _).trans_lt hn
  obtain ⟨x, hx0, hx⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hfund
      (by intro y hy; simpa only [s, mem_ball_zero_iff, norm_neg] using hy)
      (convex_ball 0 (n : ℝ)) hvol
  refine ⟨x, x.2, ?_, ?_⟩
  · intro h
    exact hx0 (Subtype.ext h)
  · exact (mem_ball_zero_iff.mp hx).le.trans (le_max_left _ _)

end NormEuclidean.MinkowskiBound
