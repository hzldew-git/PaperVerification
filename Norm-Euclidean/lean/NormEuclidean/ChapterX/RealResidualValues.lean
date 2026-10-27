import NormEuclidean.ChapterX.OrthogonalTopology
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Real residual value neighborhoods in O'Meara 104:3, step 4

A represented positive or negative unit determines the corresponding real
value ray by an actual square-root rescaling. The required residual value is
represented near beta zero, respectively near beta two divided by the
nonzero preliminary scalar. Simultaneous global scalar selection at all real
and finite places is not asserted here.
-/

noncomputable section

namespace NormEuclidean.RealResidualValues

open Filter Topology

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A real form representing one represents the whole nonnegative value ray. -/
theorem represents_nonnegative (Q : QuadraticForm ℝ V) (x : V) (hx : Q x = 1)
    (t : ℝ) (ht : 0 ≤ t) : ∃ y : V, Q y = t := by
  refine ⟨Real.sqrt t • x, ?_⟩
  rw [Q.map_smul, hx]
  simp only [smul_eq_mul, mul_one, ← pow_two, Real.sq_sqrt ht]

/-- A real form representing minus one represents the whole nonpositive value ray. -/
theorem represents_nonpositive (Q : QuadraticForm ℝ V) (x : V) (hx : Q x = -1)
    (t : ℝ) (ht : t ≤ 0) : ∃ y : V, Q y = t := by
  refine ⟨Real.sqrt (-t) • x, ?_⟩
  rw [Q.map_smul, hx]
  simp only [smul_eq_mul, ← pow_two, Real.sq_sqrt (neg_nonneg.mpr ht)]
  ring

/-- The source positive residual condition is ensured on a genuine real
neighborhood of zero, with the value represented for every scalar in it. -/
theorem exists_positive_residual_neighborhood (Q : QuadraticForm ℝ V)
    (x : V) (hx : Q x = 1) (c : ℝ) :
    ∃ B : Set ℝ, B ∈ 𝓝 0 ∧ ∀ β ∈ B, ∃ y : V, Q y = 1 - c ^ 2 * β ^ 2 := by
  let f (β : ℝ) := 1 - c ^ 2 * β ^ 2
  have hf : Continuous f := by fun_prop
  have hB : {β | 0 < f β} ∈ 𝓝 (0 : ℝ) :=
    (isOpen_Ioi.preimage hf).mem_nhds (by norm_num [f])
  exact ⟨{β | 0 < f β}, hB, fun β hβ ↦ represents_nonnegative Q x hx _ hβ.le⟩

/-- The source negative residual condition is ensured near two divided by
the nonzero preliminary scalar. It is an actual represented-value neighborhood,
without a supplied local value-set or sign-continuity law. -/
theorem exists_negative_residual_neighborhood (Q : QuadraticForm ℝ V)
    (x : V) (hx : Q x = -1) (c : ℝ) (hc : c ≠ 0) :
    ∃ B : Set ℝ, B ∈ 𝓝 (2 / c) ∧ ∀ β ∈ B, ∃ y : V, Q y = 1 - c ^ 2 * β ^ 2 := by
  let f (β : ℝ) := 1 - c ^ 2 * β ^ 2
  have hf : Continuous f := by fun_prop
  have hcenter : f (2 / c) = -3 := by
    dsimp only [f]
    field_simp
    ring
  have hB : {β | f β < 0} ∈ 𝓝 (2 / c) :=
    (isOpen_Iio.preimage hf).mem_nhds (by change f (2 / c) < 0; rw [hcenter]; norm_num)
  exact ⟨{β | f β < 0}, hB, fun β hβ ↦ represents_nonpositive Q x hx _ hβ.le⟩

end NormEuclidean.RealResidualValues
