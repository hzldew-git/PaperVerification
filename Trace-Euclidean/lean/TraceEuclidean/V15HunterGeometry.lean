import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
# The two-dimensional Hunter short-vector step

This module isolates the geometry-of-numbers step used after projecting the
integer ring of a cubic field orthogonally to the complement of `1`.  Once a
fundamental domain of the projected lattice satisfies the displayed disk-area
inequality, Minkowski's convex-body theorem produces a nonzero vector whose
scaled squared norm is strictly smaller than `16`.
-/

namespace TraceEuclidean

noncomputable section

open MeasureTheory Metric Set

/-- The Euclidean plane used for the cubic Hunter projection. -/
abbrev V15HunterPlane := EuclideanSpace ℝ (Fin 2)

/-- Radius whose squared norm condition is `3 * ‖x‖^2 < 16`. -/
def v15HunterRadius : ℝ :=
  4 / Real.sqrt 3

theorem v15HunterRadius_pos : 0 < v15HunterRadius := by
  exact div_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num))

/-- The elementary numerical comparison that makes the weaker disk version
of Hunter's cubic argument sufficient below discriminant `49`. -/
theorem v15_hunter_covolume_constant_lt_disk_area :
    (7 / Real.sqrt 3 : ℝ) * 4 <
      v15HunterRadius ^ 2 * Real.pi := by
  have hsqrt : (17 / 10 : ℝ) < Real.sqrt 3 := by
    rw [← sq_lt_sq₀ (by norm_num) (Real.sqrt_nonneg 3)]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hprod : (21 / 4 : ℝ) < Real.pi * Real.sqrt 3 := by
    have hpi : (157 / 50 : ℝ) < Real.pi := by
      have h := Real.pi_gt_d2
      norm_num at h ⊢
      exact h
    have hmul : (157 / 50 : ℝ) * (17 / 10) <
        Real.pi * Real.sqrt 3 :=
      mul_lt_mul hpi hsqrt.le (by norm_num) Real.pi_pos.le
    norm_num at hmul ⊢
    linarith
  have hsqrt0 : Real.sqrt 3 ≠ 0 :=
    (Real.sqrt_pos.2 (by norm_num)).ne'
  rw [v15HunterRadius]
  field_simp [hsqrt0]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

/-- Membership in the Hunter disk gives the exact scaled squared-norm bound
used by the cubic coefficient enumeration. -/
theorem v15_three_mul_norm_sq_lt_sixteen_of_mem_ball
    {x : V15HunterPlane}
    (hx : x ∈ ball 0 v15HunterRadius) :
    3 * ‖x‖ ^ 2 < 16 := by
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hnorm : ‖x‖ < 4 / Real.sqrt 3 := by
    simpa [v15HunterRadius, mem_ball, dist_zero_right] using hx
  have hmul : ‖x‖ * Real.sqrt 3 < 4 :=
    (lt_div_iff₀ hsqrt).mp hnorm
  have hsq : (‖x‖ * Real.sqrt 3) ^ 2 < (4 : ℝ) ^ 2 :=
    (sq_lt_sq₀ (mul_nonneg (norm_nonneg x) hsqrt.le) (by norm_num)).2 hmul
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] at hsq
  nlinarith

/-- The strict two-dimensional Minkowski disk step for the projected cubic
lattice.  The remaining field-specific task is to construct `L`, its
fundamental domain, and the displayed covolume inequality. -/
theorem v15_hunter_shortVector_of_fundamentalDomain
    (L : AddSubgroup V15HunterPlane) [Countable L]
    {F : Set V15HunterPlane}
    (fund : IsAddFundamentalDomain L F volume)
    (hvolume :
      volume F * 2 ^ Module.finrank ℝ V15HunterPlane <
        volume (ball (0 : V15HunterPlane) v15HunterRadius)) :
    ∃ x : L, x ≠ 0 ∧
      3 * ‖((x : L) : V15HunterPlane)‖ ^ 2 < 16 := by
  obtain ⟨x, hx0, hx⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      fund
      (fun y hy ↦ by simpa [mem_ball, dist_zero_right] using hy)
      (convex_ball (0 : V15HunterPlane) v15HunterRadius)
      hvolume
  exact ⟨x, hx0, v15_three_mul_norm_sq_lt_sixteen_of_mem_ball hx⟩

/-- A projected covolume strictly below `7 / sqrt(3)` supplies the disk-area
inequality required by `v15_hunter_shortVector_of_fundamentalDomain`. -/
theorem v15_hunter_measure_bound_of_covolume_lt
    {F : Set V15HunterPlane}
    (hF : volume F < ENNReal.ofReal (7 / Real.sqrt 3)) :
    volume F * 2 ^ Module.finrank ℝ V15HunterPlane <
      volume (ball (0 : V15HunterPlane) v15HunterRadius) := by
  have hconst := v15_hunter_covolume_constant_lt_disk_area
  calc
    volume F * 2 ^ Module.finrank ℝ V15HunterPlane =
        volume F * 4 := by norm_num [V15HunterPlane]
    _ < ENNReal.ofReal (7 / Real.sqrt 3) * 4 := by
      simpa [mul_comm] using
        (ENNReal.mul_lt_mul_right
          (by norm_num : (4 : ENNReal) ≠ 0)
          (by norm_num : (4 : ENNReal) ≠ ⊤) hF)
    _ = ENNReal.ofReal ((7 / Real.sqrt 3) * 4) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      norm_num
    _ < ENNReal.ofReal (v15HunterRadius ^ 2 * Real.pi) :=
      ENNReal.ofReal_lt_ofReal_iff
        (mul_pos (pow_pos v15HunterRadius_pos 2) Real.pi_pos) |>.2 hconst
    _ = volume (ball (0 : V15HunterPlane) v15HunterRadius) := by
      rw [EuclideanSpace.volume_ball_fin_two]
      rw [ENNReal.ofReal_mul (sq_nonneg v15HunterRadius),
        ENNReal.ofReal_pow v15HunterRadius_pos.le]

/-- Intrinsic covolume form of the Hunter disk argument.  A full
two-dimensional `ℤ`-lattice with covolume below `7 / sqrt(3)` contains the
required nonzero short vector; callers no longer need to provide a
fundamental domain explicitly. -/
theorem v15_hunter_shortVector_of_covolume_lt
    (L : Submodule ℤ V15HunterPlane)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (hcov : ZLattice.covolume L < 7 / Real.sqrt 3) :
    ∃ x : L, x ≠ 0 ∧
      3 * ‖((x : L) : V15HunterPlane)‖ ^ 2 < 16 := by
  let b := Module.Free.chooseBasis ℤ L
  let F : Set V15HunterPlane :=
    ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)
  have fund : IsAddFundamentalDomain L F volume := by
    exact ZLattice.isAddFundamentalDomain b volume
  have hreal : volume.real F < 7 / Real.sqrt 3 := by
    rw [← ZLattice.covolume_eq_measure_fundamentalDomain L volume fund]
    exact hcov
  have hfinite : volume F ≠ ⊤ := by
    exact (ZSpan.fundamentalDomain_isBounded
      (b.ofZLatticeBasis ℝ L)).measure_lt_top.ne
  have hF : volume F < ENNReal.ofReal (7 / Real.sqrt 3) := by
    apply (ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (by positivity)]
    exact hreal
  letI : Countable L.toAddSubgroup := by
    let f : L.toAddSubgroup → L := fun x ↦ ⟨x.1, x.2⟩
    exact (show Function.Injective f by
      intro x y hxy
      exact Subtype.ext (congrArg Subtype.val hxy)).countable
  exact v15_hunter_shortVector_of_fundamentalDomain
    L.toAddSubgroup fund (v15_hunter_measure_bound_of_covolume_lt hF)

end

end TraceEuclidean
