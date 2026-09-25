import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
# A three-dimensional Minkowski ball for the quartic Hunter argument

This module proves a coordinate-free short-vector theorem using only the
three-dimensional Minkowski convex-body theorem.  Its bound is slightly
weaker than the sharp Hermite bound.  It supplies an unconditional geometric
route to a larger finite quartic coefficient search; the extra arithmetic
candidates produced by that search must still be handled separately.
-/

namespace TraceEuclidean

noncomputable section

open MeasureTheory Metric Set

/-- The Euclidean three-space used for the quartic Hunter projection. -/
abbrev V15QuarticHunterSpace := EuclideanSpace ℝ (Fin 3)

/-- Radius whose squared-norm condition is `4 * ‖x‖^2 < 35`. -/
def v15QuarticHunterRadius : ℝ :=
  Real.sqrt 35 / 2

theorem v15QuarticHunterRadius_pos : 0 < v15QuarticHunterRadius := by
  exact div_pos (Real.sqrt_pos.2 (by norm_num)) (by norm_num)

/-- The three-dimensional ball is large enough for every projected quartic
lattice whose covolume is below `sqrt 725 / 2`. -/
theorem v15_quartic_hunter_covolume_constant_lt_ball_volume :
    (Real.sqrt 725 / 2 : ℝ) * 8 <
      v15QuarticHunterRadius ^ 3 * (Real.pi * 4 / 3) := by
  have hsqrt725 : Real.sqrt 725 < (2693 / 100 : ℝ) := by
    rw [← sq_lt_sq₀ (Real.sqrt_nonneg 725) (by norm_num)]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 725)]
    norm_num
  have hsqrt35 : (591 / 100 : ℝ) < Real.sqrt 35 := by
    rw [← sq_lt_sq₀ (by norm_num) (Real.sqrt_nonneg 35)]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 35)]
    norm_num
  have hpi : (157 / 50 : ℝ) < Real.pi := by
    have h := Real.pi_gt_d2
    norm_num at h ⊢
    exact h
  have hprod : (157 / 50 : ℝ) * (591 / 100) <
      Real.pi * Real.sqrt 35 :=
    mul_lt_mul hpi hsqrt35.le (by norm_num) Real.pi_pos.le
  have hsqrt35sq : Real.sqrt 35 ^ 2 = 35 :=
    Real.sq_sqrt (by norm_num)
  rw [v15QuarticHunterRadius]
  nlinarith

/-- Membership in the quartic Hunter ball gives the scaled squared-norm
bound used by the enlarged finite coefficient search. -/
theorem v15_four_mul_norm_sq_lt_thirtyFive_of_mem_ball
    {x : V15QuarticHunterSpace}
    (hx : x ∈ ball 0 v15QuarticHunterRadius) :
    4 * ‖x‖ ^ 2 < 35 := by
  have hnorm : ‖x‖ < Real.sqrt 35 / 2 := by
    simpa [v15QuarticHunterRadius, mem_ball, dist_zero_right] using hx
  have hnonneg : 0 ≤ ‖x‖ := norm_nonneg x
  have hsqrt : 0 ≤ Real.sqrt 35 := Real.sqrt_nonneg 35
  have hmul : 2 * ‖x‖ < Real.sqrt 35 := by linarith
  have hsq : (2 * ‖x‖) ^ 2 < (Real.sqrt 35) ^ 2 :=
    (sq_lt_sq₀ (by positivity) hsqrt).2 hmul
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 35)] at hsq
  nlinarith

/-- The strict three-dimensional Minkowski ball step. -/
theorem v15_quartic_hunter_shortVector_of_fundamentalDomain
    (L : AddSubgroup V15QuarticHunterSpace) [Countable L]
    {F : Set V15QuarticHunterSpace}
    (fund : IsAddFundamentalDomain L F volume)
    (hvolume :
      volume F * 2 ^ Module.finrank ℝ V15QuarticHunterSpace <
        volume (ball (0 : V15QuarticHunterSpace)
          v15QuarticHunterRadius)) :
    ∃ x : L, x ≠ 0 ∧
      4 * ‖((x : L) : V15QuarticHunterSpace)‖ ^ 2 < 35 := by
  obtain ⟨x, hx0, hx⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      fund
      (fun y hy ↦ by simpa [mem_ball, dist_zero_right] using hy)
      (convex_ball (0 : V15QuarticHunterSpace) v15QuarticHunterRadius)
      hvolume
  exact ⟨x, hx0,
    v15_four_mul_norm_sq_lt_thirtyFive_of_mem_ball hx⟩

/-- A covolume below `sqrt 725 / 2` gives the ball-volume inequality needed
by the three-dimensional Minkowski theorem. -/
theorem v15_quartic_hunter_measure_bound_of_covolume_lt
    {F : Set V15QuarticHunterSpace}
    (hF : volume F < ENNReal.ofReal (Real.sqrt 725 / 2)) :
    volume F * 2 ^ Module.finrank ℝ V15QuarticHunterSpace <
      volume (ball (0 : V15QuarticHunterSpace)
        v15QuarticHunterRadius) := by
  have hconst := v15_quartic_hunter_covolume_constant_lt_ball_volume
  calc
    volume F * 2 ^ Module.finrank ℝ V15QuarticHunterSpace =
        volume F * 8 := by norm_num [V15QuarticHunterSpace]
    _ < ENNReal.ofReal (Real.sqrt 725 / 2) * 8 := by
      simpa [mul_comm] using
        (ENNReal.mul_lt_mul_right
          (by norm_num : (8 : ENNReal) ≠ 0)
          (by norm_num : (8 : ENNReal) ≠ ⊤) hF)
    _ = ENNReal.ofReal ((Real.sqrt 725 / 2) * 8) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      norm_num
    _ < ENNReal.ofReal
        (v15QuarticHunterRadius ^ 3 * (Real.pi * 4 / 3)) :=
      ENNReal.ofReal_lt_ofReal_iff
        (mul_pos (pow_pos v15QuarticHunterRadius_pos 3)
          (by positivity)) |>.2 hconst
    _ = volume (ball (0 : V15QuarticHunterSpace)
        v15QuarticHunterRadius) := by
      rw [EuclideanSpace.volume_ball_fin_three]
      rw [ENNReal.ofReal_mul
          (pow_nonneg v15QuarticHunterRadius_pos.le 3),
        ENNReal.ofReal_pow v15QuarticHunterRadius_pos.le]

/-- Intrinsic covolume form of the three-dimensional Minkowski ball step. -/
theorem v15_quartic_hunter_shortVector_of_covolume_lt
    (L : Submodule ℤ V15QuarticHunterSpace)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (hcov : ZLattice.covolume L < Real.sqrt 725 / 2) :
    ∃ x : L, x ≠ 0 ∧
      4 * ‖((x : L) : V15QuarticHunterSpace)‖ ^ 2 < 35 := by
  let b := Module.Free.chooseBasis ℤ L
  let F : Set V15QuarticHunterSpace :=
    ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)
  have fund : IsAddFundamentalDomain L F volume := by
    exact ZLattice.isAddFundamentalDomain b volume
  have hreal : volume.real F < Real.sqrt 725 / 2 := by
    rw [← ZLattice.covolume_eq_measure_fundamentalDomain L volume fund]
    exact hcov
  have hfinite : volume F ≠ ⊤ := by
    exact (ZSpan.fundamentalDomain_isBounded
      (b.ofZLatticeBasis ℝ L)).measure_lt_top.ne
  have hF : volume F < ENNReal.ofReal (Real.sqrt 725 / 2) := by
    apply (ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (by positivity)]
    exact hreal
  letI : Countable L.toAddSubgroup := by
    let f : L.toAddSubgroup → L := fun x ↦ ⟨x.1, x.2⟩
    exact (show Function.Injective f by
      intro x y hxy
      exact Subtype.ext (congrArg Subtype.val hxy)).countable
  exact v15_quartic_hunter_shortVector_of_fundamentalDomain
    L.toAddSubgroup fund
      (v15_quartic_hunter_measure_bound_of_covolume_lt hF)

/-- Coordinate-free three-dimensional form of the quartic Minkowski ball
theorem. -/
theorem v15_quartic_hunter_shortVector_of_covolume_lt_of_finrank_eq_three
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hfin : Module.finrank ℝ E = 3)
    (hcov : ZLattice.covolume L < Real.sqrt 725 / 2) :
    ∃ x : L, x ≠ 0 ∧ 4 * ‖((x : L) : E)‖ ^ 2 < 35 := by
  let oE : OrthonormalBasis (Fin 3) ℝ E :=
    (stdOrthonormalBasis ℝ E).reindex (finCongr hfin)
  let e : V15QuarticHunterSpace ≃ₗᵢ[ℝ] E :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).equiv oE (Equiv.refl (Fin 3))
  let L' : Submodule ℤ V15QuarticHunterSpace :=
    ZLattice.comap ℝ L e.toContinuousLinearEquiv.toLinearMap
  have hcovEq : ZLattice.covolume L' = ZLattice.covolume L := by
    exact ZLattice.covolume_comap L volume volume
      (LinearIsometryEquiv.measurePreserving e)
  have hcov' : ZLattice.covolume L' < Real.sqrt 725 / 2 := by
    rw [hcovEq]
    exact hcov
  obtain ⟨x, hx0, hxshort⟩ :=
    v15_quartic_hunter_shortVector_of_covolume_lt L' hcov'
  let y : L := ⟨e x.1, x.2⟩
  have hy0 : y ≠ 0 := by
    intro hy
    apply hx0
    apply Subtype.ext
    apply e.injective
    simpa [y] using congrArg Subtype.val hy
  refine ⟨y, hy0, ?_⟩
  simpa [y] using hxshort

end

end TraceEuclidean
