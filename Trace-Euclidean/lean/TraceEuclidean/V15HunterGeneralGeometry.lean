import TraceEuclidean.CoveringVolume
import Mathlib.MeasureTheory.Group.GeometryOfNumbers

/-!
# A Minkowski ball theorem in arbitrary dimension

This module gives the dimension-independent geometry-of-numbers step for the
general Hunter construction.  The hypothesis is expressed using the exact
Euclidean unit-ball volume already used elsewhere in the verification.
-/

namespace TraceEuclidean

noncomputable section

open MeasureTheory Metric Set Module

/-- Cancel a positive common factor after substituting a squared-covolume
identity.  This elementary lemma keeps the subsequent number-field theorem
independent of large reducible lattice expressions. -/
theorem v15_sq_mul_lt_sq_of_sq_mul_eq
    {c d D a b : ℝ} (hd : 0 < d)
    (hidentity : c ^ 2 * d = D)
    (hbound : D * a ^ 2 < d * b ^ 2) :
    (c * a) ^ 2 < b ^ 2 := by
  have hmul : d * (c ^ 2 * a ^ 2) < d * b ^ 2 := by
    calc
      d * (c ^ 2 * a ^ 2) = (c ^ 2 * d) * a ^ 2 := by ring
      _ = D * a ^ 2 := by rw [hidentity]
      _ < d * b ^ 2 := hbound
  have hbase := lt_of_mul_lt_mul_left hmul hd.le
  simpa [mul_pow] using hbase

/-- Exact real-volume formula for a positive-radius Euclidean ball, expressed
using `euclideanUnitBallVolume`. -/
theorem v15_volume_ball_eq_ofReal_unitBall_mul_pow
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Nontrivial E] (r : ℝ) (hr : 0 < r) :
    volume (ball (0 : E) r) =
      ENNReal.ofReal
        (euclideanUnitBallVolume (finrank ℝ E) * r ^ finrank ℝ E) := by
  rw [InnerProductSpace.volume_ball]
  rw [sqrtPiPow_div_gamma_eq_euclideanUnitBallVolume]
  rw [← ENNReal.ofReal_pow hr.le]
  rw [mul_comm]
  rw [← ENNReal.ofReal_mul
    (euclideanUnitBallVolume_pos (finrank ℝ E)).le]

/-- A full lattice contains a nonzero vector in any centered Euclidean ball
whose volume is strictly larger than `2^m` times a fundamental-domain
volume. -/
theorem v15_hunterGeneral_shortVector_of_fundamentalDomain
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : AddSubgroup E) [Countable L] {F : Set E}
    (fund : IsAddFundamentalDomain L F volume) (r : ℝ)
    (hvolume :
      volume F * 2 ^ finrank ℝ E < volume (ball (0 : E) r)) :
    ∃ x : L, x ≠ 0 ∧ ‖((x : L) : E)‖ < r := by
  obtain ⟨x, hx0, hx⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      fund
      (fun y hy ↦ by simpa [mem_ball, dist_zero_right] using hy)
      (convex_ball (0 : E) r) hvolume
  exact ⟨x, hx0, by simpa [mem_ball, dist_zero_right] using hx⟩

/-- Intrinsic arbitrary-dimensional Minkowski ball theorem.  The displayed
real inequality is the exact condition obtained from the Euclidean ball
volume formula. -/
theorem v15_hunterGeneral_shortVector_of_covolume
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Nontrivial E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (r : ℝ) (hr : 0 < r)
    (hvolume :
      ZLattice.covolume L * (2 : ℝ) ^ finrank ℝ E <
        euclideanUnitBallVolume (finrank ℝ E) * r ^ finrank ℝ E) :
    ∃ x : L, x ≠ 0 ∧ ‖((x : L) : E)‖ < r := by
  let b := Module.Free.chooseBasis ℤ L
  let F : Set E := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)
  have fund : IsAddFundamentalDomain L F volume := by
    exact ZLattice.isAddFundamentalDomain b volume
  have hreal : volume.real F = ZLattice.covolume L := by
    exact (ZLattice.covolume_eq_measure_fundamentalDomain
      L volume fund).symm
  have hfinite : volume F ≠ ⊤ := by
    exact (ZSpan.fundamentalDomain_isBounded
      (b.ofZLatticeBasis ℝ L)).measure_lt_top.ne
  have htoReal : (volume F).toReal = ZLattice.covolume L := by
    exact hreal
  have hF : volume F = ENNReal.ofReal (ZLattice.covolume L) := by
    have h := (ENNReal.ofReal_toReal hfinite).symm
    rw [htoReal] at h
    exact h
  have hrightPos :
      0 < euclideanUnitBallVolume (finrank ℝ E) * r ^ finrank ℝ E :=
    mul_pos (euclideanUnitBallVolume_pos _) (pow_pos hr _)
  have hENN :
      ENNReal.ofReal
          (ZLattice.covolume L * (2 : ℝ) ^ finrank ℝ E) <
        ENNReal.ofReal
          (euclideanUnitBallVolume (finrank ℝ E) *
            r ^ finrank ℝ E) :=
    (ENNReal.ofReal_lt_ofReal_iff hrightPos).2 hvolume
  have hleft :
      ENNReal.ofReal
          (ZLattice.covolume L * (2 : ℝ) ^ finrank ℝ E) =
        ENNReal.ofReal (ZLattice.covolume L) *
          (2 : ENNReal) ^ finrank ℝ E := by
    rw [ENNReal.ofReal_mul
      (ZLattice.covolume_pos (μ := volume) L).le]
    rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hmeasure :
      volume F * 2 ^ finrank ℝ E < volume (ball (0 : E) r) := by
    rw [hF, v15_volume_ball_eq_ofReal_unitBall_mul_pow r hr]
    rw [hleft] at hENN
    simpa using hENN
  letI : Countable L.toAddSubgroup := by
    let f : L.toAddSubgroup → L := fun x ↦ ⟨x.1, x.2⟩
    exact (show Function.Injective f by
      intro x y hxy
      exact Subtype.ext (congrArg Subtype.val hxy)).countable
  exact v15_hunterGeneral_shortVector_of_fundamentalDomain
    L.toAddSubgroup fund r hmeasure

end

end TraceEuclidean
