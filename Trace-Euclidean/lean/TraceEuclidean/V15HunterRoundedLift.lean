import TraceEuclidean.V15HunterProjection
import Mathlib.Algebra.Order.Round

/-!
# Rounded lifts from a projected rank-two lattice

An integral vector in the rank-two orthogonal projection of a rank-three
lattice lifts to the original lattice.  Subtracting the nearest integral
multiple of the distinguished basis vector bounds its parallel component by
one half while preserving its orthogonal projection.
-/

namespace TraceEuclidean

noncomputable section

open MeasureTheory Module Submodule
open scoped RealInnerProductSpace

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Lift a projected vector and reduce its coefficient in the distinguished
direction to the nearest integer. -/
noncomputable def v15HunterRoundedIntegralLift
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (B : Basis (Fin 3) ℤ L)
    (q : v15HunterProjectedLattice (B.ofZLatticeBasis ℝ)) : L :=
  let b := B.ofZLatticeBasis ℝ
  let z : L := v15HunterIntegralLift B q
  let t : ℝ := inner ℝ (b 0) (((z : L) : V)) / inner ℝ (b 0) (b 0)
  z - round t • B 0

/-- Rounding only changes the distinguished component, so the orthogonal
projection of the rounded lift is the original projected vector. -/
theorem v15HunterRoundedIntegralLift_center
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (B : Basis (Fin 3) ℤ L)
    (q : v15HunterProjectedLattice (B.ofZLatticeBasis ℝ)) :
    v15HunterCenterLinearMap ((B.ofZLatticeBasis ℝ) 0)
        (inner_self_ne_zero.mpr ((B.ofZLatticeBasis ℝ).ne_zero 0))
        (((v15HunterRoundedIntegralLift L B q : L) : V)) =
      ((q : v15HunterProjectedLattice (B.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (B.ofZLatticeBasis ℝ) 0)ᗮ) := by
  let b := B.ofZLatticeBasis ℝ
  let z : L := v15HunterIntegralLift B q
  let t : ℝ := inner ℝ (b 0) (((z : L) : V)) / inner ℝ (b 0) (b 0)
  have hB0 : (((B 0 : L) : V)) = b 0 :=
    (B.ofZLatticeBasis_apply ℝ L 0).symm
  have hsmul : ((((round t) • B 0 : L) : L) : V) =
      (round t : ℤ) • (((B 0 : L) : V)) :=
    map_zsmul L.subtype (round t) (B 0)
  change v15HunterCenterLinearMap (b 0)
      (inner_self_ne_zero.mpr (b.ne_zero 0))
      ((((z - round t • B 0 : L) : L) : V)) = _
  rw [Submodule.coe_sub, hsmul, hB0]
  rw [← Int.cast_smul_eq_zsmul ℝ]
  rw [map_sub]
  rw [v15HunterCenterLinearMap_smul_self, sub_zero]
  exact v15HunterIntegralLift_center B q

/-- A nonzero projected vector has a nonzero rounded integral lift. -/
theorem v15HunterRoundedIntegralLift_ne_zero
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (B : Basis (Fin 3) ℤ L)
    (q : v15HunterProjectedLattice (B.ofZLatticeBasis ℝ))
    (hq : q ≠ 0) :
    v15HunterRoundedIntegralLift L B q ≠ 0 := by
  intro hzero
  have hcenter := v15HunterRoundedIntegralLift_center L B q
  have hyval : (((v15HunterRoundedIntegralLift L B q : L) : V)) = 0 := by
    rw [hzero]
    rfl
  have hfzero : v15HunterCenterLinearMap ((B.ofZLatticeBasis ℝ) 0)
      (inner_self_ne_zero.mpr ((B.ofZLatticeBasis ℝ).ne_zero 0))
      (((v15HunterRoundedIntegralLift L B q : L) : V)) = 0 := by
    let f := v15HunterCenterLinearMap ((B.ofZLatticeBasis ℝ) 0)
      (inner_self_ne_zero.mpr ((B.ofZLatticeBasis ℝ).ne_zero 0))
    exact (congrArg f hyval).trans (map_zero f)
  have hqval :
      ((q : v15HunterProjectedLattice (B.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (B.ofZLatticeBasis ℝ) 0)ᗮ) = 0 :=
    hcenter.symm.trans hfzero
  exact hq (Subtype.ext hqval)

omit [FiniteDimensional ℝ V] in
/-- The elementary identity behind nearest-integer reduction of the parallel
component. -/
theorem v15_inner_sub_round_smul_eq_inner_center_add
    (e z : V) (d : ℝ) (hd : d ≠ 0)
    (hinner : inner ℝ e e = d) (k : ℝ) :
    inner ℝ (z - k • e) (z - k • e) =
      inner ℝ (v15HunterCenter e z) (v15HunterCenter e z) +
        d * (inner ℝ e z / d - k) ^ 2 := by
  have he : inner ℝ e e ≠ 0 := by rw [hinner]; exact hd
  rw [v15_inner_center_center e z z he]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, starRingEnd_apply, star_trivial]
  rw [real_inner_comm z e, hinner]
  field_simp
  ring

/-- The rounded lift has squared norm at most the projected squared norm plus
one quarter of the distinguished squared norm. -/
theorem v15HunterRoundedIntegralLift_norm_sq_le
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (B : Basis (Fin 3) ℤ L)
    (d : ℝ) (hd : 0 < d)
    (hinner : inner ℝ ((B.ofZLatticeBasis ℝ) 0)
      ((B.ofZLatticeBasis ℝ) 0) = d)
    (q : v15HunterProjectedLattice (B.ofZLatticeBasis ℝ)) :
    ‖(((v15HunterRoundedIntegralLift L B q : L) : V))‖ ^ 2 ≤
      ‖((q : v15HunterProjectedLattice (B.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (B.ofZLatticeBasis ℝ) 0)ᗮ)‖ ^ 2 + d / 4 := by
  let b := B.ofZLatticeBasis ℝ
  let z : L := v15HunterIntegralLift B q
  let t : ℝ := inner ℝ (b 0) (((z : L) : V)) / d
  let k : ℝ := round t
  have hB0 : (((B 0 : L) : V)) = b 0 :=
    (B.ofZLatticeBasis_apply ℝ L 0).symm
  have hrounded :
      (((v15HunterRoundedIntegralLift L B q : L) : V)) =
        (((z : L) : V)) - k • b 0 := by
    unfold v15HunterRoundedIntegralLift
    dsimp only
    rw [hinner]
    change ((((z - round t • B 0 : L) : L) : V)) = _
    have hsmul : ((((round t) • B 0 : L) : L) : V) =
        (round t : ℤ) • (((B 0 : L) : V)) :=
      map_zsmul L.subtype (round t) (B 0)
    rw [Submodule.coe_sub, hsmul, hB0]
    rw [← Int.cast_smul_eq_zsmul ℝ]
  have hcenter := v15HunterIntegralLift_center B q
  have hcenterVal := congrArg Subtype.val hcenter
  change v15HunterCenter (b 0) (((z : L) : V)) =
    (((q : v15HunterProjectedLattice b) : (ℝ ∙ b 0)ᗮ) : V) at hcenterVal
  have hround := abs_sub_round t
  have hroundSq : (t - k) ^ 2 ≤ 1 / 4 := by
    have habs : |t - k| ≤ 1 / 2 := by simpa [k] using hround
    have hb := abs_le.mp habs
    nlinarith [sq_nonneg (t - k + 1 / 2),
      sq_nonneg (1 / 2 - (t - k))]
  have hid := v15_inner_sub_round_smul_eq_inner_center_add
    (b 0) (((z : L) : V)) d hd.ne' hinner k
  rw [hrounded, ← real_inner_self_eq_norm_sq]
  rw [hid]
  have hcenterInner :
      inner ℝ (v15HunterCenter (b 0) (((z : L) : V)))
          (v15HunterCenter (b 0) (((z : L) : V))) =
        ‖((q : v15HunterProjectedLattice b) : (ℝ ∙ b 0)ᗮ)‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    change inner ℝ (v15HunterCenter (b 0) (((z : L) : V)))
        (v15HunterCenter (b 0) (((z : L) : V))) =
      inner ℝ
        (((q : v15HunterProjectedLattice b) : (ℝ ∙ b 0)ᗮ) : V)
        (((q : v15HunterProjectedLattice b) : (ℝ ∙ b 0)ᗮ) : V)
    rw [hcenterVal]
  rw [hcenterInner]
  change _ + d * (t - k) ^ 2 ≤ _
  nlinarith

end

end TraceEuclidean
