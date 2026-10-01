import TraceEuclidean.QuarticProjectedIntegralGram
import TraceEuclidean.HunterRoundedLift

/-!
# A second short vector in the quartic Hunter lattice

If the first Minkowski vector generates a proper quadratic subfield, it is a
primitive vector of squared norm `5` or `8`.  Projecting along it, the sharp
binary Gauss bound and nearest-integer lifting produce another short integral
vector with a nonzero component orthogonal to the first.
-/

namespace TraceEuclidean

noncomputable section

open NumberField MeasureTheory Module Submodule
open scoped NumberField RealInnerProductSpace

universe u

/-- The numerical consequence of the Gauss bound in the discriminant-five
branch. -/
theorem gauss_norm_sq_lt_seven
    (r qCov lCov : ℝ)
    (hgauss : 3 * r ^ 4 ≤ 4 * qCov ^ 2)
    (hquot : qCov ^ 2 * 5 = lCov ^ 2)
    (hfull : lCov ^ 2 * 4 < 725) :
    r ^ 2 < 7 := by
  have hr4 : r ^ 4 = (r ^ 2) ^ 2 := by ring
  rw [hr4] at hgauss
  nlinarith [sq_nonneg (r ^ 2 - 7), sq_nonneg qCov, sq_nonneg lCov]

/-- The numerical consequence of the Gauss bound in the discriminant-eight
branch. -/
theorem gauss_norm_sq_lt_eleven_halves
    (r qCov lCov : ℝ)
    (hgauss : 3 * r ^ 4 ≤ 4 * qCov ^ 2)
    (hquot : qCov ^ 2 * 8 = lCov ^ 2)
    (hfull : lCov ^ 2 * 4 < 725) :
    r ^ 2 < 11 / 2 := by
  have hr4 : r ^ 4 = (r ^ 2) ^ 2 := by ring
  rw [hr4] at hgauss
  nlinarith [sq_nonneg (r ^ 2 - 11 / 2), sq_nonneg qCov, sq_nonneg lCov]

set_option maxHeartbeats 1000000 in
-- The covolume rewrites and nonlinear real arithmetic exceed the default.
/-- Abstract Gauss-and-rounding step used in both quadratic-discriminant
branches. -/
theorem exists_hunterRounded_shortVector
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (B : Basis (Fin 3) ℤ L)
    (d : ℕ) (hd : 0 < d)
    (hinner : inner ℝ ((B.ofZLatticeBasis ℝ) 0)
      ((B.ofZLatticeBasis ℝ) 0) = d)
    (hIntegral : ∀ x y : L, ∃ z : ℤ,
      (z : ℝ) = 4 * inner ℝ (((x : L) : V)) (((y : L) : V)))
    (bound : ℝ)
    (hbound : ∀ r qCov : ℝ,
      3 * r ^ 4 ≤ 4 * qCov ^ 2 →
      qCov ^ 2 * d = ZLattice.covolume L ^ 2 →
      r ^ 2 < bound)
    (hfinal : 4 * (bound + (d : ℝ) / 4) < 35) :
    ∃ y : L, y ≠ 0 ∧ 4 * ‖(((y : L) : V))‖ ^ 2 < 35 ∧
      hunterCenterLinearMap ((B.ofZLatticeBasis ℝ) 0)
        (inner_self_ne_zero.mpr ((B.ofZLatticeBasis ℝ).ne_zero 0))
        (((y : L) : V)) ≠ 0 := by
  obtain ⟨q, hq, hgauss⟩ :=
    exists_hunterProjected_shortVector_gauss
      L B 4 d (by norm_num) hd hinner hIntegral
  have hQcov :=
    hunterProjectedLattice_covolume_sq_mul_inner_self
      (B.ofZLatticeBasis ℝ)
  rw [hinner] at hQcov
  rw [show span ℤ (Set.range (B.ofZLatticeBasis ℝ)) = L by
    exact B.ofZLatticeBasis_span ℝ] at hQcov
  let r : ℝ := ‖((q : hunterProjectedLattice
    (B.ofZLatticeBasis ℝ)) :
    (ℝ ∙ (B.ofZLatticeBasis ℝ) 0)ᗮ)‖
  change 3 * r ^ 4 ≤
    4 * ZLattice.covolume
      (hunterProjectedLattice (B.ofZLatticeBasis ℝ)) ^ 2 at hgauss
  have hqnorm : r ^ 2 < bound :=
    hbound r
      (ZLattice.covolume
        (hunterProjectedLattice (B.ofZLatticeBasis ℝ))) hgauss hQcov
  let y : L := hunterRoundedIntegralLift L B q
  have hynorm := hunterRoundedIntegralLift_norm_sq_le
    L B (d : ℝ) (by exact_mod_cast hd) (by exact_mod_cast hinner) q
  have hyshort : 4 * ‖(((y : L) : V))‖ ^ 2 < 35 := by
    dsimp [y]
    change ‖((q : hunterProjectedLattice
      (B.ofZLatticeBasis ℝ)) :
      (ℝ ∙ (B.ofZLatticeBasis ℝ) 0)ᗮ)‖ ^ 2 < bound at hqnorm
    nlinarith
  have hyne : y ≠ 0 := hunterRoundedIntegralLift_ne_zero L B q hq
  have hycenter : hunterCenterLinearMap ((B.ofZLatticeBasis ℝ) 0)
      (inner_self_ne_zero.mpr ((B.ofZLatticeBasis ℝ).ne_zero 0))
      (((y : L) : V)) ≠ 0 := by
    rw [show hunterCenterLinearMap ((B.ofZLatticeBasis ℝ) 0)
        (inner_self_ne_zero.mpr ((B.ofZLatticeBasis ℝ).ne_zero 0))
        (((y : L) : V)) =
      ((q : hunterProjectedLattice (B.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (B.ofZLatticeBasis ℝ) 0)ᗮ) by
      exact hunterRoundedIntegralLift_center L B q]
    intro hzero
    exact hq (Subtype.ext hzero)
  exact ⟨y, hyne, hyshort, hycenter⟩

set_option maxHeartbeats 1000000 in
-- Dependent projected-lattice rewrites require additional reduction.
open scoped Classical in
/-- A proper-subfield Minkowski vector in a totally real quartic field admits
a second integral vector of the same strict Hunter size bound whose projection
orthogonal to the first vector is nonzero. -/
theorem exists_quartic_second_shortVector
    (K : Type u) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 4)
    (hdisc : |NumberField.discr K| < 725)
    (bz : Basis (Fin 4) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (hbzero :
      (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) =
          euclideanOne K)
    (x : quarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ))
    (hx : x ≠ 0)
    (htop : IntermediateField.adjoin ℚ
      {((quarticHunterAlgebraicIntegerLift K bz x : 𝓞 K) : K)} ≠ ⊤)
    (hshort :
      4 * ‖((x : quarticHunterProjectedLattice
        (bz.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)‖ ^ 2 < 35) :
    ∃ B : Basis (Fin 3) ℤ
        (quarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ)),
      B 0 = x ∧
      ∃ y : quarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ),
        y ≠ 0 ∧
        4 * ‖((y : quarticHunterProjectedLattice
          (bz.ofZLatticeBasis ℝ)) :
          (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)‖ ^ 2 < 35 ∧
        hunterCenterLinearMap ((B.ofZLatticeBasis ℝ) 0)
          (inner_self_ne_zero.mpr ((B.ofZLatticeBasis ℝ).ne_zero 0))
          (((y : quarticHunterProjectedLattice
            (bz.ofZLatticeBasis ℝ)) :
            (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)) ≠ 0 := by
  let b : Basis (Fin 4) ℝ
      (NumberField.mixedEmbedding.euclidean.mixedSpace K) :=
    bz.ofZLatticeBasis ℝ
  let L : Submodule ℤ ((ℝ ∙ b 0)ᗮ) := quarticHunterProjectedLattice b
  obtain ⟨B, hB0⟩ :=
    exists_quarticProjected_basis_zero_eq_shortVector_of_properSubfield
      K hreal hdegree bz hbzero x hx htop hshort
  refine ⟨B, hB0, ?_⟩
  have hinnerCases :=
    quartic_shortVector_inner_self_eq_five_or_eight
      K hreal hdegree bz hbzero x hx htop hshort
  have hIntegral :=
    quarticHunterProjectedLattice_four_mul_inner_integral
      K hreal hdegree bz hbzero
  have hb0 : b 0 =
      (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) := by
    dsimp [b]
    exact bz.ofZLatticeBasis_apply ℝ
      (NumberField.mixedEmbedding.euclidean.integerLattice K) 0
  have hbinner : inner ℝ (b 0) (b 0) = 4 := by
    rw [hb0, hbzero]
    exact inner_euclideanOne_self_eq_four_projection K hreal hdegree
  have hbspan : span ℤ (Set.range b) =
      NumberField.mixedEmbedding.euclidean.integerLattice K := by
    dsimp [b]
    exact bz.ofZLatticeBasis_span ℝ
  have hfull : ZLattice.covolume (span ℤ (Set.range b)) ^ 2 < 725 := by
    rw [hbspan]
    rw [totallyReal_euclidean_integerLattice_covolume_eq_sqrt_discr
      K hreal]
    rw [Real.sq_sqrt (by positivity :
      (0 : ℝ) ≤ (|NumberField.discr K| : ℝ))]
    exact_mod_cast hdisc
  have hLcov : ZLattice.covolume L ^ 2 * 4 =
      ZLattice.covolume (span ℤ (Set.range b)) ^ 2 := by
    change ZLattice.covolume (quarticHunterProjectedLattice b) ^ 2 * 4 = _
    have h := quarticHunterProjectedLattice_covolume_sq_mul_inner_self b
    rw [hbinner] at h
    exact h
  have hLbound : ZLattice.covolume L ^ 2 * 4 < 725 := by
    rw [hLcov]
    exact hfull
  rcases hinnerCases with hfive | height
  · have hBinner : inner ℝ ((B.ofZLatticeBasis ℝ) 0)
        ((B.ofZLatticeBasis ℝ) 0) = 5 := by
      rw [show (B.ofZLatticeBasis ℝ) 0 =
          (((B 0 : L) : (ℝ ∙ b 0)ᗮ)) by
        exact B.ofZLatticeBasis_apply ℝ L 0]
      rw [hB0]
      exact hfive
    exact exists_hunterRounded_shortVector L B 5 (by norm_num)
      hBinner hIntegral 7 (by
        intro r qCov hgauss hquot
        exact gauss_norm_sq_lt_seven r qCov
          (ZLattice.covolume L) hgauss hquot hLbound) (by norm_num)
  · have hBinner : inner ℝ ((B.ofZLatticeBasis ℝ) 0)
        ((B.ofZLatticeBasis ℝ) 0) = 8 := by
      rw [show (B.ofZLatticeBasis ℝ) 0 =
          (((B 0 : L) : (ℝ ∙ b 0)ᗮ)) by
        exact B.ofZLatticeBasis_apply ℝ L 0]
      rw [hB0]
      exact height
    exact exists_hunterRounded_shortVector L B 8 (by norm_num)
      hBinner hIntegral (11 / 2) (by
        intro r qCov hgauss hquot
        exact gauss_norm_sq_lt_eleven_halves r qCov
          (ZLattice.covolume L) hgauss hquot hLbound) (by norm_num)

end

end TraceEuclidean
