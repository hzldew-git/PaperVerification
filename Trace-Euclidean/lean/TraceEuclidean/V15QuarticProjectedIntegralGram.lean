import TraceEuclidean.V15QuarticShortVectorSubfield
import TraceEuclidean.V15GaussHermite
import Mathlib.NumberTheory.NumberField.Norm

/-!
# Integral Gram form of the quartic Hunter lattice

Four times the Gram form of the centered quartic ring-of-integers lattice is
integer valued.  This supplies the arithmetic hypothesis needed by the sharp
binary Gauss theorem after projection along a quadratic-subfield direction.
-/

namespace TraceEuclidean

noncomputable section

open NumberField Module Submodule
open scoped NumberField

open scoped Classical in
/-- Four times every inner product in the centered quartic lattice is an
integer. -/
theorem v15_quarticHunterProjectedLattice_four_mul_inner_integral
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 4)
    (bz : Basis (Fin 4) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (hbzero :
      (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) =
          v15EuclideanOne K) :
    ∀ x y : v15QuarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ),
      ∃ z : ℤ, (z : ℝ) = 4 *
        inner ℝ
          (((x : v15QuarticHunterProjectedLattice
            (bz.ofZLatticeBasis ℝ)) :
              (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ))
          (((y : v15QuarticHunterProjectedLattice
            (bz.ofZLatticeBasis ℝ)) :
              (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)) := by
  letI : NumberField.IsTotallyReal K := hreal
  intro x y
  let a : 𝓞 K := v15QuarticHunterAlgebraicIntegerLift K bz x
  let c : 𝓞 K := v15QuarticHunterAlgebraicIntegerLift K bz y
  let ta : ℤ := Algebra.trace ℤ (𝓞 K) a
  let tc : ℤ := Algebra.trace ℤ (𝓞 K) c
  let tac : ℤ := Algebra.trace ℤ (𝓞 K) (a * c)
  refine ⟨4 * tac - ta * tc, ?_⟩
  have hbzero' : (bz.ofZLatticeBasis ℝ) 0 = v15EuclideanOne K := by
    rw [show (bz.ofZLatticeBasis ℝ) 0 =
        (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
          NumberField.mixedEmbedding.euclidean.mixedSpace K)) by
      exact bz.ofZLatticeBasis_apply ℝ
        (NumberField.mixedEmbedding.euclidean.integerLattice K) 0]
    exact hbzero
  have hcenterX := v15_quarticHunterAlgebraicIntegerLift_center K bz x
  have hcenterY := v15_quarticHunterAlgebraicIntegerLift_center K bz y
  have hcenterXval := congrArg Subtype.val hcenterX
  have hcenterYval := congrArg Subtype.val hcenterY
  have htaQ : (ta : ℚ) = Algebra.trace ℚ K (a : K) := by
    simpa [ta, a] using (Algebra.coe_trace_int (K := K)
      (v15QuarticHunterAlgebraicIntegerLift K bz x))
  have htcQ : (tc : ℚ) = Algebra.trace ℚ K (c : K) := by
    simpa [tc, c] using (Algebra.coe_trace_int (K := K)
      (v15QuarticHunterAlgebraicIntegerLift K bz y))
  have htacQ : (tac : ℚ) = Algebra.trace ℚ K ((a : K) * (c : K)) := by
    simpa [tac, a, c, map_mul] using (Algebra.coe_trace_int (K := K)
      (v15QuarticHunterAlgebraicIntegerLift K bz x *
        v15QuarticHunterAlgebraicIntegerLift K bz y))
  have htaR : (ta : ℝ) =
      ((Algebra.trace ℚ K (a : K) : ℚ) : ℝ) := by
    exact_mod_cast htaQ
  have htcR : (tc : ℝ) =
      ((Algebra.trace ℚ K (c : K) : ℚ) : ℝ) := by
    exact_mod_cast htcQ
  have htacR : (tac : ℝ) =
      ((Algebra.trace ℚ K ((a : K) * (c : K)) : ℚ) : ℝ) := by
    exact_mod_cast htacQ
  push_cast
  rw [htaR, htcR, htacR]
  change 4 * ((Algebra.trace ℚ K ((a : K) * (c : K)) : ℚ) : ℝ) -
      ((Algebra.trace ℚ K (a : K) : ℚ) : ℝ) *
        ((Algebra.trace ℚ K (c : K) : ℚ) : ℝ) =
    4 * inner ℝ
      ((((x : v15QuarticHunterProjectedLattice
        (bz.ofZLatticeBasis ℝ)) :
          (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)) :
            NumberField.mixedEmbedding.euclidean.mixedSpace K)
      ((((y : v15QuarticHunterProjectedLattice
        (bz.ofZLatticeBasis ℝ)) :
          (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)) :
            NumberField.mixedEmbedding.euclidean.mixedSpace K)
  rw [← hcenterXval, ← hcenterYval]
  rw [v15HunterCenterLinearMap_apply, v15HunterCenterLinearMap_apply]
  rw [v15_inner_center_center _ _ _
    (inner_self_ne_zero.mpr ((bz.ofZLatticeBasis ℝ).ne_zero 0))]
  rw [hbzero']
  change 4 * ((Algebra.trace ℚ K ((a : K) * (c : K)) : ℚ) : ℝ) -
      ((Algebra.trace ℚ K (a : K) : ℚ) : ℝ) *
        ((Algebra.trace ℚ K (c : K) : ℚ) : ℝ) =
    4 * (inner ℝ (v15EuclideanEmbedding K (a : K))
        (v15EuclideanEmbedding K (c : K)) -
      inner ℝ (v15EuclideanOne K) (v15EuclideanEmbedding K (a : K)) *
        inner ℝ (v15EuclideanOne K) (v15EuclideanEmbedding K (c : K)) /
          inner ℝ (v15EuclideanOne K) (v15EuclideanOne K))
  rw [v15_inner_euclideanEmbedding_mul_eq_trace]
  rw [v15_inner_euclideanOne_euclideanEmbedding,
    v15_inner_euclideanOne_euclideanEmbedding]
  rw [v15_inner_euclideanOne_self_eq_four_projection K hreal hdegree]
  ring

end

end TraceEuclidean
