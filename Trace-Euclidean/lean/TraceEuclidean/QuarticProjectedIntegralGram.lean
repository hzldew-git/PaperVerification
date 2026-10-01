import TraceEuclidean.QuarticShortVectorSubfield
import TraceEuclidean.GaussHermite
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
theorem quarticHunterProjectedLattice_four_mul_inner_integral
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 4)
    (bz : Basis (Fin 4) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (hbzero :
      (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) =
          euclideanOne K) :
    ∀ x y : quarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ),
      ∃ z : ℤ, (z : ℝ) = 4 *
        inner ℝ
          (((x : quarticHunterProjectedLattice
            (bz.ofZLatticeBasis ℝ)) :
              (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ))
          (((y : quarticHunterProjectedLattice
            (bz.ofZLatticeBasis ℝ)) :
              (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)) := by
  letI : NumberField.IsTotallyReal K := hreal
  intro x y
  let a : 𝓞 K := quarticHunterAlgebraicIntegerLift K bz x
  let c : 𝓞 K := quarticHunterAlgebraicIntegerLift K bz y
  let ta : ℤ := Algebra.trace ℤ (𝓞 K) a
  let tc : ℤ := Algebra.trace ℤ (𝓞 K) c
  let tac : ℤ := Algebra.trace ℤ (𝓞 K) (a * c)
  refine ⟨4 * tac - ta * tc, ?_⟩
  have hbzero' : (bz.ofZLatticeBasis ℝ) 0 = euclideanOne K := by
    rw [show (bz.ofZLatticeBasis ℝ) 0 =
        (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
          NumberField.mixedEmbedding.euclidean.mixedSpace K)) by
      exact bz.ofZLatticeBasis_apply ℝ
        (NumberField.mixedEmbedding.euclidean.integerLattice K) 0]
    exact hbzero
  have hcenterX := quarticHunterAlgebraicIntegerLift_center K bz x
  have hcenterY := quarticHunterAlgebraicIntegerLift_center K bz y
  have hcenterXval := congrArg Subtype.val hcenterX
  have hcenterYval := congrArg Subtype.val hcenterY
  have htaQ : (ta : ℚ) = Algebra.trace ℚ K (a : K) := by
    simpa [ta, a] using (Algebra.coe_trace_int (K := K)
      (quarticHunterAlgebraicIntegerLift K bz x))
  have htcQ : (tc : ℚ) = Algebra.trace ℚ K (c : K) := by
    simpa [tc, c] using (Algebra.coe_trace_int (K := K)
      (quarticHunterAlgebraicIntegerLift K bz y))
  have htacQ : (tac : ℚ) = Algebra.trace ℚ K ((a : K) * (c : K)) := by
    simpa [tac, a, c, map_mul] using (Algebra.coe_trace_int (K := K)
      (quarticHunterAlgebraicIntegerLift K bz x *
        quarticHunterAlgebraicIntegerLift K bz y))
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
      ((((x : quarticHunterProjectedLattice
        (bz.ofZLatticeBasis ℝ)) :
          (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)) :
            NumberField.mixedEmbedding.euclidean.mixedSpace K)
      ((((y : quarticHunterProjectedLattice
        (bz.ofZLatticeBasis ℝ)) :
          (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)) :
            NumberField.mixedEmbedding.euclidean.mixedSpace K)
  rw [← hcenterXval, ← hcenterYval]
  rw [hunterCenterLinearMap_apply, hunterCenterLinearMap_apply]
  rw [inner_center_center _ _ _
    (inner_self_ne_zero.mpr ((bz.ofZLatticeBasis ℝ).ne_zero 0))]
  rw [hbzero']
  change 4 * ((Algebra.trace ℚ K ((a : K) * (c : K)) : ℚ) : ℝ) -
      ((Algebra.trace ℚ K (a : K) : ℚ) : ℝ) *
        ((Algebra.trace ℚ K (c : K) : ℚ) : ℝ) =
    4 * (inner ℝ (euclideanEmbedding K (a : K))
        (euclideanEmbedding K (c : K)) -
      inner ℝ (euclideanOne K) (euclideanEmbedding K (a : K)) *
        inner ℝ (euclideanOne K) (euclideanEmbedding K (c : K)) /
          inner ℝ (euclideanOne K) (euclideanOne K))
  rw [inner_euclideanEmbedding_mul_eq_trace]
  rw [inner_euclideanOne_euclideanEmbedding,
    inner_euclideanOne_euclideanEmbedding]
  rw [inner_euclideanOne_self_eq_four_projection K hreal hdegree]
  ring

end

end TraceEuclidean
