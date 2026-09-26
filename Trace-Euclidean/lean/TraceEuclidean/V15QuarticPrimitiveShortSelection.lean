import TraceEuclidean.V15QuarticSecondShortVector
import TraceEuclidean.V15DegreeFourMinkowskiReduction

/-!
# Primitive short-vector selection in degree four

This module closes the remaining short-vector selection step.  A first short
vector in a proper quadratic subfield yields a second transverse short
vector.  If both lifts were imprimitive, their quadratic subfields would be
distinct, have discriminants `5` and `8`, and force quartic discriminant
`1600`, contradicting the standing bound below `725`.
-/

namespace TraceEuclidean

noncomputable section

open NumberField Module Submodule
open scoped NumberField RealInnerProductSpace

universe u

set_option maxHeartbeats 1000000 in
-- Rewriting both dependent orthogonal-complement models needs extra reduction.
open scoped Classical in
/-- A second projected vector with nonzero component orthogonal to the first
cannot lift into the same quadratic subfield as the first vector. -/
theorem v15_quartic_adjoin_ne_of_second_center_ne
    (K : Type u) [Field K] [NumberField K]
    (bz : Basis (Fin 4) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (hbzero :
      (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) =
          v15EuclideanOne K)
    (x y : v15QuarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ))
    (hdegreeE : Module.finrank ℚ
      (IntermediateField.adjoin ℚ
        {((v15QuarticHunterAlgebraicIntegerLift K bz x : 𝓞 K) : K)}) = 2)
    (B : Basis (Fin 3) ℤ
      (v15QuarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ)))
    (hB0 : B 0 = x)
    (hycenter :
      v15HunterCenterLinearMap ((B.ofZLatticeBasis ℝ) 0)
        (inner_self_ne_zero.mpr ((B.ofZLatticeBasis ℝ).ne_zero 0))
        (((y : v15QuarticHunterProjectedLattice
          (bz.ofZLatticeBasis ℝ)) :
          (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)) ≠ 0) :
    IntermediateField.adjoin ℚ
        {((v15QuarticHunterAlgebraicIntegerLift K bz x : 𝓞 K) : K)} ≠
      IntermediateField.adjoin ℚ
        {((v15QuarticHunterAlgebraicIntegerLift K bz y : 𝓞 K) : K)} := by
  intro hfields
  let a : 𝓞 K := v15QuarticHunterAlgebraicIntegerLift K bz x
  let c : 𝓞 K := v15QuarticHunterAlgebraicIntegerLift K bz y
  let E : IntermediateField ℚ K := IntermediateField.adjoin ℚ {(a : K)}
  have hcF : (c : K) ∈ IntermediateField.adjoin ℚ {(c : K)} :=
    IntermediateField.subset_adjoin ℚ {(c : K)}
      (Set.mem_singleton (c : K))
  have hcE : (c : K) ∈ E := by
    change (c : K) ∈ IntermediateField.adjoin ℚ {(a : K)}
    rw [hfields]
    exact hcF
  obtain ⟨r, s, hc⟩ :=
    v15_mem_quadratic_adjoin_eq_rat_add_rat_mul
      K (a : K) (c : K) (by simpa [E, a] using hdegreeE) hcE
  have hbzero' : (bz.ofZLatticeBasis ℝ) 0 = v15EuclideanOne K := by
    rw [show (bz.ofZLatticeBasis ℝ) 0 =
        (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
          NumberField.mixedEmbedding.euclidean.mixedSpace K)) by
      exact bz.ofZLatticeBasis_apply ℝ
        (NumberField.mixedEmbedding.euclidean.integerLattice K) 0]
    exact hbzero
  have hcEmbed : v15EuclideanEmbedding K (c : K) =
      (r : ℝ) • v15EuclideanOne K +
        (s : ℝ) • v15EuclideanEmbedding K (a : K) := by
    rw [hc]
    exact v15_euclideanEmbedding_rat_add_rat_mul K r s (a : K)
  let f := v15HunterCenterLinearMap ((bz.ofZLatticeBasis ℝ) 0)
    (inner_self_ne_zero.mpr ((bz.ofZLatticeBasis ℝ).ne_zero 0))
  have hfc : f (v15EuclideanEmbedding K (c : K)) =
      ((y : v15QuarticHunterProjectedLattice
        (bz.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ) := by
    simpa [f, c, v15EuclideanEmbedding] using
      v15_quarticHunterAlgebraicIntegerLift_center K bz y
  have hfa : f (v15EuclideanEmbedding K (a : K)) =
      ((x : v15QuarticHunterProjectedLattice
        (bz.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ) := by
    simpa [f, a, v15EuclideanEmbedding] using
      v15_quarticHunterAlgebraicIntegerLift_center K bz x
  have hfone : f (v15EuclideanOne K) = 0 := by
    calc
      f (v15EuclideanOne K) = f ((bz.ofZLatticeBasis ℝ) 0) :=
        congrArg f hbzero'.symm
      _ = 0 := v15HunterCenterLinearMap_self
        ((bz.ofZLatticeBasis ℝ) 0)
          (inner_self_ne_zero.mpr ((bz.ofZLatticeBasis ℝ).ne_zero 0))
  have hyx :
      ((y : v15QuarticHunterProjectedLattice
        (bz.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ) =
      (s : ℝ) •
        ((x : v15QuarticHunterProjectedLattice
          (bz.ofZLatticeBasis ℝ)) :
          (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ) := by
    calc
      ((y : v15QuarticHunterProjectedLattice
        (bz.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ) =
          f (v15EuclideanEmbedding K (c : K)) := hfc.symm
      _ = f ((r : ℝ) • v15EuclideanOne K +
          (s : ℝ) • v15EuclideanEmbedding K (a : K)) := by rw [hcEmbed]
      _ = (r : ℝ) • f (v15EuclideanOne K) +
          (s : ℝ) • f (v15EuclideanEmbedding K (a : K)) := by
        rw [map_add, map_smul, map_smul]
      _ = (s : ℝ) • f (v15EuclideanEmbedding K (a : K)) := by
        rw [hfone]
        simp
      _ = (s : ℝ) •
          ((x : v15QuarticHunterProjectedLattice
            (bz.ofZLatticeBasis ℝ)) :
            (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ) := by rw [hfa]
  have hB0real : (B.ofZLatticeBasis ℝ) 0 =
      ((x : v15QuarticHunterProjectedLattice
        (bz.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ) := by
    rw [show (B.ofZLatticeBasis ℝ) 0 =
        (((B 0 : v15QuarticHunterProjectedLattice
          (bz.ofZLatticeBasis ℝ)) :
          (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)) by
      exact B.ofZLatticeBasis_apply ℝ
        (v15QuarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ)) 0]
    rw [hB0]
  have hyB :
      ((y : v15QuarticHunterProjectedLattice
        (bz.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ) =
      (s : ℝ) • (B.ofZLatticeBasis ℝ) 0 := by
    calc
      ((y : v15QuarticHunterProjectedLattice
        (bz.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ) =
          (s : ℝ) •
            ((x : v15QuarticHunterProjectedLattice
              (bz.ofZLatticeBasis ℝ)) :
              (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ) := hyx
      _ = (s : ℝ) • (B.ofZLatticeBasis ℝ) 0 := by rw [hB0real]
  apply hycenter
  rw [hyB]
  exact v15HunterCenterLinearMap_smul_self _ _ _

set_option maxHeartbeats 1000000 in
-- The two dependent short-vector branches and discriminant transports require
-- more reduction than the project-wide default.
open scoped Classical in
/-- Every totally real quartic field below discriminant `725` has a projected
Hunter vector of scaled squared norm below `35` whose lift generates the
field.  Thus the remaining selection input is discharged internally. -/
theorem v15_quartic_primitiveShortSelectionThirtyFive :
    V15QuarticPrimitiveShortSelectionThirtyFiveInput := by
  intro K hreal hdegree hdisc bz hbzero hexists
  obtain ⟨x, hx, hshort⟩ := hexists
  let a : 𝓞 K.1 := v15QuarticHunterAlgebraicIntegerLift K.1 bz x
  by_cases hgenA : IntermediateField.adjoin ℚ {(a : K.1)} = ⊤
  · exact ⟨x, hx, by simpa [a] using hgenA, hshort⟩
  have hdiscK : |NumberField.discr K.1| < 725 := by
    simpa only [NumberFieldCode.discriminant] using hdisc
  obtain ⟨B, hB0, y, hy, hyshort, hycenter⟩ :=
    v15_exists_quartic_second_shortVector
      K.1 hreal hdegree hdiscK bz hbzero x hx
        (by simpa [a] using hgenA) hshort
  let c : 𝓞 K.1 := v15QuarticHunterAlgebraicIntegerLift K.1 bz y
  by_cases hgenC : IntermediateField.adjoin ℚ {(c : K.1)} = ⊤
  · exact ⟨y, hy, by simpa [c] using hgenC, hyshort⟩
  exfalso
  letI : NumberField.IsTotallyReal K.1 := hreal
  let E : IntermediateField ℚ K.1 :=
    IntermediateField.adjoin ℚ {(a : K.1)}
  let F : IntermediateField ℚ K.1 :=
    IntermediateField.adjoin ℚ {(c : K.1)}
  have hnotRatA : ¬ ∃ q : ℚ, (a : K.1) = algebraMap ℚ K.1 q := by
    simpa [a] using
      v15_quarticHunterAlgebraicIntegerLift_not_rat
        K.1 bz hbzero x hx
  have hnotRatC : ¬ ∃ q : ℚ, (c : K.1) = algebraMap ℚ K.1 q := by
    simpa [c] using
      v15_quarticHunterAlgebraicIntegerLift_not_rat
        K.1 bz hbzero y hy
  have hbotE : E ≠ ⊥ := by
    intro hE
    have haE : (a : K.1) ∈ E := by
      simpa [E] using IntermediateField.subset_adjoin ℚ {(a : K.1)}
        (Set.mem_singleton (a : K.1))
    rw [hE, IntermediateField.mem_bot] at haE
    rcases haE with ⟨q, hq⟩
    exact hnotRatA ⟨q, hq.symm⟩
  have hbotF : F ≠ ⊥ := by
    intro hF
    have hcF : (c : K.1) ∈ F := by
      simpa [F] using IntermediateField.subset_adjoin ℚ {(c : K.1)}
        (Set.mem_singleton (c : K.1))
    rw [hF, IntermediateField.mem_bot] at hcF
    rcases hcF with ⟨q, hq⟩
    exact hnotRatC ⟨q, hq.symm⟩
  have hdegreeE : Module.finrank ℚ E = 2 :=
    (v15_quartic_properIntermediateField_finranks
      K.1 hdegree E hbotE (by simpa [E, a] using hgenA)).1
  have hdegreeF : Module.finrank ℚ F = 2 :=
    (v15_quartic_properIntermediateField_finranks
      K.1 hdegree F hbotF (by simpa [F, c] using hgenC)).1
  have hspreadA :
      4 * Algebra.trace ℚ K.1 ((a : K.1) ^ 2) -
          (Algebra.trace ℚ K.1 (a : K.1)) ^ 2 < 35 := by
    simpa [a] using
      v15_quarticHunterAlgebraicIntegerLift_trace_spread_lt
        K.1 hreal hdegree bz hbzero x hshort
  have hspreadC :
      4 * Algebra.trace ℚ K.1 ((c : K.1) ^ 2) -
          (Algebra.trace ℚ K.1 (c : K.1)) ^ 2 < 35 := by
    simpa [c] using
      v15_quarticHunterAlgebraicIntegerLift_trace_spread_lt
        K.1 hreal hdegree bz hbzero y hyshort
  have hrowsE : (NumberField.discr E).natAbs = 5 ∨
      (NumberField.discr E).natAbs = 8 := by
    simpa [E, a] using
      v15_quartic_adjoin_discriminant_eq_five_or_eight_of_trace_spread_lt
        K.1 hreal hdegree a hnotRatA
          (by simpa [E, a] using hgenA) hspreadA
  have hrowsF : (NumberField.discr F).natAbs = 5 ∨
      (NumberField.discr F).natAbs = 8 := by
    simpa [F, c] using
      v15_quartic_adjoin_discriminant_eq_five_or_eight_of_trace_spread_lt
        K.1 hreal hdegree c hnotRatC
          (by simpa [F, c] using hgenC) hspreadC
  have hpowerA : Algebra.discr ℤ
      (v15QuadraticPowerFamily E
        (v15AdjoinRingOfIntegersGenerator K.1 a)) =
      NumberField.discr E := by
    simpa [E, a] using
      v15_quartic_adjoin_powerFamily_discr_eq_field_of_trace_spread_lt
        K.1 hreal hdegree a hnotRatA
          (by simpa [E, a] using hgenA) hspreadA
  have hpowerC : Algebra.discr ℤ
      (v15QuadraticPowerFamily F
        (v15AdjoinRingOfIntegersGenerator K.1 c)) =
      NumberField.discr F := by
    simpa [F, c] using
      v15_quartic_adjoin_powerFamily_discr_eq_field_of_trace_spread_lt
        K.1 hreal hdegree c hnotRatC
          (by simpa [F, c] using hgenC) hspreadC
  have hneEF : E ≠ F := by
    simpa [E, F, a, c] using
      v15_quartic_adjoin_ne_of_second_center_ne
        K.1 bz hbzero x y (by simpa [E, a] using hdegreeE)
          B hB0 hycenter
  have hposE : 0 < NumberField.discr E := by
    apply Int.sign_eq_one_iff_pos.mp
    rw [NumberField.sign_discr,
      NumberField.IsTotallyReal.nrComplexPlaces_eq_zero]
    norm_num
  have hposF : 0 < NumberField.discr F := by
    apply Int.sign_eq_one_iff_pos.mp
    rw [NumberField.sign_discr,
      NumberField.IsTotallyReal.nrComplexPlaces_eq_zero]
    norm_num
  have hdiscE : NumberField.discr E = 5 ∨
      NumberField.discr E = 8 := by
    rcases hrowsE with hfive | height
    · left
      calc
        NumberField.discr E = |NumberField.discr E| :=
          (abs_of_pos hposE).symm
        _ = ((NumberField.discr E).natAbs : ℤ) :=
          (Int.natCast_natAbs (NumberField.discr E)).symm
        _ = 5 := by exact_mod_cast hfive
    · right
      calc
        NumberField.discr E = |NumberField.discr E| :=
          (abs_of_pos hposE).symm
        _ = ((NumberField.discr E).natAbs : ℤ) :=
          (Int.natCast_natAbs (NumberField.discr E)).symm
        _ = 8 := by exact_mod_cast height
  have hdiscF : NumberField.discr F = 5 ∨
      NumberField.discr F = 8 := by
    rcases hrowsF with hfive | height
    · left
      calc
        NumberField.discr F = |NumberField.discr F| :=
          (abs_of_pos hposF).symm
        _ = ((NumberField.discr F).natAbs : ℤ) :=
          (Int.natCast_natAbs (NumberField.discr F)).symm
        _ = 5 := by exact_mod_cast hfive
    · right
      calc
        NumberField.discr F = |NumberField.discr F| :=
          (abs_of_pos hposF).symm
        _ = ((NumberField.discr F).natAbs : ℤ) :=
          (Int.natCast_natAbs (NumberField.discr F)).symm
        _ = 8 := by exact_mod_cast height
  rcases hdiscE with hE5 | hE8 <;>
    rcases hdiscF with hF5 | hF8
  · apply hneEF
    exact v15_quadratic_adjoin_eq_of_powerFamily_discr_eq
      K.1 a c hdegreeE hdegreeF hpowerA hpowerC (hE5.trans hF5.symm)
  · have hcoprime : IsCoprime (NumberField.discr E)
        (NumberField.discr F) := by
      rw [hE5, hF8]
      norm_num
    have hquartic :=
      v15_quartic_discriminant_eq_product_of_coprime_quadratic_subfields
        K.1 hdegree E F hdegreeE hdegreeF hneEF hcoprime
    rw [hE5, hF8] at hquartic
    norm_num at hquartic
    have hdiscKNat : (NumberField.discr K.1).natAbs < 725 := by
      rw [← Nat.cast_lt (α := ℤ), Int.natCast_natAbs]
      exact hdiscK
    omega
  · have hcoprime : IsCoprime (NumberField.discr E)
        (NumberField.discr F) := by
      rw [hE8, hF5]
      norm_num
    have hquartic :=
      v15_quartic_discriminant_eq_product_of_coprime_quadratic_subfields
        K.1 hdegree E F hdegreeE hdegreeF hneEF hcoprime
    rw [hE8, hF5] at hquartic
    norm_num at hquartic
    have hdiscKNat : (NumberField.discr K.1).natAbs < 725 := by
      rw [← Nat.cast_lt (α := ℤ), Int.natCast_natAbs]
      exact hdiscK
    omega
  · apply hneEF
    exact v15_quadratic_adjoin_eq_of_powerFamily_discr_eq
      K.1 a c hdegreeE hdegreeF hpowerA hpowerC (hE8.trans hF8.symm)

/-- Unconditional degree-four field-discriminant bound obtained from the
internally proved primitive short-vector selection. -/
theorem v15_coded_degree_four_discriminant_ge_725
    (K : CodedNumberField) (hreal : NumberField.IsTotallyReal K.1)
    (hdegree : Module.finrank ℚ K.1 = 4) :
    725 ≤ |K.discriminant| :=
  v15_coded_degree_four_discriminant_ge_725_of_minkowski_selection
    v15_quartic_primitiveShortSelectionThirtyFive K hreal hdegree

end

end TraceEuclidean
