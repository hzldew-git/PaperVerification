import TraceEuclidean.V15QuarticSubfieldReduction
import TraceEuclidean.V15QuadraticGeneratorArithmetic

/-!
# Quadratic subfields detected by short quartic vectors

A nonrational integral element of a quartic field which does not generate the
quartic field generates a quadratic subfield.  This module converts the
quartic centered trace expression of such an element into the discriminant
of its quadratic power order.
-/

namespace TraceEuclidean

noncomputable section

open NumberField Module
open scoped NumberField

/-- If a nonrational algebraic integer in a totally real quartic field lies in
a proper subfield and has quartic trace spread below `35`, then the generated
quadratic subfield has field discriminant `5` or `8`. -/
theorem v15_quartic_adjoin_discriminant_eq_five_or_eight_of_trace_spread_lt
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hnotRat : ¬ ∃ q : ℚ, (a : K) = algebraMap ℚ K q)
    (htop : IntermediateField.adjoin ℚ {(a : K)} ≠ ⊤)
    (hspread :
      4 * Algebra.trace ℚ K ((a : K) ^ 2) -
          (Algebra.trace ℚ K (a : K)) ^ 2 < 35) :
    let E := IntermediateField.adjoin ℚ {(a : K)}
    (NumberField.discr E).natAbs = 5 ∨
      (NumberField.discr E).natAbs = 8 := by
  letI : NumberField.IsTotallyReal K := hreal
  let E : IntermediateField ℚ K :=
    IntermediateField.adjoin ℚ {(a : K)}
  have hbot : E ≠ ⊥ := by
    intro hE
    have haE : (a : K) ∈ E :=
      IntermediateField.subset_adjoin ℚ {(a : K)} (Set.mem_singleton (a : K))
    rw [hE, IntermediateField.mem_bot] at haE
    rcases haE with ⟨q, hq⟩
    exact hnotRat ⟨q, hq.symm⟩
  have hdegreeE : Module.finrank ℚ E = 2 :=
    (v15_quartic_properIntermediateField_finranks
      K hdegree E hbot htop).1
  have hdegreeKE : Module.finrank E K = 2 :=
    (v15_quartic_properIntermediateField_finranks
      K hdegree E hbot htop).2
  let aE : E := IntermediateField.AdjoinSimple.gen ℚ (a : K)
  have haEint : IsIntegral ℤ aE := by
    apply (isIntegral_algHom_iff
      (E.val.restrictScalars ℤ) E.val.injective).mp
    simpa [aE, E] using a.isIntegral_coe
  let aO : 𝓞 E := ⟨aE, haEint⟩
  have hgenE : IntermediateField.adjoin ℚ {(aO : E)} = ⊤ := by
    let hint : IsIntegral ℚ (a : K) := IsIntegral.of_finite ℚ (a : K)
    let pb : PowerBasis ℚ E := IntermediateField.adjoin.powerBasis hint
    simpa [aO, aE, E, pb] using pb.adjoin_gen_eq_top
  have haMap : algebraMap E K (aO : E) = (a : K) := by
    rfl
  have htraceOne : Algebra.trace ℚ K (a : K) =
      2 * Algebra.trace ℚ E (aO : E) := by
    calc
      Algebra.trace ℚ K (a : K) =
          Algebra.trace ℚ E (Algebra.trace E K (a : K)) :=
        (Algebra.trace_trace (a : K)).symm
      _ = Algebra.trace ℚ E
          (Algebra.trace E K (algebraMap E K (aO : E))) := by
        rw [haMap]
      _ = 2 * Algebra.trace ℚ E (aO : E) := by
        rw [Algebra.trace_algebraMap, hdegreeKE]
        simpa [Algebra.smul_def] using
          map_smul (Algebra.trace ℚ E) (2 : ℚ) (aO : E)
  have htraceSq : Algebra.trace ℚ K ((a : K) ^ 2) =
      2 * Algebra.trace ℚ E ((aO : E) ^ 2) := by
    have haMapSq : algebraMap E K ((aO : E) ^ 2) = (a : K) ^ 2 := by
      rw [map_pow, haMap]
    calc
      Algebra.trace ℚ K ((a : K) ^ 2) =
          Algebra.trace ℚ E (Algebra.trace E K ((a : K) ^ 2)) :=
        (Algebra.trace_trace ((a : K) ^ 2)).symm
      _ = Algebra.trace ℚ E
          (Algebra.trace E K (algebraMap E K ((aO : E) ^ 2))) := by
        rw [haMapSq]
      _ = 2 * Algebra.trace ℚ E ((aO : E) ^ 2) := by
        rw [Algebra.trace_algebraMap, hdegreeKE]
        simpa [Algebra.smul_def] using
          map_smul (Algebra.trace ℚ E) (2 : ℚ) ((aO : E) ^ 2)
  obtain ⟨bO, hbO⟩ := v15_exists_ringOfIntegers_basis_one_dim_two E hdegreeE
  obtain ⟨index, hindex, hindexDisc⟩ :=
    v15_quadratic_exists_positive_index E hdegreeE aO hgenE bO
  let delta : ℤ := Algebra.discr ℤ (v15QuadraticPowerFamily E aO)
  have hdeltaTrace : (delta : ℚ) =
      2 * Algebra.trace ℚ E ((aO : E) ^ 2) -
        (Algebra.trace ℚ E (aO : E)) ^ 2 := by
    simpa [delta] using
      v15_quadraticPowerFamily_discr_cast_eq_trace E hdegreeE aO
  have hspreadDelta :
      4 * Algebra.trace ℚ K ((a : K) ^ 2) -
          (Algebra.trace ℚ K (a : K)) ^ 2 = 4 * (delta : ℚ) := by
    rw [htraceOne, htraceSq, hdeltaTrace]
    ring
  have hdeltaLt : delta < 9 := by
    rw [hspreadDelta] at hspread
    exact_mod_cast (show (delta : ℚ) < 9 by linarith)
  have hdiscPos : 0 < NumberField.discr E := by
    have hsign : (NumberField.discr E).sign = 1 := by
      rw [NumberField.sign_discr,
        NumberField.IsTotallyReal.nrComplexPlaces_eq_zero]
      norm_num
    exact Int.sign_eq_one_iff_pos.mp hsign
  have hdeltaEq : delta = (index : ℤ) ^ 2 * NumberField.discr E := by
    simpa [delta] using hindexDisc
  have hdiscLe : (NumberField.discr E).natAbs ≤ 8 := by
    have hindexCast : (1 : ℤ) ≤ (index : ℤ) := by
      exact_mod_cast hindex
    have hindexSq : (1 : ℤ) ≤ (index : ℤ) ^ 2 := by
      nlinarith
    have hdeltaPos : 0 < delta := by
      rw [hdeltaEq]
      positivity
    have hdiscLeInt : NumberField.discr E ≤ 8 := by
      rw [hdeltaEq] at hdeltaLt
      nlinarith
    have hdiscLeCast : ((NumberField.discr E).natAbs : ℤ) ≤ 8 := by
      rw [Int.natCast_natAbs, abs_of_pos hdiscPos]
      exact hdiscLeInt
    exact_mod_cast hdiscLeCast
  have hrows := v15_totallyReal_quadratic_discriminant_rows
    E (inferInstance : NumberField.IsTotallyReal E) hdegreeE (by omega :
      (NumberField.discr E).natAbs ≤ 26)
  rcases hrows with h5 | h8 | h12 | h13 | h17 | h21 | h24
  · exact Or.inl h5
  · exact Or.inr h8
  all_goals omega

/-- Under the same shortness hypothesis, the integral element already gives
an integral basis of its quadratic adjoin field. -/
theorem v15_quartic_adjoin_powerFamily_discr_eq_field_of_trace_spread_lt
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hnotRat : ¬ ∃ q : ℚ, (a : K) = algebraMap ℚ K q)
    (htop : IntermediateField.adjoin ℚ {(a : K)} ≠ ⊤)
    (hspread :
      4 * Algebra.trace ℚ K ((a : K) ^ 2) -
          (Algebra.trace ℚ K (a : K)) ^ 2 < 35) :
    let E := IntermediateField.adjoin ℚ {(a : K)}
    Algebra.discr ℤ
        (v15QuadraticPowerFamily E
          (v15AdjoinRingOfIntegersGenerator K a)) =
      NumberField.discr E := by
  letI : NumberField.IsTotallyReal K := hreal
  let E : IntermediateField ℚ K :=
    IntermediateField.adjoin ℚ {(a : K)}
  have hbot : E ≠ ⊥ := by
    intro hE
    have haE : (a : K) ∈ E :=
      IntermediateField.subset_adjoin ℚ {(a : K)} (Set.mem_singleton (a : K))
    rw [hE, IntermediateField.mem_bot] at haE
    rcases haE with ⟨q, hq⟩
    exact hnotRat ⟨q, hq.symm⟩
  have hdegreeE : Module.finrank ℚ E = 2 :=
    (v15_quartic_properIntermediateField_finranks
      K hdegree E hbot htop).1
  have hdegreeKE : Module.finrank E K = 2 :=
    (v15_quartic_properIntermediateField_finranks
      K hdegree E hbot htop).2
  let aO : 𝓞 E := v15AdjoinRingOfIntegersGenerator K a
  have hgenE : IntermediateField.adjoin ℚ {(aO : E)} = ⊤ := by
    simpa [E, aO] using v15AdjoinRingOfIntegersGenerator_adjoin_eq_top K a
  have haMap : algebraMap E K (aO : E) = (a : K) := by
    rfl
  have htraceOne : Algebra.trace ℚ K (a : K) =
      2 * Algebra.trace ℚ E (aO : E) := by
    calc
      Algebra.trace ℚ K (a : K) =
          Algebra.trace ℚ E (Algebra.trace E K (a : K)) :=
        (Algebra.trace_trace (a : K)).symm
      _ = Algebra.trace ℚ E
          (Algebra.trace E K (algebraMap E K (aO : E))) := by
        rw [haMap]
      _ = 2 * Algebra.trace ℚ E (aO : E) := by
        rw [Algebra.trace_algebraMap, hdegreeKE]
        simpa [Algebra.smul_def] using
          map_smul (Algebra.trace ℚ E) (2 : ℚ) (aO : E)
  have htraceSq : Algebra.trace ℚ K ((a : K) ^ 2) =
      2 * Algebra.trace ℚ E ((aO : E) ^ 2) := by
    have haMapSq : algebraMap E K ((aO : E) ^ 2) = (a : K) ^ 2 := by
      rw [map_pow, haMap]
    calc
      Algebra.trace ℚ K ((a : K) ^ 2) =
          Algebra.trace ℚ E (Algebra.trace E K ((a : K) ^ 2)) :=
        (Algebra.trace_trace ((a : K) ^ 2)).symm
      _ = Algebra.trace ℚ E
          (Algebra.trace E K (algebraMap E K ((aO : E) ^ 2))) := by
        rw [haMapSq]
      _ = 2 * Algebra.trace ℚ E ((aO : E) ^ 2) := by
        rw [Algebra.trace_algebraMap, hdegreeKE]
        simpa [Algebra.smul_def] using
          map_smul (Algebra.trace ℚ E) (2 : ℚ) ((aO : E) ^ 2)
  let delta : ℤ := Algebra.discr ℤ (v15QuadraticPowerFamily E aO)
  have hdeltaTrace : (delta : ℚ) =
      2 * Algebra.trace ℚ E ((aO : E) ^ 2) -
        (Algebra.trace ℚ E (aO : E)) ^ 2 := by
    simpa [delta] using
      v15_quadraticPowerFamily_discr_cast_eq_trace E hdegreeE aO
  have hspreadDelta :
      4 * Algebra.trace ℚ K ((a : K) ^ 2) -
          (Algebra.trace ℚ K (a : K)) ^ 2 = 4 * (delta : ℚ) := by
    rw [htraceOne, htraceSq, hdeltaTrace]
    ring
  have hdeltaLt : (delta : ℚ) < 9 := by
    rw [hspreadDelta] at hspread
    linarith
  simpa [E, aO, delta] using
    v15_quadraticPowerFamily_discr_eq_field_of_lt_nine
      E (inferInstance : NumberField.IsTotallyReal E) hdegreeE aO hgenE
        (by simpa [delta] using hdeltaLt)

/-- For a short quartic integral element in a proper subfield, its quartic
trace spread is four times the discriminant of the generated quadratic
field. -/
theorem v15_quartic_adjoin_trace_spread_eq_four_fieldDiscriminant
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hnotRat : ¬ ∃ q : ℚ, (a : K) = algebraMap ℚ K q)
    (htop : IntermediateField.adjoin ℚ {(a : K)} ≠ ⊤)
    (hspread :
      4 * Algebra.trace ℚ K ((a : K) ^ 2) -
          (Algebra.trace ℚ K (a : K)) ^ 2 < 35) :
    let E := IntermediateField.adjoin ℚ {(a : K)}
    4 * Algebra.trace ℚ K ((a : K) ^ 2) -
        (Algebra.trace ℚ K (a : K)) ^ 2 =
      4 * (NumberField.discr E : ℚ) := by
  letI : NumberField.IsTotallyReal K := hreal
  let E : IntermediateField ℚ K := IntermediateField.adjoin ℚ {(a : K)}
  let aO : 𝓞 E := v15AdjoinRingOfIntegersGenerator K a
  have hbot : E ≠ ⊥ := by
    intro hE
    have haE : (a : K) ∈ E :=
      IntermediateField.subset_adjoin ℚ {(a : K)} (Set.mem_singleton (a : K))
    rw [hE, IntermediateField.mem_bot] at haE
    rcases haE with ⟨q, hq⟩
    exact hnotRat ⟨q, hq.symm⟩
  have hdegreeE : Module.finrank ℚ E = 2 :=
    (v15_quartic_properIntermediateField_finranks
      K hdegree E hbot htop).1
  have hdegreeKE : Module.finrank E K = 2 :=
    (v15_quartic_properIntermediateField_finranks
      K hdegree E hbot htop).2
  have haMap : algebraMap E K (aO : E) = (a : K) := by
    rfl
  have htraceOne : Algebra.trace ℚ K (a : K) =
      2 * Algebra.trace ℚ E (aO : E) := by
    calc
      Algebra.trace ℚ K (a : K) =
          Algebra.trace ℚ E (Algebra.trace E K (a : K)) :=
        (Algebra.trace_trace (a : K)).symm
      _ = Algebra.trace ℚ E
          (Algebra.trace E K (algebraMap E K (aO : E))) := by rw [haMap]
      _ = 2 * Algebra.trace ℚ E (aO : E) := by
        rw [Algebra.trace_algebraMap, hdegreeKE]
        simpa [Algebra.smul_def] using
          map_smul (Algebra.trace ℚ E) (2 : ℚ) (aO : E)
  have htraceSq : Algebra.trace ℚ K ((a : K) ^ 2) =
      2 * Algebra.trace ℚ E ((aO : E) ^ 2) := by
    have haMapSq : algebraMap E K ((aO : E) ^ 2) = (a : K) ^ 2 := by
      rw [map_pow, haMap]
    calc
      Algebra.trace ℚ K ((a : K) ^ 2) =
          Algebra.trace ℚ E (Algebra.trace E K ((a : K) ^ 2)) :=
        (Algebra.trace_trace ((a : K) ^ 2)).symm
      _ = Algebra.trace ℚ E
          (Algebra.trace E K (algebraMap E K ((aO : E) ^ 2))) := by rw [haMapSq]
      _ = 2 * Algebra.trace ℚ E ((aO : E) ^ 2) := by
        rw [Algebra.trace_algebraMap, hdegreeKE]
        simpa [Algebra.smul_def] using
          map_smul (Algebra.trace ℚ E) (2 : ℚ) ((aO : E) ^ 2)
  have hdisc : Algebra.discr ℤ (v15QuadraticPowerFamily E aO) =
      NumberField.discr E := by
    simpa [E, aO] using
      v15_quartic_adjoin_powerFamily_discr_eq_field_of_trace_spread_lt
        K hreal hdegree a hnotRat htop hspread
  calc
    4 * Algebra.trace ℚ K ((a : K) ^ 2) -
          (Algebra.trace ℚ K (a : K)) ^ 2 =
        4 * ((Algebra.discr ℤ
          (v15QuadraticPowerFamily E aO) : ℤ) : ℚ) := by
      rw [htraceOne, htraceSq,
        v15_quadraticPowerFamily_discr_cast_eq_trace E hdegreeE aO]
      ring
    _ = 4 * (NumberField.discr E : ℚ) := by rw [hdisc]

open scoped Classical in
/-- A short vector in the quartic centered lattice gives the corresponding
strict bound for the quartic trace spread of its algebraic-integer lift. -/
theorem v15_quarticHunterAlgebraicIntegerLift_trace_spread_lt
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 4)
    (bz : Basis (Fin 4) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (hbzero :
      (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) =
          v15EuclideanOne K)
    (x : v15QuarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ))
    (hshort :
      4 * ‖((x : v15QuarticHunterProjectedLattice
        (bz.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)‖ ^ 2 < 35) :
    let a := v15QuarticHunterAlgebraicIntegerLift K bz x
    4 * Algebra.trace ℚ K ((a : K) ^ 2) -
        (Algebra.trace ℚ K (a : K)) ^ 2 < 35 := by
  let a : 𝓞 K := v15QuarticHunterAlgebraicIntegerLift K bz x
  have hbzero' : (bz.ofZLatticeBasis ℝ) 0 = v15EuclideanOne K := by
    rw [show (bz.ofZLatticeBasis ℝ) 0 =
        (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
          NumberField.mixedEmbedding.euclidean.mixedSpace K)) by
      exact bz.ofZLatticeBasis_apply ℝ
        (NumberField.mixedEmbedding.euclidean.integerLattice K) 0]
    exact hbzero
  have he : inner ℝ (v15EuclideanOne K) (v15EuclideanOne K) ≠ 0 := by
    rw [v15_inner_euclideanOne_self_eq_four K hreal hdegree]
    norm_num
  have hshortBasis :
      4 * ‖v15HunterCenterLinearMap ((bz.ofZLatticeBasis ℝ) 0)
        (inner_self_ne_zero.mpr ((bz.ofZLatticeBasis ℝ).ne_zero 0))
        ((NumberField.mixedEmbedding.euclidean.toMixed K).symm
          (NumberField.mixedEmbedding K (a : K)))‖ ^ 2 < 35 := by
    change 4 * ‖v15HunterCenterLinearMap ((bz.ofZLatticeBasis ℝ) 0)
      (inner_self_ne_zero.mpr ((bz.ofZLatticeBasis ℝ).ne_zero 0))
      ((NumberField.mixedEmbedding.euclidean.toMixed K).symm
        (NumberField.mixedEmbedding K
          ((v15QuarticHunterAlgebraicIntegerLift K bz x : 𝓞 K) : K)))‖ ^ 2 < 35
    rw [v15_quarticHunterAlgebraicIntegerLift_center K bz x]
    exact hshort
  have hshortCenter :
      4 * ‖v15HunterCenterLinearMap (v15EuclideanOne K) he
        (v15EuclideanEmbedding K (a : K))‖ ^ 2 < 35 := by
    change 4 * ‖v15HunterCenter (v15EuclideanOne K)
      (v15EuclideanEmbedding K (a : K))‖ ^ 2 < 35
    change 4 * ‖v15HunterCenter ((bz.ofZLatticeBasis ℝ) 0)
      ((NumberField.mixedEmbedding.euclidean.toMixed K).symm
        (NumberField.mixedEmbedding K (a : K)))‖ ^ 2 < 35 at hshortBasis
    rw [hbzero'] at hshortBasis
    unfold v15EuclideanEmbedding at ⊢
    exact hshortBasis
  have htraceEq :=
    v15_quartic_center_norm_eq_trace_expression K hreal hdegree (a : K)
  have htraceReal :
      4 * ((Algebra.trace ℚ K ((a : K) ^ 2) : ℚ) : ℝ) -
          ((Algebra.trace ℚ K (a : K) : ℚ) : ℝ) ^ 2 < 35 := by
    rw [← htraceEq]
    exact hshortCenter
  exact_mod_cast htraceReal

open scoped Classical in
/-- Projected-lattice form of the preceding theorem: every nonzero short
vector whose integral lift fails to generate the quartic field lies in a
quadratic subfield of discriminant `5` or `8`. -/
theorem v15_quartic_shortVector_properSubfield_discriminant_eq_five_or_eight
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 4)
    (bz : Basis (Fin 4) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (hbzero :
      (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) =
          v15EuclideanOne K)
    (x : v15QuarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ))
    (hx : x ≠ 0)
    (htop : IntermediateField.adjoin ℚ
      {((v15QuarticHunterAlgebraicIntegerLift K bz x : 𝓞 K) : K)} ≠ ⊤)
    (hshort :
      4 * ‖((x : v15QuarticHunterProjectedLattice
        (bz.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)‖ ^ 2 < 35) :
    let E := IntermediateField.adjoin ℚ
      {((v15QuarticHunterAlgebraicIntegerLift K bz x : 𝓞 K) : K)}
    (NumberField.discr E).natAbs = 5 ∨
      (NumberField.discr E).natAbs = 8 := by
  let a : 𝓞 K := v15QuarticHunterAlgebraicIntegerLift K bz x
  have hnotRat : ¬ ∃ q : ℚ, (a : K) = algebraMap ℚ K q := by
    simpa [a] using
      v15_quarticHunterAlgebraicIntegerLift_not_rat K bz hbzero x hx
  have hbzero' : (bz.ofZLatticeBasis ℝ) 0 = v15EuclideanOne K := by
    rw [show (bz.ofZLatticeBasis ℝ) 0 =
        (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
          NumberField.mixedEmbedding.euclidean.mixedSpace K)) by
      exact bz.ofZLatticeBasis_apply ℝ
        (NumberField.mixedEmbedding.euclidean.integerLattice K) 0]
    exact hbzero
  have he : inner ℝ (v15EuclideanOne K) (v15EuclideanOne K) ≠ 0 := by
    rw [v15_inner_euclideanOne_self_eq_four K hreal hdegree]
    norm_num
  have hshortBasis :
      4 * ‖v15HunterCenterLinearMap ((bz.ofZLatticeBasis ℝ) 0)
        (inner_self_ne_zero.mpr ((bz.ofZLatticeBasis ℝ).ne_zero 0))
        ((NumberField.mixedEmbedding.euclidean.toMixed K).symm
          (NumberField.mixedEmbedding K (a : K)))‖ ^ 2 < 35 := by
    change 4 * ‖v15HunterCenterLinearMap ((bz.ofZLatticeBasis ℝ) 0)
      (inner_self_ne_zero.mpr ((bz.ofZLatticeBasis ℝ).ne_zero 0))
      ((NumberField.mixedEmbedding.euclidean.toMixed K).symm
        (NumberField.mixedEmbedding K
          ((v15QuarticHunterAlgebraicIntegerLift K bz x : 𝓞 K) : K)))‖ ^ 2 < 35
    rw [v15_quarticHunterAlgebraicIntegerLift_center K bz x]
    exact hshort
  have hshortCenter :
      4 * ‖v15HunterCenterLinearMap (v15EuclideanOne K) he
        (v15EuclideanEmbedding K (a : K))‖ ^ 2 < 35 := by
    change 4 * ‖v15HunterCenter (v15EuclideanOne K)
      (v15EuclideanEmbedding K (a : K))‖ ^ 2 < 35
    change 4 * ‖v15HunterCenter ((bz.ofZLatticeBasis ℝ) 0)
      ((NumberField.mixedEmbedding.euclidean.toMixed K).symm
        (NumberField.mixedEmbedding K (a : K)))‖ ^ 2 < 35 at hshortBasis
    rw [hbzero'] at hshortBasis
    unfold v15EuclideanEmbedding at ⊢
    exact hshortBasis
  have htraceEq :=
    v15_quartic_center_norm_eq_trace_expression K hreal hdegree (a : K)
  have htraceReal :
      4 * ((Algebra.trace ℚ K ((a : K) ^ 2) : ℚ) : ℝ) -
          ((Algebra.trace ℚ K (a : K) : ℚ) : ℝ) ^ 2 < 35 := by
    rw [← htraceEq]
    exact hshortCenter
  have htraceRat :
      4 * Algebra.trace ℚ K ((a : K) ^ 2) -
          (Algebra.trace ℚ K (a : K)) ^ 2 < 35 := by
    exact_mod_cast htraceReal
  simpa [a] using
    v15_quartic_adjoin_discriminant_eq_five_or_eight_of_trace_spread_lt
      K hreal hdegree a hnotRat (by simpa [a] using htop) htraceRat

open scoped Classical in
/-- The squared norm of a short vector in a proper quartic subfield is exactly
the discriminant of the quadratic field generated by its lift. -/
theorem v15_quartic_shortVector_inner_self_eq_adjoinDiscriminant
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 4)
    (bz : Basis (Fin 4) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (hbzero :
      (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) =
          v15EuclideanOne K)
    (x : v15QuarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ))
    (hx : x ≠ 0)
    (htop : IntermediateField.adjoin ℚ
      {((v15QuarticHunterAlgebraicIntegerLift K bz x : 𝓞 K) : K)} ≠ ⊤)
    (hshort :
      4 * ‖((x : v15QuarticHunterProjectedLattice
        (bz.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)‖ ^ 2 < 35) :
    let E := IntermediateField.adjoin ℚ
      {((v15QuarticHunterAlgebraicIntegerLift K bz x : 𝓞 K) : K)}
    inner ℝ
        (((x : v15QuarticHunterProjectedLattice
          (bz.ofZLatticeBasis ℝ)) :
          (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ))
        (((x : v15QuarticHunterProjectedLattice
          (bz.ofZLatticeBasis ℝ)) :
          (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)) =
      (NumberField.discr E : ℝ) := by
  let a : 𝓞 K := v15QuarticHunterAlgebraicIntegerLift K bz x
  let E : IntermediateField ℚ K := IntermediateField.adjoin ℚ {(a : K)}
  have hnotRat : ¬ ∃ q : ℚ, (a : K) = algebraMap ℚ K q := by
    simpa [a] using
      v15_quarticHunterAlgebraicIntegerLift_not_rat K bz hbzero x hx
  have hspread :
      4 * Algebra.trace ℚ K ((a : K) ^ 2) -
          (Algebra.trace ℚ K (a : K)) ^ 2 < 35 := by
    simpa [a] using v15_quarticHunterAlgebraicIntegerLift_trace_spread_lt
      K hreal hdegree bz hbzero x hshort
  have htraceDisc :
      4 * Algebra.trace ℚ K ((a : K) ^ 2) -
          (Algebra.trace ℚ K (a : K)) ^ 2 =
        4 * (NumberField.discr E : ℚ) := by
    simpa [E] using
      v15_quartic_adjoin_trace_spread_eq_four_fieldDiscriminant
        K hreal hdegree a hnotRat (by simpa [E, a] using htop) hspread
  have hbzero' : (bz.ofZLatticeBasis ℝ) 0 = v15EuclideanOne K := by
    rw [show (bz.ofZLatticeBasis ℝ) 0 =
        (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
          NumberField.mixedEmbedding.euclidean.mixedSpace K)) by
      exact bz.ofZLatticeBasis_apply ℝ
        (NumberField.mixedEmbedding.euclidean.integerLattice K) 0]
    exact hbzero
  have hcenterEq :
      v15HunterCenter (v15EuclideanOne K)
          (v15EuclideanEmbedding K (a : K)) =
        ((((x : v15QuarticHunterProjectedLattice
          (bz.ofZLatticeBasis ℝ)) :
          (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)) :
            NumberField.mixedEmbedding.euclidean.mixedSpace K) := by
    have h := congrArg Subtype.val
      (v15_quarticHunterAlgebraicIntegerLift_center K bz x)
    change v15HunterCenter ((bz.ofZLatticeBasis ℝ) 0)
        ((NumberField.mixedEmbedding.euclidean.toMixed K).symm
          (NumberField.mixedEmbedding K (a : K))) = _ at h
    calc
      v15HunterCenter (v15EuclideanOne K)
          (v15EuclideanEmbedding K (a : K)) =
          v15HunterCenter ((bz.ofZLatticeBasis ℝ) 0)
            ((NumberField.mixedEmbedding.euclidean.toMixed K).symm
              (NumberField.mixedEmbedding K (a : K))) := by
        rw [hbzero']
        rfl
      _ = _ := h
  have hnormTrace :
      4 * inner ℝ
          (((x : v15QuarticHunterProjectedLattice
            (bz.ofZLatticeBasis ℝ)) :
            (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ))
          (((x : v15QuarticHunterProjectedLattice
            (bz.ofZLatticeBasis ℝ)) :
            (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)) =
        4 * ((Algebra.trace ℚ K ((a : K) ^ 2) : ℚ) : ℝ) -
          ((Algebra.trace ℚ K (a : K) : ℚ) : ℝ) ^ 2 := by
    rw [real_inner_self_eq_norm_sq]
    change 4 * ‖((((x : v15QuarticHunterProjectedLattice
      (bz.ofZLatticeBasis ℝ)) :
      (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)‖ ^ 2 = _
    rw [← hcenterEq]
    exact v15_quartic_center_norm_eq_trace_expression
      K hreal hdegree (a : K)
  have htraceDiscReal :
      4 * ((Algebra.trace ℚ K ((a : K) ^ 2) : ℚ) : ℝ) -
          ((Algebra.trace ℚ K (a : K) : ℚ) : ℝ) ^ 2 =
        4 * (NumberField.discr E : ℝ) := by
    exact_mod_cast htraceDisc
  change inner ℝ
      (((x : v15QuarticHunterProjectedLattice
        (bz.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ))
      (((x : v15QuarticHunterProjectedLattice
        (bz.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)) =
    (NumberField.discr E : ℝ)
  nlinarith [hnormTrace, htraceDiscReal]

open scoped Classical in
/-- Hence the squared norm of such a vector is exactly `5` or `8`. -/
theorem v15_quartic_shortVector_inner_self_eq_five_or_eight
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 4)
    (bz : Basis (Fin 4) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (hbzero :
      (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) =
          v15EuclideanOne K)
    (x : v15QuarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ))
    (hx : x ≠ 0)
    (htop : IntermediateField.adjoin ℚ
      {((v15QuarticHunterAlgebraicIntegerLift K bz x : 𝓞 K) : K)} ≠ ⊤)
    (hshort :
      4 * ‖((x : v15QuarticHunterProjectedLattice
        (bz.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)‖ ^ 2 < 35) :
    inner ℝ
        (((x : v15QuarticHunterProjectedLattice
          (bz.ofZLatticeBasis ℝ)) :
          (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ))
        (((x : v15QuarticHunterProjectedLattice
          (bz.ofZLatticeBasis ℝ)) :
          (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)) = 5 ∨
      inner ℝ
        (((x : v15QuarticHunterProjectedLattice
          (bz.ofZLatticeBasis ℝ)) :
          (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ))
        (((x : v15QuarticHunterProjectedLattice
          (bz.ofZLatticeBasis ℝ)) :
          (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)) = 8 := by
  letI : NumberField.IsTotallyReal K := hreal
  let a : 𝓞 K := v15QuarticHunterAlgebraicIntegerLift K bz x
  let E : IntermediateField ℚ K := IntermediateField.adjoin ℚ {(a : K)}
  have hinner : inner ℝ
      (((x : v15QuarticHunterProjectedLattice
        (bz.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ))
      (((x : v15QuarticHunterProjectedLattice
        (bz.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)) =
      (NumberField.discr E : ℝ) := by
    simpa [E, a] using
      v15_quartic_shortVector_inner_self_eq_adjoinDiscriminant
        K hreal hdegree bz hbzero x hx htop hshort
  have hcases : (NumberField.discr E).natAbs = 5 ∨
      (NumberField.discr E).natAbs = 8 := by
    simpa [E, a] using
      v15_quartic_shortVector_properSubfield_discriminant_eq_five_or_eight
        K hreal hdegree bz hbzero x hx htop hshort
  have hdiscPos : 0 < NumberField.discr E := by
    have hsign : (NumberField.discr E).sign = 1 := by
      rw [NumberField.sign_discr,
        NumberField.IsTotallyReal.nrComplexPlaces_eq_zero]
      norm_num
    exact Int.sign_eq_one_iff_pos.mp hsign
  rcases hcases with hfive | height
  · left
    have hdisc : NumberField.discr E = 5 := by
      have h := congrArg (fun n : ℕ ↦ (n : ℤ)) hfive
      simpa [Int.natCast_natAbs, abs_of_pos hdiscPos] using h
    rw [hinner, hdisc]
    norm_num
  · right
    have hdisc : NumberField.discr E = 8 := by
      have h := congrArg (fun n : ℕ ↦ (n : ℤ)) height
      simpa [Int.natCast_natAbs, abs_of_pos hdiscPos] using h
    rw [hinner, hdisc]
    norm_num

open scoped Classical in
/-- A nonzero short vector whose lift lies in a proper quadratic subfield is
primitive in the centered integral lattice. -/
theorem v15_quartic_shortVector_isPrimitive_of_properSubfield
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 4)
    (bz : Basis (Fin 4) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (hbzero :
      (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) =
          v15EuclideanOne K)
    (x : v15QuarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ))
    (hx : x ≠ 0)
    (htop : IntermediateField.adjoin ℚ
      {((v15QuarticHunterAlgebraicIntegerLift K bz x : 𝓞 K) : K)} ≠ ⊤)
    (hshort :
      4 * ‖((x : v15QuarticHunterProjectedLattice
        (bz.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)‖ ^ 2 < 35) :
    V15IsPrimitiveVector x := by
  let a : 𝓞 K := v15QuarticHunterAlgebraicIntegerLift K bz x
  let E : IntermediateField ℚ K := IntermediateField.adjoin ℚ {(a : K)}
  let aO : 𝓞 E := v15AdjoinRingOfIntegersGenerator K a
  have hnotRat : ¬ ∃ q : ℚ, (a : K) = algebraMap ℚ K q := by
    simpa [a] using
      v15_quarticHunterAlgebraicIntegerLift_not_rat K bz hbzero x hx
  have hbot : E ≠ ⊥ := by
    intro hE
    have haE : (a : K) ∈ E := by
      simpa [E] using IntermediateField.subset_adjoin ℚ {(a : K)}
        (Set.mem_singleton (a : K))
    rw [hE, IntermediateField.mem_bot] at haE
    rcases haE with ⟨q, hq⟩
    exact hnotRat ⟨q, hq.symm⟩
  have hdegreeE : Module.finrank ℚ E = 2 :=
    (v15_quartic_properIntermediateField_finranks K hdegree E hbot
      (by simpa [E, a] using htop)).1
  have hgenE : IntermediateField.adjoin ℚ {(aO : E)} = ⊤ := by
    simpa [E, aO] using v15AdjoinRingOfIntegersGenerator_adjoin_eq_top K a
  have hspread :
      4 * Algebra.trace ℚ K ((a : K) ^ 2) -
          (Algebra.trace ℚ K (a : K)) ^ 2 < 35 := by
    simpa [a] using v15_quarticHunterAlgebraicIntegerLift_trace_spread_lt
      K hreal hdegree bz hbzero x hshort
  have hdisc : Algebra.discr ℤ (v15QuadraticPowerFamily E aO) =
      NumberField.discr E := by
    simpa [E, aO] using
      v15_quartic_adjoin_powerFamily_discr_eq_field_of_trace_spread_lt
        K hreal hdegree a hnotRat (by simpa [E, a] using htop) hspread
  have hprimA : V15IsPrimitiveVector aO :=
    v15_quadratic_generator_isPrimitive_of_discr_eq_field
      E hdegreeE aO hgenE hdisc
  intro n y hny
  by_cases hn : n = 0
  · subst n
    have hzero : x = 0 := by simpa using hny.symm
    exact (hx hzero).elim
  let c : 𝓞 K := v15QuarticHunterAlgebraicIntegerLift K bz y
  have hac : n • c = a := by
    dsimp [c, a]
    rw [← v15QuarticHunterAlgebraicIntegerLift_zsmul, hny]
  have hacK : algebraMap ℚ K (n : ℚ) * (c : K) = (a : K) := by
    have h := congrArg (fun z : 𝓞 K ↦ (z : K)) hac
    simpa [Algebra.smul_def] using h
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hnK : algebraMap ℚ K (n : ℚ) ≠ 0 :=
    by simpa using (algebraMap ℚ K).injective.ne hnQ
  have haMem : (a : K) ∈ E := by
    simpa [E] using IntermediateField.subset_adjoin ℚ {(a : K)}
      (Set.mem_singleton (a : K))
  have hcEq : (c : K) =
      algebraMap ℚ K ((n : ℚ)⁻¹) * (a : K) := by
    rw [map_inv₀]
    exact (eq_inv_mul_iff_mul_eq₀ hnK).mpr hacK
  have hcMem : (c : K) ∈ E := by
    rw [hcEq]
    exact E.mul_mem (E.algebraMap_mem ((n : ℚ)⁻¹)) haMem
  let cE : E := ⟨(c : K), hcMem⟩
  have hcEint : IsIntegral ℤ cE := by
    apply (isIntegral_algHom_iff
      (E.val.restrictScalars ℤ) E.val.injective).mp
    simpa [cE] using c.isIntegral_coe
  let cO : 𝓞 E := ⟨cE, hcEint⟩
  have haMap : algebraMap E K (aO : E) = (a : K) := by
    rfl
  have hacKz : n • (c : K) = (a : K) := by
    have h := congrArg (fun z : 𝓞 K ↦ (z : K)) hac
    simpa only [map_zsmul] using h
  have hacO : n • cO = aO := by
    apply NumberField.RingOfIntegers.coe_injective
    apply E.val.injective
    change algebraMap E K ((n • cO : 𝓞 E) : E) =
      algebraMap E K (aO : E)
    calc
      algebraMap E K ((n • cO : 𝓞 E) : E) =
          algebraMap E K (n • (cO : E)) :=
        congrArg (algebraMap E K)
          (map_zsmul (algebraMap (𝓞 E) E) n cO)
      _ = n • algebraMap E K (cO : E) :=
        map_zsmul (algebraMap E K) n (cO : E)
      _ = n • (c : K) := by rfl
      _ = (a : K) := hacKz
      _ = algebraMap E K (aO : E) := haMap.symm
  exact hprimA n cO hacO

open scoped Classical in
/-- A nonzero short vector lying in a proper quadratic subfield can be chosen
as the first vector of an integral basis of the centered rank-three lattice. -/
theorem v15_exists_quarticProjected_basis_zero_eq_shortVector_of_properSubfield
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 4)
    (bz : Basis (Fin 4) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (hbzero :
      (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) =
          v15EuclideanOne K)
    (x : v15QuarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ))
    (hx : x ≠ 0)
    (htop : IntermediateField.adjoin ℚ
      {((v15QuarticHunterAlgebraicIntegerLift K bz x : 𝓞 K) : K)} ≠ ⊤)
    (hshort :
      4 * ‖((x : v15QuarticHunterProjectedLattice
        (bz.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)‖ ^ 2 < 35) :
    ∃ B : Basis (Fin 3) ℤ
        (v15QuarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ)),
      B 0 = x :=
  v15_exists_fin_three_basis_zero_eq_of_primitive
    ((v15QuarticHunterProjectedBasis
      (bz.ofZLatticeBasis ℝ)).restrictScalars ℤ) x
    (v15_quartic_shortVector_isPrimitive_of_properSubfield
      K hreal hdegree bz hbzero x hx htop hshort)

end

end TraceEuclidean
