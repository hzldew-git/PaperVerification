import TraceEuclidean.V15QuarticHunterProjection
import TraceEuclidean.V15HunterNumberFieldProjection

/-!
# Number-field projection bridge for the quartic Hunter argument

This module specializes the quartic projection theorem to the Euclidean
Minkowski lattice of a totally real quartic number field. The sharp
three-dimensional Hermite bound is kept as the explicit input
`V15HermiteThreeInput`; all integral-basis, lift, and covolume steps are
proved here.
-/

namespace TraceEuclidean

noncomputable section

open NumberField MeasureTheory Module Submodule
open scoped NumberField

universe u

open scoped Classical in
/-- Lift an integral vector from the quartic projected lattice back to the
ring of integers. -/
noncomputable def v15QuarticHunterAlgebraicIntegerLift
    (K : Type*) [Field K] [NumberField K]
    (bz : Basis (Fin 4) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (x : v15QuarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ)) : 𝓞 K :=
  (v15RingOfIntegersEquivMixedIntegerLattice K).symm
    (v15EuclideanIntegerLatticeToMixed K
      (v15QuarticHunterIntegralLift bz x))

open scoped Classical in
@[simp]
theorem v15QuarticHunterAlgebraicIntegerLift_zsmul
    (K : Type*) [Field K] [NumberField K]
    (bz : Basis (Fin 4) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (n : ℤ)
    (x : v15QuarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ)) :
    v15QuarticHunterAlgebraicIntegerLift K bz (n • x) =
      n • v15QuarticHunterAlgebraicIntegerLift K bz x := by
  simp [v15QuarticHunterAlgebraicIntegerLift]

open scoped Classical in
/-- The mixed embedding of the quartic algebraic-integer lift is the mixed
image of the original Euclidean lattice vector. -/
theorem v15_mixedEmbedding_quarticHunterAlgebraicIntegerLift
    (K : Type*) [Field K] [NumberField K]
    (bz : Basis (Fin 4) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (x : v15QuarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ)) :
    NumberField.mixedEmbedding K
        ((v15QuarticHunterAlgebraicIntegerLift K bz x : 𝓞 K) : K) =
      NumberField.mixedEmbedding.euclidean.toMixed K
        (((v15QuarticHunterIntegralLift bz x :
            NumberField.mixedEmbedding.euclidean.integerLattice K) :
          NumberField.mixedEmbedding.euclidean.mixedSpace K)) := by
  let y := v15EuclideanIntegerLatticeToMixed K
    (v15QuarticHunterIntegralLift bz x)
  have h := (v15RingOfIntegersEquivMixedIntegerLattice K).apply_symm_apply y
  exact congrArg Subtype.val h

open scoped Classical in
/-- In Euclidean Minkowski coordinates, the quartic algebraic-integer lift
is exactly the original vector in the full integer lattice. -/
theorem v15_euclideanEmbedding_quarticHunterAlgebraicIntegerLift
    (K : Type*) [Field K] [NumberField K]
    (bz : Basis (Fin 4) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (x : v15QuarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ)) :
    (NumberField.mixedEmbedding.euclidean.toMixed K).symm
        (NumberField.mixedEmbedding K
          ((v15QuarticHunterAlgebraicIntegerLift K bz x : 𝓞 K) : K)) =
      (((v15QuarticHunterIntegralLift bz x :
          NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) := by
  apply (NumberField.mixedEmbedding.euclidean.toMixed K).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact v15_mixedEmbedding_quarticHunterAlgebraicIntegerLift K bz x

open scoped Classical in
/-- Centering the Euclidean embedding of the quartic algebraic-integer lift
recovers the chosen vector in the projected lattice. -/
theorem v15_quarticHunterAlgebraicIntegerLift_center
    (K : Type*) [Field K] [NumberField K]
    (bz : Basis (Fin 4) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (x : v15QuarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ)) :
    v15HunterCenterLinearMap ((bz.ofZLatticeBasis ℝ) 0)
        (inner_self_ne_zero.mpr ((bz.ofZLatticeBasis ℝ).ne_zero 0))
        ((NumberField.mixedEmbedding.euclidean.toMixed K).symm
          (NumberField.mixedEmbedding K
            ((v15QuarticHunterAlgebraicIntegerLift K bz x : 𝓞 K) : K))) =
      ((x : v15QuarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ) := by
  rw [v15_euclideanEmbedding_quarticHunterAlgebraicIntegerLift K bz x]
  exact v15QuarticHunterIntegralLift_center bz x

/-- In a quartic number field, `1` is a primitive vector of the ring of
integers. -/
theorem v15_ringOfIntegers_one_isPrimitive_dim_four
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4) :
    V15IsPrimitiveVector (1 : 𝓞 K) := by
  intro a x hax
  have hnorm : a ^ 4 * Algebra.norm ℤ x = 1 := by
    calc
      a ^ 4 * Algebra.norm ℤ x =
          Algebra.norm ℤ (algebraMap ℤ (𝓞 K) a) * Algebra.norm ℤ x := by
        rw [Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, hdegree]
      _ = Algebra.norm ℤ (algebraMap ℤ (𝓞 K) a * x) := by
        rw [map_mul]
      _ = Algebra.norm ℤ (a • x) := by rw [Algebra.smul_def]
      _ = 1 := by rw [hax, map_one]
  have hpow : IsUnit (a ^ 4) :=
    isUnit_iff_dvd_one.mpr ⟨Algebra.norm ℤ x, hnorm.symm⟩
  exact (isUnit_pow_iff (by norm_num : (4 : ℕ) ≠ 0)).mp hpow

/-- A quartic ring of integers has an integral basis whose first vector is
`1`. -/
theorem v15_exists_ringOfIntegers_basis_one_dim_four
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4) :
    ∃ bz : Basis (Fin 4) ℤ (𝓞 K), bz 0 = 1 := by
  let e : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Fin 4 :=
    Fintype.equivOfCardEq (by
      rw [← Module.finrank_eq_card_basis
        (NumberField.RingOfIntegers.basis K)]
      exact (NumberField.RingOfIntegers.rank K).trans hdegree)
  let b : Basis (Fin 4) ℤ (𝓞 K) :=
    (NumberField.RingOfIntegers.basis K).reindex e
  exact v15_exists_fin_four_basis_zero_eq_of_primitive b 1
    (v15_ringOfIntegers_one_isPrimitive_dim_four K hdegree)

/-- The mixed Minkowski integer lattice of a quartic field has a basis whose
first vector is the embedded algebraic integer `1`. -/
theorem v15_exists_mixedIntegerLattice_basis_one_dim_four
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4) :
    ∃ bz : Basis (Fin 4) ℤ
        (NumberField.mixedEmbedding.integerLattice K),
      (((bz 0 : NumberField.mixedEmbedding.integerLattice K) :
        NumberField.mixedEmbedding.mixedSpace K)) =
          NumberField.mixedEmbedding K 1 := by
  obtain ⟨bO, hbO⟩ :=
    v15_exists_ringOfIntegers_basis_one_dim_four K hdegree
  let bz := bO.map (v15RingOfIntegersEquivMixedIntegerLattice K)
  refine ⟨bz, ?_⟩
  simp [bz, v15RingOfIntegersEquivMixedIntegerLattice, hbO]

open scoped Classical in
/-- The Euclidean Minkowski integer lattice of a quartic field has a basis
whose first vector is the diagonal vector associated with `1`. -/
theorem v15_exists_euclidean_integerLattice_basis_one_dim_four
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4) :
    ∃ bz : Basis (Fin 4) ℤ
        (NumberField.mixedEmbedding.euclidean.integerLattice K),
      (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) =
          v15EuclideanOne K := by
  obtain ⟨bm, hbm⟩ :=
    v15_exists_mixedIntegerLattice_basis_one_dim_four K hdegree
  let bz := bm.ofZLatticeComap ℝ
    (NumberField.mixedEmbedding.integerLattice K)
    (NumberField.mixedEmbedding.euclidean.toMixed K).toLinearEquiv
  refine ⟨bz, ?_⟩
  change (NumberField.mixedEmbedding.euclidean.toMixed K).symm
      (((bm 0 : NumberField.mixedEmbedding.integerLattice K) :
        NumberField.mixedEmbedding.mixedSpace K)) = v15EuclideanOne K
  apply (NumberField.mixedEmbedding.euclidean.toMixed K).injective
  simp [hbm, v15_toMixed_euclideanOne]

open scoped Classical in
/-- In a totally real quartic field, the diagonal vector has squared
Euclidean norm four. -/
theorem v15_inner_euclideanOne_self_eq_four_projection
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 4) :
    inner ℝ (v15EuclideanOne K) (v15EuclideanOne K) = 4 := by
  letI : NumberField.IsTotallyReal K := hreal
  unfold v15EuclideanOne
  rw [WithLp.prod_inner_apply]
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp [← NumberField.IsTotallyReal.finrank K, hdegree]

open scoped Classical in
/-- A nonzero quartic projected vector lifts to an algebraic integer outside
the rational subfield. -/
theorem v15_quarticHunterAlgebraicIntegerLift_not_rat
    (K : Type*) [Field K] [NumberField K]
    (bz : Basis (Fin 4) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (hbzero :
      (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) =
          v15EuclideanOne K)
    (x : v15QuarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ))
    (hx : x ≠ 0) :
    ¬ ∃ q : ℚ,
      ((v15QuarticHunterAlgebraicIntegerLift K bz x : 𝓞 K) : K) =
        algebraMap ℚ K q := by
  rintro ⟨q, hq⟩
  have hcenter := v15_quarticHunterAlgebraicIntegerLift_center K bz x
  rw [hq, v15_euclideanEmbedding_algebraMap_rat K q] at hcenter
  have hbzero' : (bz.ofZLatticeBasis ℝ) 0 = v15EuclideanOne K := by
    rw [show (bz.ofZLatticeBasis ℝ) 0 =
        (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
          NumberField.mixedEmbedding.euclidean.mixedSpace K)) by
      exact bz.ofZLatticeBasis_apply ℝ
        (NumberField.mixedEmbedding.euclidean.integerLattice K) 0]
    exact hbzero
  rw [← hbzero'] at hcenter
  rw [v15HunterCenterLinearMap_smul_self] at hcenter
  apply hx
  apply Subtype.ext
  simpa using hcenter.symm

open scoped Classical in
/-- Conditional quartic Hunter short vector: all steps except the sharp
three-dimensional Hermite theorem are discharged internally. -/
theorem v15_quartic_projected_shortVector_of_integralBasis_one
    (hHermite : V15HermiteThreeInput.{u})
    (K : Type u) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 4)
    (hdisc : |NumberField.discr K| < 725)
    (bz : Basis (Fin 4) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (hbzero :
      (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) =
          v15EuclideanOne K) :
    let b := bz.ofZLatticeBasis ℝ
    ∃ x : v15QuarticHunterProjectedLattice b, x ≠ 0 ∧
      4 * ‖((x : v15QuarticHunterProjectedLattice b) : (ℝ ∙ b 0)ᗮ)‖ ^ 2 < 29 := by
  let b := bz.ofZLatticeBasis ℝ
  have hinner : inner ℝ (b 0) (b 0) = 4 := by
    rw [show b 0 =
        (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
          NumberField.mixedEmbedding.euclidean.mixedSpace K)) by
      exact bz.ofZLatticeBasis_apply ℝ
        (NumberField.mixedEmbedding.euclidean.integerLattice K) 0]
    rw [hbzero]
    exact v15_inner_euclideanOne_self_eq_four_projection K hreal hdegree
  have hcov : ZLattice.covolume (span ℤ (Set.range b)) ^ 2 < 725 := by
    rw [show span ℤ (Set.range b) =
        NumberField.mixedEmbedding.euclidean.integerLattice K by
      exact bz.ofZLatticeBasis_span ℝ]
    rw [v15_totallyReal_euclidean_integerLattice_covolume_eq_sqrt_discr
      K hreal]
    rw [Real.sq_sqrt (by positivity :
      (0 : ℝ) ≤ (|NumberField.discr K| : ℝ))]
    exact_mod_cast hdisc
  exact v15QuarticHunterProjectedLattice_shortVector
    hHermite b hinner hcov

open scoped Classical in
/-- The conditional quartic Hunter short vector with the required integral
basis constructed internally. -/
theorem v15_quartic_projected_shortVector
    (hHermite : V15HermiteThreeInput.{u})
    (K : Type u) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 4)
    (hdisc : |NumberField.discr K| < 725) :
    ∃ bz : Basis (Fin 4) ℤ
        (NumberField.mixedEmbedding.euclidean.integerLattice K),
      (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) =
          v15EuclideanOne K ∧
      ∃ x : v15QuarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ),
        x ≠ 0 ∧
        4 * ‖((x : v15QuarticHunterProjectedLattice
          (bz.ofZLatticeBasis ℝ)) :
          (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)‖ ^ 2 < 29 := by
  obtain ⟨bz, hbz⟩ :=
    v15_exists_euclidean_integerLattice_basis_one_dim_four K hdegree
  refine ⟨bz, hbz, ?_⟩
  exact v15_quartic_projected_shortVector_of_integralBasis_one
    hHermite K hreal hdegree hdisc bz hbz

open scoped Classical in
/-- Unconditional quartic Hunter short vector from the three-dimensional
Minkowski ball.  Its bound `35` feeds the enlarged finite discriminant
search. -/
theorem v15_quartic_projected_shortVector_of_integralBasis_one_minkowski
    (K : Type u) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 4)
    (hdisc : |NumberField.discr K| < 725)
    (bz : Basis (Fin 4) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (hbzero :
      (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) =
          v15EuclideanOne K) :
    let b := bz.ofZLatticeBasis ℝ
    ∃ x : v15QuarticHunterProjectedLattice b, x ≠ 0 ∧
      4 * ‖((x : v15QuarticHunterProjectedLattice b) :
        (ℝ ∙ b 0)ᗮ)‖ ^ 2 < 35 := by
  let b := bz.ofZLatticeBasis ℝ
  have hinner : inner ℝ (b 0) (b 0) = 4 := by
    rw [show b 0 =
        (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
          NumberField.mixedEmbedding.euclidean.mixedSpace K)) by
      exact bz.ofZLatticeBasis_apply ℝ
        (NumberField.mixedEmbedding.euclidean.integerLattice K) 0]
    rw [hbzero]
    exact v15_inner_euclideanOne_self_eq_four_projection K hreal hdegree
  have hcov : ZLattice.covolume (span ℤ (Set.range b)) ^ 2 < 725 := by
    rw [show span ℤ (Set.range b) =
        NumberField.mixedEmbedding.euclidean.integerLattice K by
      exact bz.ofZLatticeBasis_span ℝ]
    rw [v15_totallyReal_euclidean_integerLattice_covolume_eq_sqrt_discr
      K hreal]
    rw [Real.sq_sqrt (by positivity :
      (0 : ℝ) ≤ (|NumberField.discr K| : ℝ))]
    exact_mod_cast hdisc
  exact v15QuarticHunterProjectedLattice_shortVector_minkowski
    b hinner hcov

open scoped Classical in
/-- The unconditional Minkowski short vector with the required integral
basis constructed internally. -/
theorem v15_quartic_projected_shortVector_minkowski
    (K : Type u) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 4)
    (hdisc : |NumberField.discr K| < 725) :
    ∃ bz : Basis (Fin 4) ℤ
        (NumberField.mixedEmbedding.euclidean.integerLattice K),
      (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) =
          v15EuclideanOne K ∧
      ∃ x : v15QuarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ),
        x ≠ 0 ∧
        4 * ‖((x : v15QuarticHunterProjectedLattice
          (bz.ofZLatticeBasis ℝ)) :
          (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)‖ ^ 2 < 35 := by
  obtain ⟨bz, hbz⟩ :=
    v15_exists_euclidean_integerLattice_basis_one_dim_four K hdegree
  refine ⟨bz, hbz, ?_⟩
  exact v15_quartic_projected_shortVector_of_integralBasis_one_minkowski
    K hreal hdegree hdisc bz hbz

end

end TraceEuclidean
