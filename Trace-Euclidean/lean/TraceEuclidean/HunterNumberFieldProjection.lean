import TraceEuclidean.HunterProjection
import TraceEuclidean.PrimitiveBasis
import Mathlib.NumberTheory.NumberField.Norm

/-!
# Number-field projection bridge for the cubic Hunter argument

This module connects the coordinate-free projection theorem to the Euclidean
Minkowski lattice of a totally real cubic number field.
-/

namespace TraceEuclidean

noncomputable section

open NumberField MeasureTheory Module Submodule
open scoped NumberField

/-- The ring of integers is linearly equivalent to its image in the mixed
Minkowski integer lattice. -/
noncomputable def ringOfIntegersEquivMixedIntegerLattice
    (K : Type*) [Field K] [NumberField K] :
    (𝓞 K) ≃ₗ[ℤ] NumberField.mixedEmbedding.integerLattice K :=
  LinearEquiv.ofInjective
    (((NumberField.mixedEmbedding K).comp
      (algebraMap (𝓞 K) K)).toIntAlgHom.toLinearMap)
    ((NumberField.mixedEmbedding_injective K).comp
      NumberField.RingOfIntegers.coe_injective)

/-- Send a vector in the Euclidean integer lattice to the corresponding
vector in the mixed Minkowski integer lattice. -/
def euclideanIntegerLatticeToMixed
    (K : Type*) [Field K] [NumberField K]
    (x : NumberField.mixedEmbedding.euclidean.integerLattice K) :
    NumberField.mixedEmbedding.integerLattice K :=
  ⟨NumberField.mixedEmbedding.euclidean.toMixed K
      ((x : NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K), x.property⟩

@[simp]
theorem euclideanIntegerLatticeToMixed_coe
    (K : Type*) [Field K] [NumberField K]
    (x : NumberField.mixedEmbedding.euclidean.integerLattice K) :
    (((euclideanIntegerLatticeToMixed K x :
        NumberField.mixedEmbedding.integerLattice K) :
      NumberField.mixedEmbedding.mixedSpace K)) =
        NumberField.mixedEmbedding.euclidean.toMixed K
          ((x : NumberField.mixedEmbedding.euclidean.integerLattice K) :
            NumberField.mixedEmbedding.euclidean.mixedSpace K) := rfl

@[simp]
theorem euclideanIntegerLatticeToMixed_zsmul
    (K : Type*) [Field K] [NumberField K] (n : ℤ)
    (x : NumberField.mixedEmbedding.euclidean.integerLattice K) :
    euclideanIntegerLatticeToMixed K (n • x) =
      n • euclideanIntegerLatticeToMixed K x := by
  apply Subtype.ext
  simpa [euclideanIntegerLatticeToMixed] using
    map_zsmul (NumberField.mixedEmbedding.euclidean.toMixed K)
      n (((x : NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K))

open scoped Classical in
/-- Lift an integral vector from the Euclidean Minkowski lattice back to the
ring of integers. -/
noncomputable def hunterAlgebraicIntegerLift
    (K : Type*) [Field K] [NumberField K]
    (bz : Basis (Fin 3) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (x : hunterProjectedLattice (bz.ofZLatticeBasis ℝ)) : 𝓞 K :=
  (ringOfIntegersEquivMixedIntegerLattice K).symm
    (euclideanIntegerLatticeToMixed K (hunterIntegralLift bz x))

open scoped Classical in
/-- The mixed embedding of the algebraic-integer lift is the mixed image of
the original Euclidean lattice vector. -/
theorem mixedEmbedding_hunterAlgebraicIntegerLift
    (K : Type*) [Field K] [NumberField K]
    (bz : Basis (Fin 3) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (x : hunterProjectedLattice (bz.ofZLatticeBasis ℝ)) :
    NumberField.mixedEmbedding K
        ((hunterAlgebraicIntegerLift K bz x : 𝓞 K) : K) =
      NumberField.mixedEmbedding.euclidean.toMixed K
        (((hunterIntegralLift bz x :
            NumberField.mixedEmbedding.euclidean.integerLattice K) :
          NumberField.mixedEmbedding.euclidean.mixedSpace K)) := by
  let y := euclideanIntegerLatticeToMixed K
    (hunterIntegralLift bz x)
  have h := (ringOfIntegersEquivMixedIntegerLattice K).apply_symm_apply y
  exact congrArg Subtype.val h

open scoped Classical in
/-- In Euclidean Minkowski coordinates, the algebraic-integer lift is exactly
the original vector in the full integer lattice. -/
theorem euclideanEmbedding_hunterAlgebraicIntegerLift
    (K : Type*) [Field K] [NumberField K]
    (bz : Basis (Fin 3) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (x : hunterProjectedLattice (bz.ofZLatticeBasis ℝ)) :
    (NumberField.mixedEmbedding.euclidean.toMixed K).symm
        (NumberField.mixedEmbedding K
          ((hunterAlgebraicIntegerLift K bz x : 𝓞 K) : K)) =
      (((hunterIntegralLift bz x :
          NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) := by
  apply (NumberField.mixedEmbedding.euclidean.toMixed K).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact mixedEmbedding_hunterAlgebraicIntegerLift K bz x

open scoped Classical in
/-- Orthogonally centering the Euclidean embedding of the algebraic-integer
lift recovers the chosen vector in the projected lattice. -/
theorem hunterAlgebraicIntegerLift_center
    (K : Type*) [Field K] [NumberField K]
    (bz : Basis (Fin 3) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (x : hunterProjectedLattice (bz.ofZLatticeBasis ℝ)) :
    hunterCenterLinearMap ((bz.ofZLatticeBasis ℝ) 0)
        (inner_self_ne_zero.mpr ((bz.ofZLatticeBasis ℝ).ne_zero 0))
        ((NumberField.mixedEmbedding.euclidean.toMixed K).symm
          (NumberField.mixedEmbedding K
            ((hunterAlgebraicIntegerLift K bz x : 𝓞 K) : K))) =
      ((x : hunterProjectedLattice (bz.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ) := by
  rw [euclideanEmbedding_hunterAlgebraicIntegerLift K bz x]
  exact hunterIntegralLift_center bz x

/-- In a cubic number field, `1` is a primitive vector of the ring of
integers.  The norm turns any hypothetical integral divisibility of `1` into
the assertion that the corresponding third power is a unit in `ℤ`. -/
theorem ringOfIntegers_one_isPrimitive
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 3) :
    IsPrimitiveVector (1 : 𝓞 K) := by
  intro a x hax
  have hnorm : a ^ 3 * Algebra.norm ℤ x = 1 := by
    calc
      a ^ 3 * Algebra.norm ℤ x =
          Algebra.norm ℤ (algebraMap ℤ (𝓞 K) a) * Algebra.norm ℤ x := by
        rw [Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, hdegree]
      _ = Algebra.norm ℤ (algebraMap ℤ (𝓞 K) a * x) := by
        rw [map_mul]
      _ = Algebra.norm ℤ (a • x) := by rw [Algebra.smul_def]
      _ = 1 := by rw [hax, map_one]
  have hpow : IsUnit (a ^ 3) :=
    isUnit_iff_dvd_one.mpr ⟨Algebra.norm ℤ x, hnorm.symm⟩
  exact (isUnit_pow_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hpow

/-- A cubic ring of integers has an integral basis whose first vector is
`1`. -/
theorem exists_ringOfIntegers_basis_one
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 3) :
    ∃ bz : Basis (Fin 3) ℤ (𝓞 K), bz 0 = 1 := by
  let e : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Fin 3 :=
    Fintype.equivOfCardEq (by
      rw [← Module.finrank_eq_card_basis
        (NumberField.RingOfIntegers.basis K)]
      exact (NumberField.RingOfIntegers.rank K).trans hdegree)
  let b : Basis (Fin 3) ℤ (𝓞 K) :=
    (NumberField.RingOfIntegers.basis K).reindex e
  exact exists_fin_three_basis_zero_eq_of_primitive b 1
    (ringOfIntegers_one_isPrimitive K hdegree)

/-- The mixed Minkowski integer lattice has a basis whose first vector is the
embedded algebraic integer `1`. -/
theorem exists_mixedIntegerLattice_basis_one
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 3) :
    ∃ bz : Basis (Fin 3) ℤ
        (NumberField.mixedEmbedding.integerLattice K),
      (((bz 0 : NumberField.mixedEmbedding.integerLattice K) :
        NumberField.mixedEmbedding.mixedSpace K)) =
          NumberField.mixedEmbedding K 1 := by
  obtain ⟨bO, hbO⟩ := exists_ringOfIntegers_basis_one K hdegree
  let bz := bO.map (ringOfIntegersEquivMixedIntegerLattice K)
  refine ⟨bz, ?_⟩
  simp [bz, ringOfIntegersEquivMixedIntegerLattice, hbO]

/-- The diagonal vector corresponding to the algebraic integer `1` in the
Euclidean Minkowski model. -/
def euclideanOne (K : Type*) [Field K] [NumberField K] :
    NumberField.mixedEmbedding.euclidean.mixedSpace K :=
  WithLp.toLp 2
    (WithLp.toLp 2 (fun _ ↦ (1 : ℝ)),
      WithLp.toLp 2 (fun _ ↦ (1 : ℂ)))

open scoped Classical in
theorem toMixed_euclideanOne
    (K : Type*) [Field K] [NumberField K] :
    NumberField.mixedEmbedding.euclidean.toMixed K (euclideanOne K) =
      NumberField.mixedEmbedding K 1 := by
  ext <;> simp [euclideanOne, NumberField.mixedEmbedding.euclidean.toMixed]

open scoped Classical in
/-- A rational element embeds as the corresponding real multiple of the
diagonal vector. -/
theorem euclideanEmbedding_algebraMap_rat
    (K : Type*) [Field K] [NumberField K] (q : ℚ) :
    (NumberField.mixedEmbedding.euclidean.toMixed K).symm
        (NumberField.mixedEmbedding K (algebraMap ℚ K q)) =
      (q : ℝ) • euclideanOne K := by
  apply (NumberField.mixedEmbedding.euclidean.toMixed K).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, map_smul]
  rw [toMixed_euclideanOne]
  ext <;> simp

open scoped Classical in
/-- The Euclidean Minkowski integer lattice has a basis whose first vector is
the diagonal vector associated with `1`. -/
theorem exists_euclidean_integerLattice_basis_one
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 3) :
    ∃ bz : Basis (Fin 3) ℤ
        (NumberField.mixedEmbedding.euclidean.integerLattice K),
      (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) =
          euclideanOne K := by
  obtain ⟨bm, hbm⟩ := exists_mixedIntegerLattice_basis_one K hdegree
  let bz := bm.ofZLatticeComap ℝ
    (NumberField.mixedEmbedding.integerLattice K)
    (NumberField.mixedEmbedding.euclidean.toMixed K).toLinearEquiv
  refine ⟨bz, ?_⟩
  change (NumberField.mixedEmbedding.euclidean.toMixed K).symm
      (((bm 0 : NumberField.mixedEmbedding.integerLattice K) :
        NumberField.mixedEmbedding.mixedSpace K)) = euclideanOne K
  apply (NumberField.mixedEmbedding.euclidean.toMixed K).injective
  simp [hbm, toMixed_euclideanOne]

open scoped Classical in
/-- The diagonal vector belongs to the full integer-ring lattice. -/
theorem euclideanOne_mem_integerLattice
    (K : Type*) [Field K] [NumberField K] :
    euclideanOne K ∈
      NumberField.mixedEmbedding.euclidean.integerLattice K := by
  rw [NumberField.mixedEmbedding.euclidean.integerLattice]
  change NumberField.mixedEmbedding.euclidean.toMixed K
      (euclideanOne K) ∈
    NumberField.mixedEmbedding.integerLattice K
  rw [toMixed_euclideanOne]
  exact ⟨1, by simp⟩

open scoped Classical in
/-- In a totally real cubic field, the diagonal vector has squared Euclidean
norm three. -/
theorem inner_euclideanOne_self_eq_three
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 3) :
    inner ℝ (euclideanOne K) (euclideanOne K) = 3 := by
  letI : NumberField.IsTotallyReal K := hreal
  unfold euclideanOne
  rw [WithLp.prod_inner_apply]
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp [← NumberField.IsTotallyReal.finrank K, hdegree]

open scoped Classical in
/-- A nonzero projected vector lifts to an algebraic integer outside the
rational subfield. -/
theorem hunterAlgebraicIntegerLift_not_rat
    (K : Type*) [Field K] [NumberField K]
    (bz : Basis (Fin 3) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (hbzero :
      (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) =
          euclideanOne K)
    (x : hunterProjectedLattice (bz.ofZLatticeBasis ℝ))
    (hx : x ≠ 0) :
    ¬ ∃ q : ℚ,
      ((hunterAlgebraicIntegerLift K bz x : 𝓞 K) : K) =
        algebraMap ℚ K q := by
  rintro ⟨q, hq⟩
  have hcenter := hunterAlgebraicIntegerLift_center K bz x
  rw [hq, euclideanEmbedding_algebraMap_rat K q] at hcenter
  have hbzero' : (bz.ofZLatticeBasis ℝ) 0 = euclideanOne K := by
    rw [show (bz.ofZLatticeBasis ℝ) 0 =
        (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
          NumberField.mixedEmbedding.euclidean.mixedSpace K)) by
      exact bz.ofZLatticeBasis_apply ℝ
        (NumberField.mixedEmbedding.euclidean.integerLattice K) 0]
    exact hbzero
  rw [← hbzero'] at hcenter
  rw [hunterCenterLinearMap_smul_self] at hcenter
  apply hx
  apply Subtype.ext
  simpa using hcenter.symm

open scoped Classical in
/-- In degree three, every nonrational element generates the whole number
field; hence the algebraic-integer lift is a primitive field generator. -/
theorem hunterAlgebraicIntegerLift_adjoin_eq_top
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 3)
    (bz : Basis (Fin 3) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (hbzero :
      (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) =
          euclideanOne K)
    (x : hunterProjectedLattice (bz.ofZLatticeBasis ℝ))
    (hx : x ≠ 0) :
    IntermediateField.adjoin ℚ
        {((hunterAlgebraicIntegerLift K bz x : 𝓞 K) : K)} = ⊤ := by
  let alpha : K := ((hunterAlgebraicIntegerLift K bz x : 𝓞 K) : K)
  change IntermediateField.adjoin ℚ {alpha} = ⊤
  letI : IsSimpleOrder (IntermediateField ℚ K) :=
    IntermediateField.isSimpleOrder_of_finrank_prime ℚ K (by
      rw [hdegree]
      exact Nat.prime_three)
  rcases eq_bot_or_eq_top (IntermediateField.adjoin ℚ {alpha}) with hbot | htop
  · exfalso
    have halpha : alpha ∈ (⊥ : IntermediateField ℚ K) := by
      rw [← hbot]
      exact IntermediateField.mem_adjoin_simple_self ℚ alpha
    obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp halpha
    exact (hunterAlgebraicIntegerLift_not_rat K bz hbzero x hx)
      ⟨q, hq.symm⟩
  · exact htop

open scoped Classical in
/-- Once an integral basis whose first vector is `1` is supplied, the full
number-field covolume and the abstract projection theorem construct the
required short vector in the centered rank-two lattice. -/
theorem cubic_projected_shortVector_of_integralBasis_one
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 3)
    (hdisc : |NumberField.discr K| < 49)
    (bz : Basis (Fin 3) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (hbzero :
      (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) =
          euclideanOne K) :
    let b := bz.ofZLatticeBasis ℝ
    ∃ x : hunterProjectedLattice b, x ≠ 0 ∧
      3 * ‖((x : hunterProjectedLattice b) : (ℝ ∙ b 0)ᗮ)‖ ^ 2 < 16 := by
  let b := bz.ofZLatticeBasis ℝ
  have hinner : inner ℝ (b 0) (b 0) = 3 := by
    rw [show b 0 =
        (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
          NumberField.mixedEmbedding.euclidean.mixedSpace K)) by
      exact bz.ofZLatticeBasis_apply ℝ
        (NumberField.mixedEmbedding.euclidean.integerLattice K) 0]
    rw [hbzero]
    exact inner_euclideanOne_self_eq_three K hreal hdegree
  have hcov : ZLattice.covolume (span ℤ (Set.range b)) < 7 := by
    rw [show span ℤ (Set.range b) =
        NumberField.mixedEmbedding.euclidean.integerLattice K by
      exact bz.ofZLatticeBasis_span ℝ]
    rw [totallyReal_euclidean_integerLattice_covolume_eq_sqrt_discr K hreal]
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 7)]
    exact_mod_cast hdisc
  exact hunterProjectedLattice_shortVector b hinner hcov

open scoped Classical in
/-- The cubic Hunter short vector with the required integral basis constructed
internally.  No basis choice remains as an input to the theorem. -/
theorem cubic_projected_shortVector
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 3)
    (hdisc : |NumberField.discr K| < 49) :
    ∃ bz : Basis (Fin 3) ℤ
        (NumberField.mixedEmbedding.euclidean.integerLattice K),
      (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
          NumberField.mixedEmbedding.euclidean.mixedSpace K)) =
            euclideanOne K ∧
      ∃ x : hunterProjectedLattice (bz.ofZLatticeBasis ℝ),
        x ≠ 0 ∧
        3 * ‖((x : hunterProjectedLattice (bz.ofZLatticeBasis ℝ)) :
          (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)‖ ^ 2 < 16 := by
  obtain ⟨bz, hbz⟩ :=
    exists_euclidean_integerLattice_basis_one K hdegree
  refine ⟨bz, hbz, ?_⟩
  exact cubic_projected_shortVector_of_integralBasis_one
    K hreal hdegree hdisc bz hbz

open scoped Classical in
/-- The geometric construction supplies a primitive integral generator whose
centered Euclidean embedding satisfies the cubic Hunter bound. -/
theorem cubic_hunter_generator
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 3)
    (hdisc : |NumberField.discr K| < 49) :
    ∃ bz : Basis (Fin 3) ℤ
        (NumberField.mixedEmbedding.euclidean.integerLattice K),
      (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
          NumberField.mixedEmbedding.euclidean.mixedSpace K)) =
            euclideanOne K ∧
      ∃ x : hunterProjectedLattice (bz.ofZLatticeBasis ℝ),
        x ≠ 0 ∧
        IntermediateField.adjoin ℚ
          {((hunterAlgebraicIntegerLift K bz x : 𝓞 K) : K)} = ⊤ ∧
        3 * ‖hunterCenterLinearMap ((bz.ofZLatticeBasis ℝ) 0)
          (inner_self_ne_zero.mpr ((bz.ofZLatticeBasis ℝ).ne_zero 0))
          ((NumberField.mixedEmbedding.euclidean.toMixed K).symm
            (NumberField.mixedEmbedding K
              ((hunterAlgebraicIntegerLift K bz x : 𝓞 K) : K)))‖ ^ 2 < 16 := by
  obtain ⟨bz, hbzero, x, hx, hshort⟩ :=
    cubic_projected_shortVector K hreal hdegree hdisc
  refine ⟨bz, hbzero, x, hx,
    hunterAlgebraicIntegerLift_adjoin_eq_top
      K hdegree bz hbzero x hx, ?_⟩
  rw [hunterAlgebraicIntegerLift_center K bz x]
  exact hshort

end

end TraceEuclidean
