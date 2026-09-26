import TraceEuclidean.V15HunterGeneralProjection
import TraceEuclidean.V15HunterGeneralGeometry
import TraceEuclidean.V15HunterNumberFieldProjection
import TraceEuclidean.V15HunterNumberField

/-!
# Number-field Hunter projection in arbitrary positive degree

This module connects the arbitrary-rank centered lattice to the Euclidean
Minkowski lattice of a totally real number field.  It constructs a basis
whose first vector is the embedded algebraic integer `1`, lifts projected
integral vectors back to algebraic integers, and identifies the projected
covolume with the field discriminant.
-/

namespace TraceEuclidean

noncomputable section

open NumberField MeasureTheory Module Submodule
open scoped NumberField

/-- In every positive degree, `1` is a primitive vector of the ring of
integers. -/
theorem v15_ringOfIntegers_one_isPrimitive_general
    (K : Type*) [Field K] [NumberField K] {n : ℕ}
    (hdegree : Module.finrank ℚ K = n + 1) :
    V15IsPrimitiveVector (1 : 𝓞 K) := by
  intro a x hax
  have hnorm : a ^ (n + 1) * Algebra.norm ℤ x = 1 := by
    calc
      a ^ (n + 1) * Algebra.norm ℤ x =
          Algebra.norm ℤ (algebraMap ℤ (𝓞 K) a) * Algebra.norm ℤ x := by
        rw [Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, hdegree]
      _ = Algebra.norm ℤ (algebraMap ℤ (𝓞 K) a * x) := by
        rw [map_mul]
      _ = Algebra.norm ℤ (a • x) := by rw [Algebra.smul_def]
      _ = 1 := by rw [hax, map_one]
  have hpow : IsUnit (a ^ (n + 1)) :=
    isUnit_iff_dvd_one.mpr ⟨Algebra.norm ℤ x, hnorm.symm⟩
  exact (isUnit_pow_iff (Nat.succ_ne_zero n)).mp hpow

/-- A ring of integers of degree `n + 1` has an integral basis whose first
vector is `1`. -/
theorem v15_exists_ringOfIntegers_basis_one_general
    (K : Type*) [Field K] [NumberField K] {n : ℕ}
    (hdegree : Module.finrank ℚ K = n + 1) :
    ∃ bz : Basis (Fin (n + 1)) ℤ (𝓞 K), bz 0 = 1 := by
  let e : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Fin (n + 1) :=
    Fintype.equivOfCardEq (by
      rw [← Module.finrank_eq_card_basis
        (NumberField.RingOfIntegers.basis K)]
      simpa using (NumberField.RingOfIntegers.rank K).trans hdegree)
  let b : Basis (Fin (n + 1)) ℤ (𝓞 K) :=
    (NumberField.RingOfIntegers.basis K).reindex e
  exact v15_exists_fin_succ_basis_zero_eq_of_primitive b 1
    (v15_ringOfIntegers_one_isPrimitive_general K hdegree)

/-- The mixed Minkowski integer lattice has a degree-indexed basis whose
first vector is the embedded algebraic integer `1`. -/
theorem v15_exists_mixedIntegerLattice_basis_one_general
    (K : Type*) [Field K] [NumberField K] {n : ℕ}
    (hdegree : Module.finrank ℚ K = n + 1) :
    ∃ bz : Basis (Fin (n + 1)) ℤ
        (NumberField.mixedEmbedding.integerLattice K),
      (((bz 0 : NumberField.mixedEmbedding.integerLattice K) :
        NumberField.mixedEmbedding.mixedSpace K)) =
          NumberField.mixedEmbedding K 1 := by
  obtain ⟨bO, hbO⟩ :=
    v15_exists_ringOfIntegers_basis_one_general K hdegree
  let bz := bO.map (v15RingOfIntegersEquivMixedIntegerLattice K)
  refine ⟨bz, ?_⟩
  simp [bz, v15RingOfIntegersEquivMixedIntegerLattice, hbO]

open scoped Classical in
/-- The Euclidean Minkowski integer lattice has a degree-indexed basis whose
first vector is the diagonal vector associated with `1`. -/
theorem v15_exists_euclidean_integerLattice_basis_one_general
    (K : Type*) [Field K] [NumberField K] {n : ℕ}
    (hdegree : Module.finrank ℚ K = n + 1) :
    ∃ bz : Basis (Fin (n + 1)) ℤ
        (NumberField.mixedEmbedding.euclidean.integerLattice K),
      (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) =
          v15EuclideanOne K := by
  obtain ⟨bm, hbm⟩ :=
    v15_exists_mixedIntegerLattice_basis_one_general K hdegree
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
/-- In a totally real field, the diagonal vector has squared norm equal to
the field degree. -/
theorem v15_inner_euclideanOne_self_eq_degree
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K) :
    inner ℝ (v15EuclideanOne K) (v15EuclideanOne K) =
      Module.finrank ℚ K := by
  letI : NumberField.IsTotallyReal K := hreal
  unfold v15EuclideanOne
  rw [WithLp.prod_inner_apply]
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp [← NumberField.IsTotallyReal.finrank K]

open scoped Classical in
/-- Lift an arbitrary-rank projected integral vector back to the ring of
integers. -/
noncomputable def v15HunterGeneralAlgebraicIntegerLift
    (K : Type*) [Field K] [NumberField K] {n : ℕ}
    (bz : Basis (Fin (n + 1)) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (x : v15HunterGeneralProjectedLattice (bz.ofZLatticeBasis ℝ)) : 𝓞 K :=
  (v15RingOfIntegersEquivMixedIntegerLattice K).symm
    (v15EuclideanIntegerLatticeToMixed K
      (v15HunterGeneralIntegralLift bz x))

open scoped Classical in
/-- The mixed embedding of the general algebraic-integer lift is the mixed
image of the original Euclidean lattice vector. -/
theorem v15_mixedEmbedding_hunterGeneralAlgebraicIntegerLift
    (K : Type*) [Field K] [NumberField K] {n : ℕ}
    (bz : Basis (Fin (n + 1)) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (x : v15HunterGeneralProjectedLattice (bz.ofZLatticeBasis ℝ)) :
    NumberField.mixedEmbedding K
        ((v15HunterGeneralAlgebraicIntegerLift K bz x : 𝓞 K) : K) =
      NumberField.mixedEmbedding.euclidean.toMixed K
        (((v15HunterGeneralIntegralLift bz x :
            NumberField.mixedEmbedding.euclidean.integerLattice K) :
          NumberField.mixedEmbedding.euclidean.mixedSpace K)) := by
  let y := v15EuclideanIntegerLatticeToMixed K
    (v15HunterGeneralIntegralLift bz x)
  have h := (v15RingOfIntegersEquivMixedIntegerLattice K).apply_symm_apply y
  exact congrArg Subtype.val h

open scoped Classical in
/-- In Euclidean Minkowski coordinates, the general algebraic-integer lift is
the original full-lattice vector. -/
theorem v15_euclideanEmbedding_hunterGeneralAlgebraicIntegerLift
    (K : Type*) [Field K] [NumberField K] {n : ℕ}
    (bz : Basis (Fin (n + 1)) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (x : v15HunterGeneralProjectedLattice (bz.ofZLatticeBasis ℝ)) :
    (NumberField.mixedEmbedding.euclidean.toMixed K).symm
        (NumberField.mixedEmbedding K
          ((v15HunterGeneralAlgebraicIntegerLift K bz x : 𝓞 K) : K)) =
      (((v15HunterGeneralIntegralLift bz x :
          NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) := by
  apply (NumberField.mixedEmbedding.euclidean.toMixed K).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact v15_mixedEmbedding_hunterGeneralAlgebraicIntegerLift K bz x

open scoped Classical in
/-- Orthogonally centering the Euclidean embedding of the general lift
recovers the chosen projected-lattice vector. -/
theorem v15_hunterGeneralAlgebraicIntegerLift_center
    (K : Type*) [Field K] [NumberField K] {n : ℕ}
    (bz : Basis (Fin (n + 1)) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (x : v15HunterGeneralProjectedLattice (bz.ofZLatticeBasis ℝ)) :
    v15HunterCenterLinearMap ((bz.ofZLatticeBasis ℝ) 0)
        (inner_self_ne_zero.mpr ((bz.ofZLatticeBasis ℝ).ne_zero 0))
        ((NumberField.mixedEmbedding.euclidean.toMixed K).symm
          (NumberField.mixedEmbedding K
            ((v15HunterGeneralAlgebraicIntegerLift K bz x : 𝓞 K) : K))) =
      ((x : v15HunterGeneralProjectedLattice (bz.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ) := by
  rw [v15_euclideanEmbedding_hunterGeneralAlgebraicIntegerLift K bz x]
  exact v15HunterGeneralIntegralLift_center bz x

open scoped Classical in
/-- A nonzero projected vector lifts to an algebraic integer outside the
rational subfield. -/
theorem v15_hunterGeneralAlgebraicIntegerLift_not_rat
    (K : Type*) [Field K] [NumberField K] {n : ℕ}
    (bz : Basis (Fin (n + 1)) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (hbzero :
      (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) =
          v15EuclideanOne K)
    (x : v15HunterGeneralProjectedLattice (bz.ofZLatticeBasis ℝ))
    (hx : x ≠ 0) :
    ¬ ∃ q : ℚ,
      ((v15HunterGeneralAlgebraicIntegerLift K bz x : 𝓞 K) : K) =
        algebraMap ℚ K q := by
  rintro ⟨q, hq⟩
  have hcenter := v15_hunterGeneralAlgebraicIntegerLift_center K bz x
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
/-- For a totally real field of degree `n + 1`, the squared projected
covolume times the degree is the absolute field discriminant. -/
theorem v15_hunterGeneralProjected_covolume_sq_mul_degree_eq_discr
    (K : Type*) [Field K] [NumberField K] {n : ℕ}
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = n + 1)
    (bz : Basis (Fin (n + 1)) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (hbzero :
      (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) =
          v15EuclideanOne K) :
    ZLattice.covolume
        (v15HunterGeneralProjectedLattice (bz.ofZLatticeBasis ℝ)) ^ 2 *
        (n + 1 : ℝ) = |NumberField.discr K| := by
  let b := bz.ofZLatticeBasis ℝ
  have hinner : inner ℝ (b 0) (b 0) = (n + 1 : ℝ) := by
    rw [show b 0 =
        (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
          NumberField.mixedEmbedding.euclidean.mixedSpace K)) by
      exact bz.ofZLatticeBasis_apply ℝ
        (NumberField.mixedEmbedding.euclidean.integerLattice K) 0]
    rw [hbzero, v15_inner_euclideanOne_self_eq_degree K hreal, hdegree]
    norm_num
  have hprojection :=
    v15HunterGeneralProjectedLattice_covolume_sq_mul_inner_self b
  rw [hinner] at hprojection
  rw [show span ℤ (Set.range b) =
      NumberField.mixedEmbedding.euclidean.integerLattice K by
    exact bz.ofZLatticeBasis_span ℝ] at hprojection
  rw [v15_totallyReal_euclidean_integerLattice_covolume_eq_sqrt_discr
    K hreal] at hprojection
  rw [Real.sq_sqrt (by positivity :
    (0 : ℝ) ≤ (|NumberField.discr K| : ℝ))] at hprojection
  simpa [b, Int.cast_abs] using hprojection

open scoped Classical in
/-- General Hunter short vector obtained from the exact Minkowski ball
volume.  The hypothesis is squared to avoid introducing roots: after using
`covol(π O_K)^2 (n + 1) = |D_K|`, it is precisely the strict volume
inequality for a radius-`r` ball in dimension `n`. -/
theorem v15_hunterGeneral_projected_shortVector_of_ball
    (K : Type*) [Field K] [NumberField K] {n : ℕ}
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = n + 1)
    (hn : 0 < n)
    (bz : Basis (Fin (n + 1)) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (hbzero :
      (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) =
          v15EuclideanOne K)
    (r : ℝ) (hr : 0 < r)
    (hball :
      ((|NumberField.discr K| : ℤ) : ℝ) *
          (((2 : ℝ) ^ n) ^ 2) <
        (n + 1 : ℝ) *
          (euclideanUnitBallVolume n * r ^ n) ^ 2) :
    ∃ x : v15HunterGeneralProjectedLattice (bz.ofZLatticeBasis ℝ),
      x ≠ 0 ∧
      ‖((x : v15HunterGeneralProjectedLattice
        (bz.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)‖ < r := by
  let b := bz.ofZLatticeBasis ℝ
  let L := v15HunterGeneralProjectedLattice b
  have hfin : finrank ℝ ((ℝ ∙ b 0)ᗮ) = n := by
    simpa using finrank_eq_card_basis (v15HunterGeneralProjectedBasis b)
  letI : Nontrivial ((ℝ ∙ b 0)ᗮ) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hfin]; exact hn)
  have hdegreePos : (0 : ℝ) < n + 1 := by positivity
  have hcovEq :
      ZLattice.covolume L ^ 2 * (n + 1 : ℝ) =
        ((|NumberField.discr K| : ℤ) : ℝ) := by
    simpa [L, b] using
      v15_hunterGeneralProjected_covolume_sq_mul_degree_eq_discr
        K hreal hdegree bz hbzero
  have hsquares :
      (ZLattice.covolume L * (2 : ℝ) ^ n) ^ 2 <
        (euclideanUnitBallVolume n * r ^ n) ^ 2 := by
    exact v15_sq_mul_lt_sq_of_sq_mul_eq hdegreePos hcovEq hball
  have hleftNonneg :
      0 ≤ ZLattice.covolume L * (2 : ℝ) ^ n :=
    mul_nonneg (ZLattice.covolume_pos L).le (by positivity)
  have hrightNonneg :
      0 ≤ euclideanUnitBallVolume n * r ^ n :=
    mul_nonneg (euclideanUnitBallVolume_pos n).le (pow_nonneg hr.le n)
  have hvolume :
      ZLattice.covolume L * (2 : ℝ) ^ n <
        euclideanUnitBallVolume n * r ^ n :=
    (sq_lt_sq₀ hleftNonneg hrightNonneg).mp hsquares
  have hshort := v15_hunterGeneral_shortVector_of_covolume L r hr (by
    simpa [hfin] using hvolume)
  simpa [L, b] using hshort

end

end TraceEuclidean
