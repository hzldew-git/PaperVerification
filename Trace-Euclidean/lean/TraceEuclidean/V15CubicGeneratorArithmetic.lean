import TraceEuclidean.V15CubicPowerBasis

/-!
# Arithmetic certificate of a primitive cubic generator

For a primitive algebraic integer in a cubic number field, this module
extracts the three integral coefficients of its minimal polynomial.  It
proves the absence of integral roots and the exact relation

`disc(f) = index^2 * disc(K)`

with a strictly positive natural-number index.  The index is constructed as
the absolute determinant of the power family in an integral basis.
-/

namespace TraceEuclidean

noncomputable section

open NumberField Module Polynomial
open scoped Matrix NumberField

/-- The trace coefficient of the integral minimal polynomial. -/
def v15CubicS1
    (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) : ℤ :=
  -(minpoly ℤ (a : K)).coeff 2

/-- The linear coefficient of the integral minimal polynomial. -/
def v15CubicS2
    (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) : ℤ :=
  (minpoly ℤ (a : K)).coeff 1

/-- The negative constant coefficient of the integral minimal polynomial. -/
def v15CubicS3
    (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) : ℤ :=
  -(minpoly ℤ (a : K)).coeff 0

/-- The integral power family `1, a, a^2`. -/
def v15CubicPowerFamily
    (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) :
    Fin 3 → 𝓞 K :=
  ![1, a, a ^ 2]

/-- A primitive integral generator of a cubic field has a degree-three
integral minimal polynomial. -/
theorem v15_cubic_minpoly_natDegree
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 3)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    (minpoly ℤ (a : K)).natDegree = 3 := by
  have h := hgen
  rw [Field.primitive_element_iff_minpoly_natDegree_eq,
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ a.isIntegral_coe,
    (minpoly.monic a.isIntegral_coe).natDegree_map] at h
  exact h.trans hdegree

/-- The cubic assembled from `v15CubicS1`, `v15CubicS2`, and
`v15CubicS3` is the integral minimal polynomial. -/
theorem v15_cubicEval_eq_minpoly_eval
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 3)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤)
    (z : ℤ) :
    v15CubicEval (v15CubicS1 K a) (v15CubicS2 K a)
        (v15CubicS3 K a) z =
      (minpoly ℤ (a : K)).eval z := by
  have hdeg := v15_cubic_minpoly_natDegree K hdegree a hgen
  rw [Polynomial.eval_eq_sum_range' (n := 4)
    (by omega : (minpoly ℤ (a : K)).natDegree < 4)]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ]
  have hlead : (minpoly ℤ (a : K)).coeff 3 = 1 := by
    rw [← hdeg]
    exact (minpoly.monic a.isIntegral_coe).coeff_natDegree
  simp only [Finset.sum_range_zero, zero_add, pow_zero, mul_one, pow_one]
  rw [hlead]
  simp [v15CubicEval, v15CubicS1, v15CubicS2, v15CubicS3]
  ring

/-- The integral minimal polynomial of a primitive cubic generator has no
integral root. -/
theorem v15_cubic_minpoly_no_integer_root
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 3)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    ∀ z : ℤ, v15CubicEval (v15CubicS1 K a) (v15CubicS2 K a)
      (v15CubicS3 K a) z ≠ 0 := by
  intro z hz
  have hdeg := v15_cubic_minpoly_natDegree K hdegree a hgen
  apply (minpoly.irreducible a.isIntegral_coe).not_isRoot_of_natDegree_ne_one
    (by omega : (minpoly ℤ (a : K)).natDegree ≠ 1)
  rw [Polynomial.IsRoot]
  rw [← v15_cubicEval_eq_minpoly_eval K hdegree a hgen z]
  exact hz

/-- The polynomial discriminant is the explicit cubic coefficient formula. -/
theorem v15_cubic_minpoly_discr
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 3)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    Polynomial.discr (minpoly ℤ (a : K)) =
      v15CubicDiscriminant (v15CubicS1 K a) (v15CubicS2 K a)
        (v15CubicS3 K a) := by
  have hdeg := v15_cubic_minpoly_natDegree K hdegree a hgen
  have hdegreePoly : (minpoly ℤ (a : K)).degree = 3 := by
    rw [degree_eq_natDegree (minpoly.ne_zero a.isIntegral_coe), hdeg]
    norm_num
  rw [Polynomial.discr_of_degree_eq_three hdegreePoly]
  have hlead : (minpoly ℤ (a : K)).coeff 3 = 1 := by
    rw [← hdeg]
    exact (minpoly.monic a.isIntegral_coe).coeff_natDegree
  rw [hlead]
  simp only [v15CubicS1, v15CubicS2, v15CubicS3,
    v15CubicDiscriminant]
  ring

/-- Discriminants of integral families commute with localization from the
ring of integers to the number field. -/
theorem v15_discr_ringOfIntegers_cast
    (K : Type*) [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → 𝓞 K) :
    ((Algebra.discr ℤ v : ℤ) : ℚ) =
      Algebra.discr ℚ (fun i ↦ ((v i : 𝓞 K) : K)) := by
  rw [Algebra.discr_def, Algebra.discr_def]
  change algebraMap ℤ ℚ (Algebra.traceMatrix ℤ v).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  exact (Algebra.trace_localization (R := ℤ) (Rₘ := ℚ)
    (S := 𝓞 K) (Sₘ := K) (nonZeroDivisors ℤ) (v i * v j)).symm

/-- After localization, the integral power family is the rational power
basis generated by `a`. -/
theorem v15_cubicPowerFamily_discr_eq_powerBasis
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 3)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    Algebra.discr ℚ
        (fun i ↦ ((v15CubicPowerFamily K a i : 𝓞 K) : K)) =
      Algebra.discr ℚ
        (PowerBasis.ofAdjoinEqTop (IsIntegral.of_finite ℚ (a : K))
          (Algebra.adjoin_eq_top_of_primitive_element
            (IsIntegral.of_finite ℚ (a : K)).isAlgebraic hgen)).basis := by
  classical
  let hint : IsIntegral ℚ (a : K) := IsIntegral.of_finite ℚ (a : K)
  let hsub : Algebra.adjoin ℚ {(a : K)} = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element hint.isAlgebraic hgen
  let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop hint hsub
  have hdim : pb.dim = 3 := by
    rw [PowerBasis.ofAdjoinEqTop_dim]
    have h := hgen
    rw [Field.primitive_element_iff_minpoly_natDegree_eq] at h
    exact h.trans hdegree
  let e : Fin pb.dim ≃ Fin 3 := finCongr hdim
  change Algebra.discr ℚ
      (fun i ↦ ((v15CubicPowerFamily K a i : 𝓞 K) : K)) =
    Algebra.discr ℚ pb.basis
  rw [← Algebra.discr_reindex ℚ pb.basis e]
  congr 1
  ext i
  change ((v15CubicPowerFamily K a i : 𝓞 K) : K) =
    pb.basis (e.symm i)
  rw [pb.basis_eq_pow]
  have he : ((e.symm i : Fin pb.dim) : ℕ) = (i : ℕ) := rfl
  rw [he]
  fin_cases i <;> simp [v15CubicPowerFamily, pb]

/-- The discriminant of the integral power family equals the explicit cubic
discriminant. -/
theorem v15_cubicPowerFamily_discr_eq_cubicDiscriminant
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 3)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    Algebra.discr ℤ (v15CubicPowerFamily K a) =
      v15CubicDiscriminant (v15CubicS1 K a) (v15CubicS2 K a)
        (v15CubicS3 K a) := by
  classical
  apply Rat.intCast_injective
  rw [v15_discr_ringOfIntegers_cast]
  let hint : IsIntegral ℚ (a : K) := IsIntegral.of_finite ℚ (a : K)
  let hsub : Algebra.adjoin ℚ {(a : K)} = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element hint.isAlgebraic hgen
  let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop hint hsub
  have hpb : Algebra.discr ℚ
      (fun i ↦ ((v15CubicPowerFamily K a i : 𝓞 K) : K)) =
        Algebra.discr ℚ pb.basis := by
    exact v15_cubicPowerFamily_discr_eq_powerBasis K hdegree a hgen
  rw [hpb]
  have hdim : pb.dim = 3 := by
    rw [PowerBasis.ofAdjoinEqTop_dim]
    have h := hgen
    rw [Field.primitive_element_iff_minpoly_natDegree_eq] at h
    exact h.trans hdegree
  rw [v15_powerBasis_discr_dim_three pb hdim]
  have hmin : pb.minpolyGen =
      (minpoly ℤ (a : K)).map (algebraMap ℤ ℚ) := by
    rw [pb.minpolyGen_eq]
    exact minpoly.isIntegrallyClosed_eq_field_fractions' ℚ a.isIntegral_coe
  rw [hmin]
  simp only [Polynomial.coeff_map]
  simp [v15CubicS1, v15CubicS2, v15CubicS3,
    v15CubicDiscriminant]
  ring

/-- The determinant of the integral power family in any integral basis gives
the square factor between polynomial and field discriminants. -/
theorem v15_cubicDiscriminant_eq_det_sq_mul_fieldDiscriminant
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 3)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤)
    (bO : Basis (Fin 3) ℤ (𝓞 K)) :
    v15CubicDiscriminant (v15CubicS1 K a) (v15CubicS2 K a)
        (v15CubicS3 K a) =
      (bO.toMatrix (v15CubicPowerFamily K a)).det ^ 2 *
        NumberField.discr K := by
  classical
  rw [← v15_cubicPowerFamily_discr_eq_cubicDiscriminant
    K hdegree a hgen]
  let P := bO.toMatrix (v15CubicPowerFamily K a)
  change Algebra.discr ℤ (v15CubicPowerFamily K a) =
    P.det ^ 2 * NumberField.discr K
  calc
    Algebra.discr ℤ (v15CubicPowerFamily K a) =
        Algebra.discr ℤ
          (bO ᵥ* P.map (algebraMap ℤ (𝓞 K))) := by
      rw [bO.toMatrix_map_vecMul (v15CubicPowerFamily K a)]
    _ = P.det ^ 2 * Algebra.discr ℤ bO :=
      Algebra.discr_of_matrix_vecMul bO P
    _ = P.det ^ 2 * NumberField.discr K := by
      rw [NumberField.discr_eq_discr K bO]

/-- The primitive power family has nonzero integral discriminant. -/
theorem v15_cubicPowerFamily_discr_ne_zero
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 3)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    Algebra.discr ℤ (v15CubicPowerFamily K a) ≠ 0 := by
  classical
  intro hzero
  have hcast := congrArg (fun z : ℤ ↦ (z : ℚ)) hzero
  rw [v15_discr_ringOfIntegers_cast] at hcast
  simp only [Int.cast_zero] at hcast
  rw [v15_cubicPowerFamily_discr_eq_powerBasis K hdegree a hgen] at hcast
  exact (Algebra.discr_not_zero_of_basis ℚ
    (PowerBasis.ofAdjoinEqTop (IsIntegral.of_finite ℚ (a : K))
      (Algebra.adjoin_eq_top_of_primitive_element
        (IsIntegral.of_finite ℚ (a : K)).isAlgebraic hgen)).basis) hcast

/-- A primitive cubic algebraic integer determines a strictly positive
natural index with the exact discriminant relation required by the finite
cubic reduction. -/
theorem v15_cubic_exists_positive_index
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 3)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤)
    (bO : Basis (Fin 3) ℤ (𝓞 K)) :
    ∃ index : ℕ, 0 < index ∧
      v15CubicDiscriminant (v15CubicS1 K a) (v15CubicS2 K a)
          (v15CubicS3 K a) =
        (index : ℤ) ^ 2 * NumberField.discr K := by
  classical
  let P := bO.toMatrix (v15CubicPowerFamily K a)
  have hfamily : Algebra.discr ℤ (v15CubicPowerFamily K a) =
      P.det ^ 2 * NumberField.discr K := by
    calc
      Algebra.discr ℤ (v15CubicPowerFamily K a) =
          Algebra.discr ℤ
            (bO ᵥ* P.map (algebraMap ℤ (𝓞 K))) := by
        rw [bO.toMatrix_map_vecMul (v15CubicPowerFamily K a)]
      _ = P.det ^ 2 * Algebra.discr ℤ bO :=
        Algebra.discr_of_matrix_vecMul bO P
      _ = P.det ^ 2 * NumberField.discr K := by
        rw [NumberField.discr_eq_discr K bO]
  have hdet : P.det ≠ 0 := by
    intro hzero
    apply v15_cubicPowerFamily_discr_ne_zero K hdegree a hgen
    rw [hfamily, hzero]
    norm_num
  refine ⟨P.det.natAbs, Int.natAbs_pos.mpr hdet, ?_⟩
  rw [← v15_cubicPowerFamily_discr_eq_cubicDiscriminant
    K hdegree a hgen]
  rw [hfamily]
  simp [sq_abs]

end

end TraceEuclidean
