import TraceEuclidean.V15QuarticPowerBasis
import TraceEuclidean.V15CubicGeneratorArithmetic

/-!
# Arithmetic certificate of a primitive quartic generator

For a primitive algebraic integer in a quartic number field, this module
extracts the four integral coefficients of its minimal polynomial. It proves
the absence of integral roots and monic quadratic factors, and constructs the
strictly positive index in

`disc(f) = index^2 * disc(K)`.
-/

namespace TraceEuclidean

noncomputable section

open NumberField Module Polynomial
open scoped Matrix NumberField

/-- A quartic ring of integers admits an integral basis indexed by `Fin 4`. -/
theorem v15_exists_ringOfIntegers_basis_fin_four
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4) :
    Nonempty (Basis (Fin 4) ℤ (𝓞 K)) := by
  let e : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Fin 4 :=
    Fintype.equivOfCardEq (by
      rw [← Module.finrank_eq_card_basis
        (NumberField.RingOfIntegers.basis K)]
      exact (NumberField.RingOfIntegers.rank K).trans hdegree)
  exact ⟨(NumberField.RingOfIntegers.basis K).reindex e⟩

/-- The four signed elementary coefficients of an integral quartic minimal
polynomial. -/
def v15QuarticS1
    (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) : ℤ :=
  -(minpoly ℤ (a : K)).coeff 3

def v15QuarticS2
    (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) : ℤ :=
  (minpoly ℤ (a : K)).coeff 2

def v15QuarticS3
    (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) : ℤ :=
  -(minpoly ℤ (a : K)).coeff 1

def v15QuarticS4
    (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) : ℤ :=
  (minpoly ℤ (a : K)).coeff 0

/-- The monic quartic with the signed coefficients used by the finite
enumeration. -/
def v15QuarticPolynomial (s1 s2 s3 s4 : ℤ) : Polynomial ℤ :=
  X ^ 4 - C s1 * X ^ 3 + C s2 * X ^ 2 - C s3 * X + C s4

/-- The integral power family `1, a, a^2, a^3`. -/
def v15QuarticPowerFamily
    (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) :
    Fin 4 → 𝓞 K :=
  ![1, a, a ^ 2, a ^ 3]

/-- A primitive integral generator of a quartic field has a degree-four
integral minimal polynomial. -/
theorem v15_quartic_minpoly_natDegree
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    (minpoly ℤ (a : K)).natDegree = 4 := by
  have h := hgen
  rw [Field.primitive_element_iff_minpoly_natDegree_eq,
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ a.isIntegral_coe,
    (minpoly.monic a.isIntegral_coe).natDegree_map] at h
  exact h.trans hdegree

/-- Evaluation of the explicit quartic agrees with evaluation of the minimal
polynomial. -/
theorem v15_quarticEval_eq_minpoly_eval
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤)
    (z : ℤ) :
    v15QuarticEval (v15QuarticS1 K a) (v15QuarticS2 K a)
        (v15QuarticS3 K a) (v15QuarticS4 K a) z =
      (minpoly ℤ (a : K)).eval z := by
  have hdeg := v15_quartic_minpoly_natDegree K hdegree a hgen
  rw [Polynomial.eval_eq_sum_range' (n := 5)
    (by omega : (minpoly ℤ (a : K)).natDegree < 5)]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ]
  have hlead : (minpoly ℤ (a : K)).coeff 4 = 1 := by
    rw [← hdeg]
    exact (minpoly.monic a.isIntegral_coe).coeff_natDegree
  simp only [Finset.sum_range_zero, zero_add, pow_zero, mul_one, pow_one]
  rw [hlead]
  simp [v15QuarticEval, v15QuarticS1, v15QuarticS2,
    v15QuarticS3, v15QuarticS4]
  ring

/-- The quartic assembled from the four signed coefficients is the integral
minimal polynomial. -/
theorem v15_quarticPolynomial_eq_minpoly
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    v15QuarticPolynomial (v15QuarticS1 K a) (v15QuarticS2 K a)
        (v15QuarticS3 K a) (v15QuarticS4 K a) =
      minpoly ℤ (a : K) := by
  apply Polynomial.funext
  intro z
  simpa [v15QuarticPolynomial, v15QuarticEval] using
    v15_quarticEval_eq_minpoly_eval K hdegree a hgen z

/-- The integral minimal polynomial of a primitive quartic generator has no
integral root. -/
theorem v15_quartic_minpoly_no_integer_root
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    ∀ z : ℤ, v15QuarticEval (v15QuarticS1 K a) (v15QuarticS2 K a)
      (v15QuarticS3 K a) (v15QuarticS4 K a) z ≠ 0 := by
  intro z hz
  have hdeg := v15_quartic_minpoly_natDegree K hdegree a hgen
  apply (minpoly.irreducible a.isIntegral_coe).not_isRoot_of_natDegree_ne_one
    (by omega : (minpoly ℤ (a : K)).natDegree ≠ 1)
  rw [Polynomial.IsRoot]
  rw [← v15_quarticEval_eq_minpoly_eval K hdegree a hgen z]
  exact hz

/-- A coefficient witness is exactly a factorization into two monic
quadratics. -/
theorem v15_quarticPolynomial_eq_mul_of_factorWitness
    (s1 s2 s3 s4 u v p q : ℤ)
    (hfactor : V15QuarticQuadraticFactorWitness
      s1 s2 s3 s4 u v p q) :
    v15QuarticPolynomial s1 s2 s3 s4 =
      (X ^ 2 + C u * X + C v) * (X ^ 2 + C p * X + C q) := by
  rcases hfactor with ⟨h1, h2, h3, h4⟩
  have hs1 : s1 = -(u + p) := by omega
  have hs3 : s3 = -(u * q + v * p) := by omega
  rw [hs1, ← h2, hs3, ← h4]
  simp only [v15QuarticPolynomial, map_neg, map_add, map_mul]
  ring

/-- Irreducibility of a primitive quartic minimal polynomial excludes every
monic quadratic factor witness. -/
theorem v15_quartic_minpoly_no_quadratic_factor
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    ∀ u v p q : ℤ,
      ¬V15QuarticQuadraticFactorWitness
        (v15QuarticS1 K a) (v15QuarticS2 K a)
        (v15QuarticS3 K a) (v15QuarticS4 K a) u v p q := by
  intro u v p q hfactor
  let f : Polynomial ℤ := X ^ 2 + C u * X + C v
  let g : Polynomial ℤ := X ^ 2 + C p * X + C q
  have hpoly := v15_quarticPolynomial_eq_minpoly K hdegree a hgen
  have hmul := v15_quarticPolynomial_eq_mul_of_factorWitness
    (v15QuarticS1 K a) (v15QuarticS2 K a)
    (v15QuarticS3 K a) (v15QuarticS4 K a) u v p q hfactor
  have hirr : Irreducible (f * g) := by
    rw [← hmul, hpoly]
    exact minpoly.irreducible a.isIntegral_coe
  rcases of_irreducible_mul hirr with hf | hg
  · exact (Polynomial.not_isUnit_of_natDegree_pos f (by
      have hcoeff : f.coeff 2 ≠ 0 := by
        simp only [f, Polynomial.coeff_add, Polynomial.coeff_X_pow,
          Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
        norm_num
      have hle := Polynomial.le_natDegree_of_ne_zero hcoeff
      omega)) hf
  · exact (Polynomial.not_isUnit_of_natDegree_pos g (by
      have hcoeff : g.coeff 2 ≠ 0 := by
        simp only [g, Polynomial.coeff_add, Polynomial.coeff_X_pow,
          Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
        norm_num
      have hle := Polynomial.le_natDegree_of_ne_zero hcoeff
      omega)) hg

/-- After localization, the integral quartic power family is the rational
power basis generated by `a`. -/
theorem v15_quarticPowerFamily_discr_eq_powerBasis
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    Algebra.discr ℚ
        (fun i ↦ ((v15QuarticPowerFamily K a i : 𝓞 K) : K)) =
      Algebra.discr ℚ
        (PowerBasis.ofAdjoinEqTop (IsIntegral.of_finite ℚ (a : K))
          (Algebra.adjoin_eq_top_of_primitive_element
            (IsIntegral.of_finite ℚ (a : K)).isAlgebraic hgen)).basis := by
  classical
  let hint : IsIntegral ℚ (a : K) := IsIntegral.of_finite ℚ (a : K)
  let hsub : Algebra.adjoin ℚ {(a : K)} = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element hint.isAlgebraic hgen
  let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop hint hsub
  have hdim : pb.dim = 4 := by
    rw [PowerBasis.ofAdjoinEqTop_dim]
    have h := hgen
    rw [Field.primitive_element_iff_minpoly_natDegree_eq] at h
    exact h.trans hdegree
  let e : Fin pb.dim ≃ Fin 4 := finCongr hdim
  change Algebra.discr ℚ
      (fun i ↦ ((v15QuarticPowerFamily K a i : 𝓞 K) : K)) =
    Algebra.discr ℚ pb.basis
  rw [← Algebra.discr_reindex ℚ pb.basis e]
  congr 1
  ext i
  change ((v15QuarticPowerFamily K a i : 𝓞 K) : K) =
    pb.basis (e.symm i)
  rw [pb.basis_eq_pow]
  have he : ((e.symm i : Fin pb.dim) : ℕ) = (i : ℕ) := rfl
  rw [he]
  fin_cases i <;> simp [v15QuarticPowerFamily, pb]

/-- The discriminant of the integral power family equals the explicit
quartic discriminant. -/
theorem v15_quarticPowerFamily_discr_eq_quarticDiscriminant
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    Algebra.discr ℤ (v15QuarticPowerFamily K a) =
      v15QuarticDiscriminant (v15QuarticS1 K a) (v15QuarticS2 K a)
        (v15QuarticS3 K a) (v15QuarticS4 K a) := by
  classical
  apply Rat.intCast_injective
  rw [v15_discr_ringOfIntegers_cast]
  let hint : IsIntegral ℚ (a : K) := IsIntegral.of_finite ℚ (a : K)
  let hsub : Algebra.adjoin ℚ {(a : K)} = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element hint.isAlgebraic hgen
  let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop hint hsub
  have hpb : Algebra.discr ℚ
      (fun i ↦ ((v15QuarticPowerFamily K a i : 𝓞 K) : K)) =
        Algebra.discr ℚ pb.basis := by
    exact v15_quarticPowerFamily_discr_eq_powerBasis K hdegree a hgen
  rw [hpb]
  have hdim : pb.dim = 4 := by
    rw [PowerBasis.ofAdjoinEqTop_dim]
    have h := hgen
    rw [Field.primitive_element_iff_minpoly_natDegree_eq] at h
    exact h.trans hdegree
  rw [v15_powerBasis_discr_dim_four pb hdim]
  have hmin : pb.minpolyGen =
      (minpoly ℤ (a : K)).map (algebraMap ℤ ℚ) := by
    rw [pb.minpolyGen_eq]
    exact minpoly.isIntegrallyClosed_eq_field_fractions' ℚ a.isIntegral_coe
  rw [hmin]
  simp only [Polynomial.coeff_map]
  simp [v15QuarticS1, v15QuarticS2, v15QuarticS3,
    v15QuarticS4, v15QuarticDiscriminant]
  ring

/-- The primitive quartic power family has nonzero integral discriminant. -/
theorem v15_quarticPowerFamily_discr_ne_zero
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    Algebra.discr ℤ (v15QuarticPowerFamily K a) ≠ 0 := by
  classical
  intro hzero
  have hcast := congrArg (fun z : ℤ ↦ (z : ℚ)) hzero
  rw [v15_discr_ringOfIntegers_cast] at hcast
  simp only [Int.cast_zero] at hcast
  rw [v15_quarticPowerFamily_discr_eq_powerBasis K hdegree a hgen] at hcast
  exact (Algebra.discr_not_zero_of_basis ℚ
    (PowerBasis.ofAdjoinEqTop (IsIntegral.of_finite ℚ (a : K))
      (Algebra.adjoin_eq_top_of_primitive_element
        (IsIntegral.of_finite ℚ (a : K)).isAlgebraic hgen)).basis) hcast

/-- A primitive quartic algebraic integer determines a strictly positive
natural index with the exact field-discriminant relation. -/
theorem v15_quartic_exists_positive_index
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤)
    (bO : Basis (Fin 4) ℤ (𝓞 K)) :
    ∃ index : ℕ, 0 < index ∧
      v15QuarticDiscriminant (v15QuarticS1 K a) (v15QuarticS2 K a)
          (v15QuarticS3 K a) (v15QuarticS4 K a) =
        (index : ℤ) ^ 2 * NumberField.discr K := by
  classical
  let P := bO.toMatrix (v15QuarticPowerFamily K a)
  have hfamily : Algebra.discr ℤ (v15QuarticPowerFamily K a) =
      P.det ^ 2 * NumberField.discr K := by
    calc
      Algebra.discr ℤ (v15QuarticPowerFamily K a) =
          Algebra.discr ℤ
            (bO ᵥ* P.map (algebraMap ℤ (𝓞 K))) := by
        rw [bO.toMatrix_map_vecMul (v15QuarticPowerFamily K a)]
      _ = P.det ^ 2 * Algebra.discr ℤ bO :=
        Algebra.discr_of_matrix_vecMul bO P
      _ = P.det ^ 2 * NumberField.discr K := by
        rw [NumberField.discr_eq_discr K bO]
  have hdet : P.det ≠ 0 := by
    intro hzero
    apply v15_quarticPowerFamily_discr_ne_zero K hdegree a hgen
    rw [hfamily, hzero]
    norm_num
  refine ⟨P.det.natAbs, Int.natAbs_pos.mpr hdet, ?_⟩
  rw [← v15_quarticPowerFamily_discr_eq_quarticDiscriminant
    K hdegree a hgen]
  rw [hfamily]
  simp [sq_abs]

end

end TraceEuclidean
