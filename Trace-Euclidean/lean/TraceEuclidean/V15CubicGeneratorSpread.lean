import TraceEuclidean.V15CubicGeneratorArithmetic
import TraceEuclidean.V15HunterNumberFieldProjection

/-!
# Trace and Euclidean-spread bridge for cubic generators

This module identifies the coefficient expression

`2 * s1^2 - 6 * s2`

with three times the squared norm of the centered Euclidean Minkowski
embedding of a primitive cubic algebraic integer.  It supplies the exact
bridge from the geometric Hunter vector to the finite coefficient reduction.
-/

namespace TraceEuclidean

noncomputable section

open NumberField Module Polynomial Finset
open scoped NumberField

/-- In a totally real field, real infinite places are equivalent to all
complex embeddings over `ℚ`. -/
noncomputable def v15RealPlacesEquivComplexEmbeddings
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] :
    {w : NumberField.InfinitePlace K // w.IsReal} ≃ (K →ₐ[ℚ] ℂ) where
  toFun w := w.1.embedding.toRatAlgHom
  invFun φ :=
    ⟨NumberField.InfinitePlace.mk φ.toRingHom,
      ⟨φ.toRingHom,
        NumberField.IsTotallyReal.complexEmbedding_isReal φ.toRingHom,
        rfl⟩⟩
  left_inv w := by
    apply Subtype.ext
    exact NumberField.InfinitePlace.mk_embedding w.1
  right_inv φ := by
    ext x
    change (NumberField.InfinitePlace.embedding
      (NumberField.InfinitePlace.mk φ.toRingHom)) x = φ x
    rw [NumberField.InfinitePlace.embedding_mk_eq_of_isReal
      (NumberField.IsTotallyReal.complexEmbedding_isReal φ.toRingHom)]
    rfl

open scoped Classical in
/-- In a totally real number field, the sum over real-place coordinates is
the real value of the field trace. -/
theorem v15_sum_realPlaces_eq_trace
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (a : K) :
    ∑ w : {w : NumberField.InfinitePlace K // w.IsReal},
        NumberField.InfinitePlace.embedding_of_isReal w.prop a =
      ((Algebra.trace ℚ K a : ℚ) : ℝ) := by
  classical
  have htrace := trace_eq_sum_embeddings ℂ
    (K := ℚ) (L := K) (x := a)
  have hre := congrArg Complex.re htrace
  rw [← (v15RealPlacesEquivComplexEmbeddings K).sum_comp] at hre
  symm
  calc
    ((Algebra.trace ℚ K a : ℚ) : ℝ) =
        (((Algebra.trace ℚ K a : ℚ) : ℂ)).re := by simp
    _ = ∑ w : {w : NumberField.InfinitePlace K // w.IsReal},
          (((v15RealPlacesEquivComplexEmbeddings K) w) a).re := by
      simpa [eq_ratCast, Complex.re_sum] using hre
    _ = ∑ w : {w : NumberField.InfinitePlace K // w.IsReal},
          NumberField.InfinitePlace.embedding_of_isReal w.prop a := by
      apply Finset.sum_congr rfl
      intro w hw
      have hemb := NumberField.InfinitePlace.embedding_of_isReal_apply
        w.prop a
      exact_mod_cast congrArg Complex.re hemb

/-- The Euclidean-coordinate version of the mixed Minkowski embedding. -/
def v15EuclideanEmbedding
    (K : Type*) [Field K] [NumberField K] (a : K) :
    NumberField.mixedEmbedding.euclidean.mixedSpace K :=
  (NumberField.mixedEmbedding.euclidean.toMixed K).symm
    (NumberField.mixedEmbedding K a)

open scoped Classical in
/-- Multiplication by a rational scalar before the Euclidean Minkowski
embedding agrees with the corresponding real scalar multiplication. -/
theorem v15_euclideanEmbedding_rat_smul
    (K : Type*) [Field K] [NumberField K]
    (q : ℚ) (a : K) :
    v15EuclideanEmbedding K (algebraMap ℚ K q * a) =
      (q : ℝ) • v15EuclideanEmbedding K a := by
  apply (NumberField.mixedEmbedding.euclidean.toMixed K).injective
  unfold v15EuclideanEmbedding
  rw [ContinuousLinearEquiv.apply_symm_apply, map_smul]
  ext <;> simp

open scoped Classical in
/-- The Euclidean Minkowski embedding of a rational affine expression in
one element is the same real affine expression in its embedded vectors. -/
theorem v15_euclideanEmbedding_rat_add_rat_mul
    (K : Type*) [Field K] [NumberField K]
    (r s : ℚ) (a : K) :
    v15EuclideanEmbedding K
        (algebraMap ℚ K r + algebraMap ℚ K s * a) =
      (r : ℝ) • v15EuclideanOne K +
        (s : ℝ) • v15EuclideanEmbedding K a := by
  unfold v15EuclideanEmbedding
  rw [map_add, map_add]
  rw [v15_euclideanEmbedding_algebraMap_rat K r]
  rw [show
    (NumberField.mixedEmbedding.euclidean.toMixed K).symm
        (NumberField.mixedEmbedding K (algebraMap ℚ K s * a)) =
      (s : ℝ) • v15EuclideanEmbedding K a by
    simpa [v15EuclideanEmbedding] using
      v15_euclideanEmbedding_rat_smul K s a]
  rfl

open scoped Classical in
/-- Coordinate description of the Euclidean Minkowski embedding. -/
theorem v15_euclideanEmbedding_eq
    (K : Type*) [Field K] [NumberField K] (a : K) :
    v15EuclideanEmbedding K a =
      WithLp.toLp 2
        (WithLp.toLp 2 (fun w :
            {w : NumberField.InfinitePlace K // w.IsReal} ↦
              NumberField.InfinitePlace.embedding_of_isReal w.prop a),
          WithLp.toLp 2 (fun w :
            {w : NumberField.InfinitePlace K // w.IsComplex} ↦
              w.1.embedding a)) := by
  apply (NumberField.mixedEmbedding.euclidean.toMixed K).injective
  unfold v15EuclideanEmbedding
  rw [ContinuousLinearEquiv.apply_symm_apply]
  ext <;> simp [NumberField.mixedEmbedding.euclidean.toMixed,
    NumberField.mixedEmbedding.mixedEmbedding_apply_isReal,
    NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex]

open scoped Classical in
/-- Pairing the diagonal vector with an embedded element gives its trace. -/
theorem v15_inner_euclideanOne_euclideanEmbedding
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (a : K) :
    inner ℝ (v15EuclideanOne K) (v15EuclideanEmbedding K a) =
      ((Algebra.trace ℚ K a : ℚ) : ℝ) := by
  letI : IsEmpty
      {w : NumberField.InfinitePlace K // w.IsComplex} :=
    Fintype.card_eq_zero_iff.mp
      (NumberField.IsTotallyReal.nrComplexPlaces_eq_zero K)
  rw [v15_euclideanEmbedding_eq]
  unfold v15EuclideanOne
  rw [WithLp.prod_inner_apply]
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp [v15_sum_realPlaces_eq_trace K a]

open scoped Classical in
/-- The squared Euclidean norm of an embedded element is the trace of its
square in a totally real field. -/
theorem v15_inner_euclideanEmbedding_self
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (a : K) :
    inner ℝ (v15EuclideanEmbedding K a) (v15EuclideanEmbedding K a) =
      ((Algebra.trace ℚ K (a ^ 2) : ℚ) : ℝ) := by
  letI : IsEmpty
      {w : NumberField.InfinitePlace K // w.IsComplex} :=
    Fintype.card_eq_zero_iff.mp
      (NumberField.IsTotallyReal.nrComplexPlaces_eq_zero K)
  rw [v15_euclideanEmbedding_eq]
  rw [WithLp.prod_inner_apply]
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp [← map_pow, v15_sum_realPlaces_eq_trace K (a ^ 2)]

/-- The trace of a primitive cubic generator is its first integral
coefficient `s1`. -/
theorem v15_cubic_trace_eq_s1
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 3)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    Algebra.trace ℚ K (a : K) = (v15CubicS1 K a : ℚ) := by
  let hint : IsIntegral ℚ (a : K) := IsIntegral.of_finite ℚ (a : K)
  let hsub : Algebra.adjoin ℚ {(a : K)} = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element hint.isAlgebraic hgen
  let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop hint hsub
  have hdim : pb.dim = 3 := by
    rw [PowerBasis.ofAdjoinEqTop_dim]
    have h := hgen
    rw [Field.primitive_element_iff_minpoly_natDegree_eq] at h
    exact h.trans hdegree
  have ht := v15_powerBasis_trace_gen_dim_three pb hdim
  have hmin : pb.minpolyGen =
      (minpoly ℤ (a : K)).map (algebraMap ℤ ℚ) := by
    rw [pb.minpolyGen_eq]
    exact minpoly.isIntegrallyClosed_eq_field_fractions' ℚ a.isIntegral_coe
  rw [hmin] at ht
  simpa [pb, v15CubicS1, Polynomial.coeff_map] using ht

/-- Newton's second identity for the primitive cubic generator. -/
theorem v15_cubic_trace_sq_eq_s1_sq_sub_two_s2
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 3)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    Algebra.trace ℚ K ((a : K) ^ 2) =
      (v15CubicS1 K a : ℚ) ^ 2 - 2 * (v15CubicS2 K a : ℚ) := by
  let hint : IsIntegral ℚ (a : K) := IsIntegral.of_finite ℚ (a : K)
  let hsub : Algebra.adjoin ℚ {(a : K)} = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element hint.isAlgebraic hgen
  let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop hint hsub
  have hdim : pb.dim = 3 := by
    rw [PowerBasis.ofAdjoinEqTop_dim]
    have h := hgen
    rw [Field.primitive_element_iff_minpoly_natDegree_eq] at h
    exact h.trans hdegree
  have ht := v15_powerBasis_trace_gen_sq_dim_three pb hdim
  have hmin : pb.minpolyGen =
      (minpoly ℤ (a : K)).map (algebraMap ℤ ℚ) := by
    rw [pb.minpolyGen_eq]
    exact minpoly.isIntegrallyClosed_eq_field_fractions' ℚ a.isIntegral_coe
  rw [hmin] at ht
  simpa [pb, v15CubicS1, v15CubicS2, Polynomial.coeff_map] using ht

open scoped Classical in
/-- The centered Euclidean norm is the standard quadratic trace expression. -/
theorem v15_cubic_center_norm_eq_trace_expression
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 3) (a : K) :
    let e := v15EuclideanOne K
    let he : inner ℝ e e ≠ 0 := by
      rw [v15_inner_euclideanOne_self_eq_three K hreal hdegree]
      norm_num
    3 * ‖v15HunterCenterLinearMap e he (v15EuclideanEmbedding K a)‖ ^ 2 =
      3 * ((Algebra.trace ℚ K (a ^ 2) : ℚ) : ℝ) -
        ((Algebra.trace ℚ K a : ℚ) : ℝ) ^ 2 := by
  letI : NumberField.IsTotallyReal K := hreal
  dsimp only
  let he : inner ℝ (v15EuclideanOne K) (v15EuclideanOne K) ≠ 0 := by
    rw [v15_inner_euclideanOne_self_eq_three K hreal hdegree]
    norm_num
  rw [← real_inner_self_eq_norm_sq]
  change 3 * inner ℝ
      (v15HunterCenter (v15EuclideanOne K) (v15EuclideanEmbedding K a))
      (v15HunterCenter (v15EuclideanOne K) (v15EuclideanEmbedding K a)) = _
  rw [v15_inner_center_center (v15EuclideanOne K)
    (v15EuclideanEmbedding K a) (v15EuclideanEmbedding K a) he]
  rw [v15_inner_euclideanOne_self_eq_three K hreal hdegree]
  rw [v15_inner_euclideanOne_euclideanEmbedding K a]
  rw [v15_inner_euclideanEmbedding_self K a]
  ring

open scoped Classical in
/-- Exact bridge from the cubic coefficient spread to the Hunter centered
norm. -/
theorem v15_cubicSpread_cast_eq_center_norm
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 3)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤)
    (he : inner ℝ (v15EuclideanOne K) (v15EuclideanOne K) ≠ 0) :
    ((v15CubicSpread (v15CubicS1 K a) (v15CubicS2 K a) : ℤ) : ℝ) =
      3 * ‖v15HunterCenterLinearMap (v15EuclideanOne K) he
        (v15EuclideanEmbedding K (a : K))‖ ^ 2 := by
  letI : NumberField.IsTotallyReal K := hreal
  rw [v15_cubic_center_norm_eq_trace_expression K hreal hdegree (a : K)]
  rw [v15_cubic_trace_eq_s1 K hdegree a hgen]
  rw [v15_cubic_trace_sq_eq_s1_sq_sub_two_s2 K hdegree a hgen]
  push_cast
  simp only [v15CubicSpread]
  push_cast
  ring

end

end TraceEuclidean
