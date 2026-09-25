import TraceEuclidean.V15QuarticGeneratorSpread
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.PosDef

/-!
# Hermite positivity for a primitive quartic generator

This module identifies the third leading Hermite minor of a primitive
quartic minimal polynomial with the Gram determinant of the embedded vectors
`1, a, a^2`. Their linear independence proves the required positivity, so
this condition is no longer part of the residual Hunter input.
-/

namespace TraceEuclidean

noncomputable section

open NumberField Module Polynomial Finset
open scoped NumberField Matrix

open scoped Classical in
/-- In a totally real number field, the Euclidean inner product of two
Minkowski embeddings is the rational trace of their product. -/
theorem v15_inner_euclideanEmbedding_mul_eq_trace
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (a b : K) :
    inner ℝ (v15EuclideanEmbedding K a) (v15EuclideanEmbedding K b) =
      ((Algebra.trace ℚ K (a * b) : ℚ) : ℝ) := by
  letI : IsEmpty
      {w : NumberField.InfinitePlace K // w.IsComplex} :=
    Fintype.card_eq_zero_iff.mp
      (NumberField.IsTotallyReal.nrComplexPlaces_eq_zero K)
  rw [v15_euclideanEmbedding_eq, v15_euclideanEmbedding_eq]
  rw [WithLp.prod_inner_apply]
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp [← map_mul, mul_comm, v15_sum_realPlaces_eq_trace K (a * b)]

/-- The embedded quartic power family `1, a, a^2, a^3`. -/
def v15QuarticEuclideanPowerFamily
    (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) :
    Fin 4 → NumberField.mixedEmbedding.euclidean.mixedSpace K :=
  fun i =>
    v15EuclideanEmbedding K ((v15QuarticPowerFamily K a i : 𝓞 K) : K)

open scoped Classical in
/-- The Gram determinant of the embedded power family is its rational
discriminant. -/
theorem v15_quarticEuclideanPowerFamily_gram_det
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (a : 𝓞 K) :
    (Matrix.gram ℝ (v15QuarticEuclideanPowerFamily K a)).det =
      ((Algebra.discr ℚ
        (fun i : Fin 4 =>
          ((v15QuarticPowerFamily K a i : 𝓞 K) : K)) : ℚ) : ℝ) := by
  rw [Algebra.discr_def]
  have hmatrix :
      Matrix.gram ℝ (v15QuarticEuclideanPowerFamily K a) =
        (Algebra.traceMatrix ℚ
          (fun i : Fin 4 =>
            ((v15QuarticPowerFamily K a i : 𝓞 K) : K))).map
              (algebraMap ℚ ℝ) := by
    ext i j
    simp only [Matrix.gram_apply, v15QuarticEuclideanPowerFamily,
      Algebra.traceMatrix_apply, Algebra.traceForm_apply,
      Matrix.map_apply]
    rw [v15_inner_euclideanEmbedding_mul_eq_trace]
    change (algebraMap ℚ ℝ) _ = (algebraMap ℚ ℝ) _
    rfl
  rw [hmatrix]
  exact (RingHom.map_det (algebraMap ℚ ℝ) _).symm

open scoped Classical in
/-- A primitive quartic generator gives four linearly independent embedded
power vectors. -/
theorem v15_quarticEuclideanPowerFamily_linearIndependent
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    LinearIndependent ℝ (v15QuarticEuclideanPowerFamily K a) := by
  apply Matrix.linearIndependent_of_det_gram_ne_zero
  rw [v15_quarticEuclideanPowerFamily_gram_det]
  have hInt := v15_quarticPowerFamily_discr_ne_zero K hdegree a hgen
  have hRat :
      ((Algebra.discr ℤ (v15QuarticPowerFamily K a) : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast hInt
  rw [v15_discr_ringOfIntegers_cast] at hRat
  exact_mod_cast hRat

/-- The first two embedded power vectors used by the centered spread. -/
def v15QuarticSpreadFamily
    (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) :
    Fin 2 → NumberField.mixedEmbedding.euclidean.mixedSpace K :=
  v15QuarticEuclideanPowerFamily K a ∘ Fin.castLE (by omega : 2 ≤ 4)

@[simp]
theorem v15QuarticSpreadFamily_zero
    (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) :
    v15QuarticSpreadFamily K a 0 =
      v15EuclideanEmbedding K (1 : K) :=
  rfl

@[simp]
theorem v15QuarticSpreadFamily_one
    (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) :
    v15QuarticSpreadFamily K a 1 =
      v15EuclideanEmbedding K (a : K) :=
  rfl

open scoped Classical in
/-- The embedded vectors 1 and a are linearly independent for a primitive
quartic generator. -/
theorem v15_quarticSpreadFamily_linearIndependent
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    LinearIndependent ℝ (v15QuarticSpreadFamily K a) := by
  exact LinearIndependent.comp
    (v15_quarticEuclideanPowerFamily_linearIndependent
      K hdegree a hgen)
    (Fin.castLE (by omega : 2 ≤ 4)) (Fin.castLE_injective _)

open scoped Classical in
/-- The Gram determinant of the embedded vectors 1 and a is positive. -/
theorem v15_quarticSpreadFamily_gram_det_pos
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    0 < (Matrix.gram ℝ (v15QuarticSpreadFamily K a)).det := by
  exact (Matrix.posDef_gram_of_linearIndependent
    (v15_quarticSpreadFamily_linearIndependent
      K hdegree a hgen)).det_pos

/-- The first three embedded power vectors used by the Hermite minor. -/
def v15QuarticHermiteFamily
    (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) :
    Fin 3 → NumberField.mixedEmbedding.euclidean.mixedSpace K :=
  v15QuarticEuclideanPowerFamily K a ∘ Fin.castLE (by omega : 3 ≤ 4)

@[simp]
theorem v15QuarticHermiteFamily_zero
    (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) :
    v15QuarticHermiteFamily K a 0 =
      v15EuclideanEmbedding K (1 : K) :=
  rfl

@[simp]
theorem v15QuarticHermiteFamily_one
    (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) :
    v15QuarticHermiteFamily K a 1 =
      v15EuclideanEmbedding K (a : K) :=
  rfl

@[simp]
theorem v15QuarticHermiteFamily_two
    (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) :
    v15QuarticHermiteFamily K a 2 =
      v15EuclideanEmbedding K ((a : K) ^ 2) := by
  rfl

open scoped Classical in
/-- Restricting the full power family to `1, a, a^2` preserves linear
independence. -/
theorem v15_quarticHermiteFamily_linearIndependent
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    LinearIndependent ℝ (v15QuarticHermiteFamily K a) := by
  exact LinearIndependent.comp
    (v15_quarticEuclideanPowerFamily_linearIndependent
      K hdegree a hgen)
    (Fin.castLE (by omega : 3 ≤ 4)) (Fin.castLE_injective _)

open scoped Classical in
/-- The Gram determinant of `1, a, a^2` is strictly positive. -/
theorem v15_quarticHermiteFamily_gram_det_pos
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    0 < (Matrix.gram ℝ (v15QuarticHermiteFamily K a)).det := by
  exact (Matrix.posDef_gram_of_linearIndependent
    (v15_quarticHermiteFamily_linearIndependent
      K hdegree a hgen)).det_pos

open scoped Classical in
/-- In degree four, the trace of one is four. -/
theorem v15_trace_one_dim_four
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4) :
    Algebra.trace ℚ K (1 : K) = 4 := by
  rw [Algebra.trace]
  simp only [LinearMap.comp_apply]
  have h : (Algebra.lmul ℚ K).toLinearMap 1 = 1 := by
    ext x
    simp
  rw [h, LinearMap.trace_one, hdegree]
  norm_num

open scoped Classical in
/-- The centered quartic spread is exactly the two-vector Gram
determinant. -/
theorem v15_quarticSpread_cast_eq_gram_det
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    ((v15QuarticSpread
        (v15QuarticS1 K a) (v15QuarticS2 K a) : ℤ) : ℝ) =
      (Matrix.gram ℝ (v15QuarticSpreadFamily K a)).det := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.gram_apply, v15QuarticSpreadFamily_zero,
    v15QuarticSpreadFamily_one]
  simp_rw [v15_inner_euclideanEmbedding_mul_eq_trace]
  simp only [one_mul, mul_one]
  have hsq : (a : K) * (a : K) = (a : K) ^ 2 := by ring
  rw [hsq]
  rw [v15_trace_one_dim_four K hdegree]
  rw [v15_quartic_trace_eq_s1 K hdegree a hgen]
  rw [v15_quartic_trace_sq_eq_s1_sq_sub_two_s2
    K hdegree a hgen]
  simp only [v15QuarticSpread, v15QuarticSecondPowerSum]
  push_cast
  ring

open scoped Classical in
/-- A primitive generator of a totally real quartic field automatically has
strictly positive centered spread. -/
theorem v15_quarticSpread_pos
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    0 < v15QuarticSpread
      (v15QuarticS1 K a) (v15QuarticS2 K a) := by
  letI : NumberField.IsTotallyReal K := hreal
  have hdet :=
    v15_quarticSpreadFamily_gram_det_pos K hdegree a hgen
  rw [← v15_quarticSpread_cast_eq_gram_det
    K hdegree a hgen] at hdet
  exact_mod_cast hdet

open scoped Classical in
/-- The coefficient formula for the third Hermite minor is exactly the Gram
determinant of the first three embedded power vectors. -/
theorem v15_quarticHermiteMinorThree_cast_eq_gram_det
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    ((v15QuarticHermiteMinorThree
        (v15QuarticS1 K a) (v15QuarticS2 K a)
        (v15QuarticS3 K a) (v15QuarticS4 K a) : ℤ) : ℝ) =
      (Matrix.gram ℝ (v15QuarticHermiteFamily K a)).det := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.gram_apply, v15QuarticHermiteFamily_zero,
    v15QuarticHermiteFamily_one, v15QuarticHermiteFamily_two]
  simp_rw [v15_inner_euclideanEmbedding_mul_eq_trace]
  simp only [one_mul, mul_one]
  have hsq : (a : K) * (a : K) = (a : K) ^ 2 := by ring
  have hcubel : (a : K) * (a : K) ^ 2 = (a : K) ^ 3 := by ring
  have hcuber : (a : K) ^ 2 * (a : K) = (a : K) ^ 3 := by ring
  have hfour : (a : K) ^ 2 * (a : K) ^ 2 = (a : K) ^ 4 := by ring
  rw [hsq, hcubel, hcuber, hfour]
  rw [v15_trace_one_dim_four K hdegree]
  rw [v15_quartic_trace_eq_s1 K hdegree a hgen]
  rw [v15_quartic_trace_sq_eq_s1_sq_sub_two_s2
    K hdegree a hgen]
  rw [v15_quartic_trace_cube_eq_coefficients K hdegree a hgen]
  rw [v15_quartic_trace_fourth_eq_coefficients K hdegree a hgen]
  simp only [v15QuarticHermiteMinorThree]
  push_cast
  ring

open scoped Classical in
/-- A primitive generator of a totally real quartic field automatically
satisfies positivity of the third Hermite minor. -/
theorem v15_quarticHermiteMinorThree_pos
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    0 < v15QuarticHermiteMinorThree
      (v15QuarticS1 K a) (v15QuarticS2 K a)
      (v15QuarticS3 K a) (v15QuarticS4 K a) := by
  letI : NumberField.IsTotallyReal K := hreal
  have hdet :=
    v15_quarticHermiteFamily_gram_det_pos K hdegree a hgen
  rw [← v15_quarticHermiteMinorThree_cast_eq_gram_det
    K hdegree a hgen] at hdet
  exact_mod_cast hdet

end

end TraceEuclidean
