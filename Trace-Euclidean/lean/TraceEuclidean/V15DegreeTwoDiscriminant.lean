import TraceEuclidean.GlobalLatticeClass
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Trace.Basic

/-!
# The exact quadratic discriminant lower bound

This module proves internally that a totally real number field of degree two
has absolute discriminant at least five.  The proof combines mathlib's exact
Minkowski bound with the elementary fact, proved here from the two complex
embeddings, that a quadratic field discriminant is not a square in `ℚ`.
-/

namespace TraceEuclidean

open Matrix Module Finset
open scoped NumberField

noncomputable section

/-- The discriminant of a power basis differs from the field discriminant by
the square of the rational change-of-basis determinant. -/
theorem v15_powerBasis_discr_eq_det_sq_mul_field
    (K : Type*) [Field K] [NumberField K] (pb : PowerBasis ℚ K) :
    ∃ q : ℚ, Algebra.discr ℚ pb.basis =
      q ^ 2 * (NumberField.discr K : ℚ) := by
  let B := pb.basis
  let B₀ := (NumberField.integralBasis K).reindex
    ((NumberField.integralBasis K).indexEquiv B)
  refine ⟨(B₀.toMatrix B).det, ?_⟩
  have hchange : Algebra.discr ℚ B =
      (B₀.toMatrix B).det ^ 2 * Algebra.discr ℚ B₀ := by
    calc
      Algebra.discr ℚ B =
          Algebra.discr ℚ
            (B₀ ᵥ* (B₀.toMatrix B).map (algebraMap ℚ K)) := by
              rw [B₀.toMatrix_map_vecMul B]
      _ = (B₀.toMatrix B).det ^ 2 * Algebra.discr ℚ B₀ :=
        Algebra.discr_of_matrix_vecMul B₀ (B₀.toMatrix B)
  have hfield : Algebra.discr ℚ B₀ =
      (NumberField.discr K : ℚ) := by
    unfold B₀
    rw [Basis.coe_reindex, Algebra.discr_reindex,
      ← NumberField.coe_discr]
  rw [hfield] at hchange
  exact hchange

/-- A square field discriminant would force every power-basis discriminant
to be a square. -/
theorem v15_powerBasis_discr_isSquare_of_field_discr_isSquare
    (K : Type*) [Field K] [NumberField K]
    (pb : PowerBasis ℚ K)
    (h : IsSquare (NumberField.discr K : ℚ)) :
    IsSquare (Algebra.discr ℚ pb.basis) := by
  rcases h with ⟨r, hr⟩
  rcases v15_powerBasis_discr_eq_det_sq_mul_field K pb with ⟨q, hq⟩
  refine ⟨q * r, ?_⟩
  rw [hq, hr]
  ring

/-- The field discriminant of a quadratic number field is not a square in
`ℚ`.  If it were, the difference of the two images of a primitive element
would be rational; its trace then makes each image rational, contradicting
that the primitive element has degree two. -/
theorem v15_field_discr_not_isSquare_of_finrank_two
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 2) :
    ¬ IsSquare (NumberField.discr K : ℚ) := by
  intro hdisc
  let pb : PowerBasis ℚ K := Field.powerBasisOfFiniteOfSeparable ℚ K
  have hdim : pb.dim = 2 := by
    rw [← PowerBasis.finrank pb, hdegree]
  have hsquare :=
    v15_powerBasis_discr_isSquare_of_field_discr_isSquare K pb hdisc
  rcases hsquare with ⟨q, hq⟩
  let B : Basis (Fin 2) ℚ K :=
    pb.basis.reindex (finCongr hdim)
  let e : Fin 2 ≃ (K →ₐ[ℚ] ℂ) := by
    refine Fintype.equivOfCardEq ?_
    rw [Fintype.card_fin, AlgHom.card]
    exact hdegree.symm
  have hBdisc : Algebra.discr ℚ B = q ^ 2 := by
    calc
      Algebra.discr ℚ B = Algebra.discr ℚ pb.basis := by
        simpa [B, Basis.coe_reindex] using
          (Algebra.discr_reindex ℚ pb.basis (finCongr hdim))
      _ = q ^ 2 := by simpa [pow_two] using hq
  have hdet :=
    Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two
      ℚ ℂ B e
  rw [hBdisc] at hdet
  push_cast at hdet
  have hmatrix :
      (Algebra.embeddingsMatrixReindex ℚ ℂ B e).det =
        e 1 pb.gen - e 0 pb.gen := by
    rw [Matrix.det_fin_two]
    simp [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix,
      B, PowerBasis.coe_basis]
  rw [hmatrix] at hdet
  have hdiff :
      e 1 pb.gen - e 0 pb.gen = (q : ℂ) ∨
        e 1 pb.gen - e 0 pb.gen = -(q : ℂ) := by
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hdet.symm
  have htrace := trace_eq_sum_embeddings
    (K := ℚ) (L := K) (E := ℂ) (x := pb.gen)
  rw [← e.sum_comp] at htrace
  simp only [Fin.sum_univ_two, eq_ratCast] at htrace
  have hgen : pb.gen ∈ (algebraMap ℚ K).range := by
    rcases hdiff with hdiff | hdiff
    · refine ⟨(Algebra.trace ℚ K pb.gen - q) / 2, ?_⟩
      apply (e 0).injective
      change (e 0) (algebraMap ℚ K
        ((Algebra.trace ℚ K pb.gen - q) / 2)) = (e 0) pb.gen
      rw [(e 0).commutes]
      rw [map_div₀, map_sub, map_ofNat]
      rw [eq_ratCast, eq_ratCast]
      apply (div_eq_iff (by norm_num : (2 : ℂ) ≠ 0)).2
      rw [htrace, ← hdiff]
      ring
    · refine ⟨(Algebra.trace ℚ K pb.gen + q) / 2, ?_⟩
      apply (e 0).injective
      change (e 0) (algebraMap ℚ K
        ((Algebra.trace ℚ K pb.gen + q) / 2)) = (e 0) pb.gen
      rw [(e 0).commutes]
      rw [map_div₀, map_add, map_ofNat]
      rw [eq_ratCast, eq_ratCast]
      apply (div_eq_iff (by norm_num : (2 : ℂ) ≠ 0)).2
      have hdiff' :
          -((e 1) pb.gen - (e 0) pb.gen) = (q : ℂ) := by
        simpa using congrArg Neg.neg hdiff
      rw [htrace, ← hdiff']
      ring
  have hdegOne : (minpoly ℚ pb.gen).natDegree = 1 :=
    minpoly.natDegree_eq_one_iff.mpr hgen
  rw [pb.natDegree_minpoly, hdim] at hdegOne
  omega

/-- A totally real quadratic number field has absolute discriminant at least
five.  Minkowski gives four; positivity and the nonsquare theorem exclude
equality. -/
theorem v15_degree_two_discriminant_ge_five
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 2) :
    (5 : ℝ) ≤ ((|NumberField.discr K| : ℤ) : ℝ) := by
  letI : NumberField.IsTotallyReal K := hreal
  have hsign : (NumberField.discr K).sign = 1 := by
    rw [NumberField.sign_discr,
      NumberField.IsTotallyReal.nrComplexPlaces_eq_zero]
    norm_num
  have hpos : 0 < NumberField.discr K :=
    Int.sign_eq_one_iff_pos.mp hsign
  have hMinkowski := NumberField.abs_discr_ge' K
  rw [hdegree, NumberField.IsTotallyReal.nrComplexPlaces_eq_zero] at hMinkowski
  norm_num at hMinkowski
  have hfour : (4 : ℤ) ≤ |NumberField.discr K| := by
    exact_mod_cast hMinkowski
  have hne : |NumberField.discr K| ≠ (4 : ℤ) := by
    intro habs
    have hdisc : NumberField.discr K = 4 := by
      simpa [abs_of_pos hpos] using habs
    apply v15_field_discr_not_isSquare_of_finrank_two K hdegree
    refine ⟨2, ?_⟩
    norm_num [hdisc]
  have hfive : (5 : ℤ) ≤ |NumberField.discr K| := by omega
  exact_mod_cast hfive

/-- The coded-number-field form used by the Section 4 input interface. -/
theorem v15_coded_degree_two_discriminant_ge_five
    (K : CodedNumberField) (hreal : NumberField.IsTotallyReal K.1)
    (hdegree : Module.finrank ℚ K.1 = 2) :
    (5 : ℝ) ≤ ((|K.discriminant| : ℤ) : ℝ) := by
  simpa only [NumberFieldCode.discriminant] using
    v15_degree_two_discriminant_ge_five K.1 hreal hdegree

end

end TraceEuclidean
