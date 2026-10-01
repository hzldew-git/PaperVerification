import TraceEuclidean.DegreeTwoDiscriminant
import TraceEuclidean.HunterNumberField

/-!
# Finite cubic discriminant reduction

For a monic cubic

`X^3 - s1 * X^2 + s2 * X - s3`,

Hunter's trace normalization gives `s1 = 0` or `s1 = 1`, while the
two-dimensional short-vector estimate gives

`0 < 2 * s1^2 - 6 * s2 < 16`.

This module proves by exact integer arithmetic that the only such polynomial
without an integer root and with positive discriminant has discriminant
`49`.  It then packages the precise remaining Hunter certificate needed to
deduce the degree-three field-discriminant bound.  No enumeration table is
used in the finite reduction.
-/

namespace TraceEuclidean

noncomputable section

/-- The squared-conjugate spread of a normalized monic cubic. -/
def cubicSpread (s1 s2 : ℤ) : ℤ :=
  2 * s1 ^ 2 - 6 * s2

/-- The discriminant of `X^3 - s1 * X^2 + s2 * X - s3`. -/
def cubicDiscriminant (s1 s2 s3 : ℤ) : ℤ :=
  s1 ^ 2 * s2 ^ 2 - 4 * s2 ^ 3 - 4 * s1 ^ 3 * s3 -
    27 * s3 ^ 2 + 18 * s1 * s2 * s3

/-- Evaluation of `X^3 - s1 * X^2 + s2 * X - s3` at an integer. -/
def cubicEval (s1 s2 s3 z : ℤ) : ℤ :=
  z ^ 3 - s1 * z ^ 2 + s2 * z - s3

/-- Positive cubic discriminant already forces positive conjugate spread.
This is the integral form of the depressed-cubic identity
`27 * discr = 4 * (s1^2 - 3*s2)^3 - q^2`. -/
theorem cubic_spread_pos_of_discriminant_pos
    (s1 s2 s3 : ℤ)
    (hdisc : 0 < cubicDiscriminant s1 s2 s3) :
    0 < cubicSpread s1 s2 := by
  let p : ℤ := s1 ^ 2 - 3 * s2
  let q : ℤ := 2 * s1 ^ 3 - 9 * s1 * s2 + 27 * s3
  have hid : 27 * cubicDiscriminant s1 s2 s3 =
      4 * p ^ 3 - q ^ 2 := by
    simp only [cubicDiscriminant, p, q]
    ring
  have hpCube : 0 < p ^ 3 := by
    nlinarith [sq_nonneg q]
  have hp : 0 < p :=
    (show Odd 3 by decide).pow_pos_iff.mp hpCube
  simp only [cubicSpread, p] at hp ⊢
  nlinarith

/-- Coefficients after replacing a root `alpha` by `alpha - k`. -/
def cubicShiftS1 (s1 k : ℤ) : ℤ :=
  s1 - 3 * k

def cubicShiftS2 (s1 s2 k : ℤ) : ℤ :=
  s2 - 2 * s1 * k + 3 * k ^ 2

def cubicShiftS3 (s1 s2 s3 k : ℤ) : ℤ :=
  s3 - s2 * k + s1 * k ^ 2 - k ^ 3

/-- Translation of a cubic root gives the displayed translated polynomial. -/
theorem cubic_shift_eval (s1 s2 s3 k z : ℤ) :
    cubicEval
        (cubicShiftS1 s1 k)
        (cubicShiftS2 s1 s2 k)
        (cubicShiftS3 s1 s2 s3 k) z =
      cubicEval s1 s2 s3 (z + k) := by
  simp only [cubicEval, cubicShiftS1, cubicShiftS2,
    cubicShiftS3]
  ring

/-- The conjugate spread is invariant under an integral translation. -/
theorem cubic_shift_spread (s1 s2 k : ℤ) :
    cubicSpread
        (cubicShiftS1 s1 k)
        (cubicShiftS2 s1 s2 k) =
      cubicSpread s1 s2 := by
  simp only [cubicSpread, cubicShiftS1, cubicShiftS2]
  ring

/-- The cubic discriminant is invariant under an integral translation. -/
theorem cubic_shift_discriminant (s1 s2 s3 k : ℤ) :
    cubicDiscriminant
        (cubicShiftS1 s1 k)
        (cubicShiftS2 s1 s2 k)
        (cubicShiftS3 s1 s2 s3 k) =
      cubicDiscriminant s1 s2 s3 := by
  simp only [cubicDiscriminant, cubicShiftS1, cubicShiftS2,
    cubicShiftS3]
  ring

/-- Replacing a root by its negative transforms the coefficients as shown. -/
theorem cubic_neg_eval (s1 s2 s3 z : ℤ) :
    cubicEval (-s1) s2 (-s3) z =
      -cubicEval s1 s2 s3 (-z) := by
  simp only [cubicEval]
  ring

theorem cubic_neg_spread (s1 s2 : ℤ) :
    cubicSpread (-s1) s2 = cubicSpread s1 s2 := by
  simp only [cubicSpread]
  ring

theorem cubic_neg_discriminant (s1 s2 s3 : ℤ) :
    cubicDiscriminant (-s1) s2 (-s3) =
      cubicDiscriminant s1 s2 s3 := by
  simp only [cubicDiscriminant]
  ring

/-- Every root-free integral monic cubic can be translated, and if necessary
negated, so that its trace coefficient is `0` or `1`.  The spread,
discriminant, and absence of an integral root are preserved. -/
theorem normalize_cubic_coefficients
    (s1 s2 s3 : ℤ)
    (hnoRoot : ∀ z : ℤ, cubicEval s1 s2 s3 z ≠ 0) :
    ∃ t1 t2 t3 : ℤ,
      (t1 = 0 ∨ t1 = 1) ∧
      cubicSpread t1 t2 = cubicSpread s1 s2 ∧
      cubicDiscriminant t1 t2 t3 =
        cubicDiscriminant s1 s2 s3 ∧
      ∀ z : ℤ, cubicEval t1 t2 t3 z ≠ 0 := by
  have hremNonneg : 0 ≤ s1 % 3 :=
    Int.emod_nonneg s1 (by norm_num)
  have hremLt : s1 % 3 < 3 :=
    Int.emod_lt_of_pos s1 (by norm_num)
  have hdecomp : s1 / 3 * 3 + s1 % 3 = s1 :=
    Int.ediv_mul_add_emod s1 3
  interval_cases hrem : s1 % 3
  · refine ⟨cubicShiftS1 s1 (s1 / 3),
      cubicShiftS2 s1 s2 (s1 / 3),
      cubicShiftS3 s1 s2 s3 (s1 / 3), ?_,
      cubic_shift_spread s1 s2 (s1 / 3),
      cubic_shift_discriminant s1 s2 s3 (s1 / 3), ?_⟩
    · left
      simp only [cubicShiftS1]
      omega
    · intro z hz
      apply hnoRoot (z + s1 / 3)
      rw [← cubic_shift_eval]
      exact hz
  · refine ⟨cubicShiftS1 s1 (s1 / 3),
      cubicShiftS2 s1 s2 (s1 / 3),
      cubicShiftS3 s1 s2 s3 (s1 / 3), ?_,
      cubic_shift_spread s1 s2 (s1 / 3),
      cubic_shift_discriminant s1 s2 s3 (s1 / 3), ?_⟩
    · right
      simp only [cubicShiftS1]
      omega
    · intro z hz
      apply hnoRoot (z + s1 / 3)
      rw [← cubic_shift_eval]
      exact hz
  · let k : ℤ := -(s1 / 3) - 1
    refine ⟨cubicShiftS1 (-s1) k,
      cubicShiftS2 (-s1) s2 k,
      cubicShiftS3 (-s1) s2 (-s3) k, ?_, ?_, ?_, ?_⟩
    · right
      simp only [cubicShiftS1, k]
      omega
    · rw [cubic_shift_spread, cubic_neg_spread]
    · rw [cubic_shift_discriminant, cubic_neg_discriminant]
    · intro z hz
      have hshift :
          cubicEval (-s1) s2 (-s3) (z + k) = 0 := by
        rw [← cubic_shift_eval]
        exact hz
      rw [cubic_neg_eval] at hshift
      exact hnoRoot (-(z + k)) (neg_eq_zero.mp hshift)

/-- The exact finite part of the totally real cubic minimum-discriminant
argument.  The normalized Hunter inequalities leave five `(s1,s2)` pairs;
positivity of the cubic discriminant and the absence of an integer root leave
only `X^3 - X^2 - 2X + 1`, whose discriminant is `49`. -/
theorem normalized_cubic_discriminant_eq_49
    (s1 s2 s3 : ℤ)
    (hs1 : s1 = 0 ∨ s1 = 1)
    (hspreadPos : 0 < cubicSpread s1 s2)
    (hspreadLt : cubicSpread s1 s2 < 16)
    (hdiscPos : 0 < cubicDiscriminant s1 s2 s3)
    (hnoRoot : ∀ z : ℤ, cubicEval s1 s2 s3 z ≠ 0) :
    cubicDiscriminant s1 s2 s3 = 49 := by
  rcases hs1 with rfl | rfl
  · have hs2lo : (-2 : ℤ) ≤ s2 := by
      simp only [cubicSpread] at hspreadLt
      omega
    have hs2hi : s2 ≤ -1 := by
      simp only [cubicSpread] at hspreadPos
      omega
    interval_cases s2
    · have hs3lo : (-1 : ℤ) ≤ s3 := by
        simp only [cubicDiscriminant] at hdiscPos
        by_contra h
        have hs3 : s3 ≤ -2 := by omega
        nlinarith [sq_nonneg (s3 + 2)]
      have hs3hi : s3 ≤ 1 := by
        simp only [cubicDiscriminant] at hdiscPos
        by_contra h
        have hs3 : 2 ≤ s3 := by omega
        nlinarith [sq_nonneg (s3 - 2)]
      interval_cases s3
      · exact ((hnoRoot 1) (by norm_num [cubicEval])).elim
      · exact ((hnoRoot 0) (by norm_num [cubicEval])).elim
      · exact ((hnoRoot (-1)) (by norm_num [cubicEval])).elim
    · have hs3lo : (0 : ℤ) ≤ s3 := by
        simp only [cubicDiscriminant] at hdiscPos
        by_contra h
        have hs3 : s3 ≤ -1 := by omega
        nlinarith [sq_nonneg (s3 + 1)]
      have hs3hi : s3 ≤ 0 := by
        simp only [cubicDiscriminant] at hdiscPos
        by_contra h
        have hs3 : 1 ≤ s3 := by omega
        nlinarith [sq_nonneg (s3 - 1)]
      interval_cases s3
      exact ((hnoRoot 0) (by norm_num [cubicEval])).elim
  · have hs2lo : (-2 : ℤ) ≤ s2 := by
      simp only [cubicSpread] at hspreadLt
      omega
    have hs2hi : s2 ≤ 0 := by
      simp only [cubicSpread] at hspreadPos
      omega
    interval_cases s2
    · have hs3lo : (-2 : ℤ) ≤ s3 := by
        simp only [cubicDiscriminant] at hdiscPos
        by_contra h
        have hs3 : s3 ≤ -3 := by omega
        nlinarith [sq_nonneg (s3 + 3)]
      have hs3hi : s3 ≤ 0 := by
        simp only [cubicDiscriminant] at hdiscPos
        by_contra h
        have hs3 : 1 ≤ s3 := by omega
        nlinarith [sq_nonneg (s3 - 1)]
      interval_cases s3
      · exact ((hnoRoot 1) (by norm_num [cubicEval])).elim
      · norm_num [cubicDiscriminant]
      · exact ((hnoRoot 0) (by norm_num [cubicEval])).elim
    · have hs3lo : (0 : ℤ) ≤ s3 := by
        simp only [cubicDiscriminant] at hdiscPos
        by_contra h
        have hs3 : s3 ≤ -1 := by omega
        nlinarith [sq_nonneg (s3 + 1)]
      have hs3hi : s3 ≤ 0 := by
        simp only [cubicDiscriminant] at hdiscPos
        by_contra h
        have hs3 : 1 ≤ s3 := by omega
        nlinarith [sq_nonneg (s3 - 1)]
      interval_cases s3
      exact ((hnoRoot 0) (by norm_num [cubicEval])).elim
    · simp only [cubicDiscriminant] at hdiscPos
      nlinarith [sq_nonneg s3]

/-- A concrete Hunter certificate for a totally real cubic field whose
absolute discriminant is assumed to be smaller than `49`.  The certificate
does not assume a normalized trace: integral translation and negation are
handled internally by `normalize_cubic_coefficients`.  The remaining
field-specific task is to construct the coefficients and finite index under
the contradiction hypothesis. -/
def DegreeThreeHunterCertificateInput : Prop :=
  ∀ (K : CodedNumberField), NumberField.IsTotallyReal K.1 →
    Module.finrank ℚ K.1 = 3 →
      |K.discriminant| < 49 →
      ∃ s1 s2 s3 : ℤ, ∃ index : ℕ,
        cubicSpread s1 s2 < 16 ∧
        (∀ z : ℤ, cubicEval s1 s2 s3 z ≠ 0) ∧
        0 < index ∧
        cubicDiscriminant s1 s2 s3 =
          (index : ℤ) ^ 2 * K.discriminant

/-- The Hunter certificate implies the exact totally real cubic lower bound
`|D_K| >= 49`. -/
theorem coded_degree_three_discriminant_ge_49_of_hunterCertificate
    (hHunter : DegreeThreeHunterCertificateInput)
    (K : CodedNumberField) (hreal : NumberField.IsTotallyReal K.1)
    (hdegree : Module.finrank ℚ K.1 = 3) :
    (49 : ℝ) ≤ ((|K.discriminant| : ℤ) : ℝ) := by
  have hfieldInt : (49 : ℤ) ≤ |K.discriminant| := by
    by_contra hnot
    have hlt : |K.discriminant| < 49 := by omega
    rcases hHunter K hreal hdegree hlt with
      ⟨s1, s2, s3, index, hspreadLt, hnoRoot,
        hindex, hdisc⟩
    rcases normalize_cubic_coefficients s1 s2 s3 hnoRoot with
      ⟨t1, t2, t3, ht1, hspread, hdiscNorm, hnoRootNorm⟩
    have hspreadLtNorm : cubicSpread t1 t2 < 16 := by
      rw [hspread]
      exact hspreadLt
    have hdiscRel : cubicDiscriminant t1 t2 t3 =
        (index : ℤ) ^ 2 * K.discriminant := by
      rw [hdiscNorm, hdisc]
    letI : NumberField.IsTotallyReal K.1 := hreal
    have hsign : K.discriminant.sign = 1 := by
      rw [NumberFieldCode.discriminant, NumberField.sign_discr,
        NumberField.IsTotallyReal.nrComplexPlaces_eq_zero]
      norm_num
    have hfieldPos : 0 < K.discriminant :=
      Int.sign_eq_one_iff_pos.mp hsign
    have hdiscPos : 0 < cubicDiscriminant t1 t2 t3 := by
      rw [hdiscRel]
      positivity
    have hspreadPosNorm : 0 < cubicSpread t1 t2 :=
      cubic_spread_pos_of_discriminant_pos t1 t2 t3 hdiscPos
    have hpoly := normalized_cubic_discriminant_eq_49
      t1 t2 t3 ht1 hspreadPosNorm hspreadLtNorm hdiscPos hnoRootNorm
    rw [hpoly] at hdiscRel
    have hindexSq : (index : ℤ) ^ 2 ≤ 49 := by
      nlinarith
    have hindexLe : index ≤ 7 := by
      exact_mod_cast (sq_le_sq₀
        (by positivity : (0 : ℤ) ≤ (index : ℤ))
        (by norm_num : (0 : ℤ) ≤ 7)).mp
          (by norm_num at hindexSq ⊢; exact hindexSq)
    have hfieldGtTwo : (2 : ℤ) < |K.discriminant| := by
      simpa [NumberFieldCode.discriminant] using
        (NumberField.abs_discr_gt_two (K := K.1) (by omega))
    have habs : |K.discriminant| = K.discriminant :=
      abs_of_pos hfieldPos
    rw [habs] at hfieldGtTwo
    have hindexOne : index = 1 := by
      interval_cases index <;>
        norm_num at hindex hdiscRel hfieldGtTwo ⊢ <;> omega
    rw [hindexOne] at hdiscRel
    norm_num at hdiscRel
    rw [abs_of_pos hfieldPos, ← hdiscRel] at hlt
    omega
  exact_mod_cast hfieldInt

end

end TraceEuclidean
