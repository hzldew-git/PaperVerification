import TraceEuclidean.V15DegreeThreeDiscriminant

/-!
# Finite quartic discriminant reduction

For a monic quartic

`X^4 - s1 * X^3 + s2 * X^2 - s3 * X + s4`,

the normalized Hunter inequalities, positivity of the first three Hermite
minors, and irreducibility leave only two translated defining polynomials.
Both have discriminant `725`.  This file checks that finite arithmetic inside
Lean and isolates the remaining degree-four Hunter certificate.
-/

namespace TraceEuclidean

noncomputable section

/-- The second power sum of the roots of the normalized quartic. -/
def v15QuarticSecondPowerSum (s1 s2 : ℤ) : ℤ :=
  s1 ^ 2 - 2 * s2

/-- Four times the squared norm after centering the four conjugates. -/
def v15QuarticSpread (s1 s2 : ℤ) : ℤ :=
  4 * v15QuarticSecondPowerSum s1 s2 - s1 ^ 2

/-- The third leading principal minor of the quartic Hermite matrix. -/
def v15QuarticHermiteMinorThree (s1 s2 s3 s4 : ℤ) : ℤ :=
  -2 * (3 * s1 ^ 3 * s3 - s1 ^ 2 * s2 ^ 2 +
    6 * s1 ^ 2 * s4 - 14 * s1 * s2 * s3 + 4 * s2 ^ 3 -
    16 * s2 * s4 + 18 * s3 ^ 2)

/-- The discriminant of `X^4 - s1*X^3 + s2*X^2 - s3*X + s4`. -/
def v15QuarticDiscriminant (s1 s2 s3 s4 : ℤ) : ℤ :=
  -27 * s1 ^ 4 * s4 ^ 2 + 18 * s1 ^ 3 * s2 * s3 * s4 -
    4 * s1 ^ 3 * s3 ^ 3 - 4 * s1 ^ 2 * s2 ^ 3 * s4 +
    s1 ^ 2 * s2 ^ 2 * s3 ^ 2 + 144 * s1 ^ 2 * s2 * s4 ^ 2 -
    6 * s1 ^ 2 * s3 ^ 2 * s4 - 80 * s1 * s2 ^ 2 * s3 * s4 +
    18 * s1 * s2 * s3 ^ 3 - 192 * s1 * s3 * s4 ^ 2 +
    16 * s2 ^ 4 * s4 - 4 * s2 ^ 3 * s3 ^ 2 -
    128 * s2 ^ 2 * s4 ^ 2 + 144 * s2 * s3 ^ 2 * s4 -
    27 * s3 ^ 4 + 256 * s4 ^ 3

/-- Evaluation of the normalized monic quartic at an integer. -/
def v15QuarticEval (s1 s2 s3 s4 z : ℤ) : ℤ :=
  z ^ 4 - s1 * z ^ 3 + s2 * z ^ 2 - s3 * z + s4

/-- Coefficients after replacing a quartic root `alpha` by `alpha - k`. -/
def v15QuarticShiftS1 (s1 k : ℤ) : ℤ :=
  s1 - 4 * k

def v15QuarticShiftS2 (s1 s2 k : ℤ) : ℤ :=
  s2 - 3 * s1 * k + 6 * k ^ 2

def v15QuarticShiftS3 (s1 s2 s3 k : ℤ) : ℤ :=
  s3 - 2 * s2 * k + 3 * s1 * k ^ 2 - 4 * k ^ 3

def v15QuarticShiftS4 (s1 s2 s3 s4 k : ℤ) : ℤ :=
  s4 - s3 * k + s2 * k ^ 2 - s1 * k ^ 3 + k ^ 4

/-- Translation of a quartic root gives the displayed translated
polynomial. -/
theorem v15_quartic_shift_eval (s1 s2 s3 s4 k z : ℤ) :
    v15QuarticEval
        (v15QuarticShiftS1 s1 k)
        (v15QuarticShiftS2 s1 s2 k)
        (v15QuarticShiftS3 s1 s2 s3 k)
        (v15QuarticShiftS4 s1 s2 s3 s4 k) z =
      v15QuarticEval s1 s2 s3 s4 (z + k) := by
  simp only [v15QuarticEval, v15QuarticShiftS1,
    v15QuarticShiftS2, v15QuarticShiftS3, v15QuarticShiftS4]
  ring

/-- The centered quartic spread is invariant under integral translation. -/
theorem v15_quartic_shift_spread (s1 s2 k : ℤ) :
    v15QuarticSpread
        (v15QuarticShiftS1 s1 k)
        (v15QuarticShiftS2 s1 s2 k) =
      v15QuarticSpread s1 s2 := by
  simp only [v15QuarticSpread, v15QuarticSecondPowerSum,
    v15QuarticShiftS1, v15QuarticShiftS2]
  ring

/-- The third Hermite minor is invariant under translating all roots. -/
theorem v15_quartic_shift_hermiteMinorThree
    (s1 s2 s3 s4 k : ℤ) :
    v15QuarticHermiteMinorThree
        (v15QuarticShiftS1 s1 k)
        (v15QuarticShiftS2 s1 s2 k)
        (v15QuarticShiftS3 s1 s2 s3 k)
        (v15QuarticShiftS4 s1 s2 s3 s4 k) =
      v15QuarticHermiteMinorThree s1 s2 s3 s4 := by
  simp only [v15QuarticHermiteMinorThree, v15QuarticShiftS1,
    v15QuarticShiftS2, v15QuarticShiftS3, v15QuarticShiftS4]
  ring

/-- The quartic discriminant is invariant under integral translation. -/
theorem v15_quartic_shift_discriminant (s1 s2 s3 s4 k : ℤ) :
    v15QuarticDiscriminant
        (v15QuarticShiftS1 s1 k)
        (v15QuarticShiftS2 s1 s2 k)
        (v15QuarticShiftS3 s1 s2 s3 k)
        (v15QuarticShiftS4 s1 s2 s3 s4 k) =
      v15QuarticDiscriminant s1 s2 s3 s4 := by
  simp only [v15QuarticDiscriminant, v15QuarticShiftS1,
    v15QuarticShiftS2, v15QuarticShiftS3, v15QuarticShiftS4]
  ring

/-- Replacing every quartic root by its negative transforms the coefficients
as shown. -/
theorem v15_quartic_neg_eval (s1 s2 s3 s4 z : ℤ) :
    v15QuarticEval (-s1) s2 (-s3) s4 z =
      v15QuarticEval s1 s2 s3 s4 (-z) := by
  simp only [v15QuarticEval]
  ring

theorem v15_quartic_neg_spread (s1 s2 : ℤ) :
    v15QuarticSpread (-s1) s2 = v15QuarticSpread s1 s2 := by
  simp only [v15QuarticSpread, v15QuarticSecondPowerSum]
  ring

theorem v15_quartic_neg_hermiteMinorThree (s1 s2 s3 s4 : ℤ) :
    v15QuarticHermiteMinorThree (-s1) s2 (-s3) s4 =
      v15QuarticHermiteMinorThree s1 s2 s3 s4 := by
  simp only [v15QuarticHermiteMinorThree]
  ring

theorem v15_quartic_neg_discriminant (s1 s2 s3 s4 : ℤ) :
    v15QuarticDiscriminant (-s1) s2 (-s3) s4 =
      v15QuarticDiscriminant s1 s2 s3 s4 := by
  simp only [v15QuarticDiscriminant]
  ring

/-- Coefficient equalities witnessing a factorization into two monic
quadratics. -/
def V15QuarticQuadraticFactorWitness
    (s1 s2 s3 s4 u v p q : ℤ) : Prop :=
  u + p = -s1 ∧
  v + q + u * p = s2 ∧
  u * q + v * p = -s3 ∧
  v * q = s4

/-- A monic quadratic factorization of a translated quartic pulls back to a
monic quadratic factorization of the original quartic. -/
theorem v15_quartic_factorWitness_of_shifted
    (s1 s2 s3 s4 k u v p q : ℤ)
    (hfactor : V15QuarticQuadraticFactorWitness
      (v15QuarticShiftS1 s1 k)
      (v15QuarticShiftS2 s1 s2 k)
      (v15QuarticShiftS3 s1 s2 s3 k)
      (v15QuarticShiftS4 s1 s2 s3 s4 k) u v p q) :
    V15QuarticQuadraticFactorWitness s1 s2 s3 s4
      (u - 2 * k) (v - u * k + k ^ 2)
      (p - 2 * k) (q - p * k + k ^ 2) := by
  unfold V15QuarticQuadraticFactorWitness at hfactor ⊢
  simp only [v15QuarticShiftS1, v15QuarticShiftS2,
    v15QuarticShiftS3, v15QuarticShiftS4] at hfactor
  rcases hfactor with ⟨h1, h2, h3, h4⟩
  constructor
  · linear_combination h1
  constructor
  · linear_combination h2 - 3 * k * h1
  constructor
  · linear_combination h3 - 2 * k * h2 + 3 * k ^ 2 * h1
  · linear_combination h4 - k * h3 + k ^ 2 * h2 - k ^ 3 * h1

/-- A monic quadratic factorization after negating every root gives one for
the original quartic. -/
theorem v15_quartic_factorWitness_of_negated
    (s1 s2 s3 s4 u v p q : ℤ)
    (hfactor : V15QuarticQuadraticFactorWitness
      (-s1) s2 (-s3) s4 u v p q) :
    V15QuarticQuadraticFactorWitness s1 s2 s3 s4
      (-u) v (-p) q := by
  unfold V15QuarticQuadraticFactorWitness at hfactor ⊢
  rcases hfactor with ⟨h1, h2, h3, h4⟩
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- Every root-free integral monic quartic can be translated, and if
necessary negated, so that its trace coefficient is `0`, `1`, or `2`.
The spread, Hermite minor, discriminant, and irreducibility tests used by the
finite search are preserved. -/
theorem v15_normalize_quartic_coefficients
    (s1 s2 s3 s4 : ℤ)
    (hnoRoot : ∀ z : ℤ, v15QuarticEval s1 s2 s3 s4 z ≠ 0)
    (hnoQuadratic : ∀ u v p q : ℤ,
      ¬V15QuarticQuadraticFactorWitness s1 s2 s3 s4 u v p q) :
    ∃ t1 t2 t3 t4 : ℤ,
      (t1 = 0 ∨ t1 = 1 ∨ t1 = 2) ∧
      v15QuarticSpread t1 t2 = v15QuarticSpread s1 s2 ∧
      v15QuarticHermiteMinorThree t1 t2 t3 t4 =
        v15QuarticHermiteMinorThree s1 s2 s3 s4 ∧
      v15QuarticDiscriminant t1 t2 t3 t4 =
        v15QuarticDiscriminant s1 s2 s3 s4 ∧
      (∀ z : ℤ, v15QuarticEval t1 t2 t3 t4 z ≠ 0) ∧
      ∀ u v p q : ℤ,
        ¬V15QuarticQuadraticFactorWitness t1 t2 t3 t4 u v p q := by
  have hremNonneg : 0 ≤ s1 % 4 :=
    Int.emod_nonneg s1 (by norm_num)
  have hremLt : s1 % 4 < 4 :=
    Int.emod_lt_of_pos s1 (by norm_num)
  have hdecomp : s1 / 4 * 4 + s1 % 4 = s1 :=
    Int.ediv_mul_add_emod s1 4
  interval_cases hrem : s1 % 4
  all_goals first
    | · refine ⟨v15QuarticShiftS1 s1 (s1 / 4),
          v15QuarticShiftS2 s1 s2 (s1 / 4),
          v15QuarticShiftS3 s1 s2 s3 (s1 / 4),
          v15QuarticShiftS4 s1 s2 s3 s4 (s1 / 4), ?_,
          v15_quartic_shift_spread s1 s2 (s1 / 4),
          v15_quartic_shift_hermiteMinorThree s1 s2 s3 s4 (s1 / 4),
          v15_quartic_shift_discriminant s1 s2 s3 s4 (s1 / 4), ?_, ?_⟩
        · simp only [v15QuarticShiftS1]
          omega
        · intro z hz
          apply hnoRoot (z + s1 / 4)
          rw [← v15_quartic_shift_eval]
          exact hz
        · intro u v p q hfactor
          exact hnoQuadratic
            (u - 2 * (s1 / 4)) (v - u * (s1 / 4) + (s1 / 4) ^ 2)
            (p - 2 * (s1 / 4)) (q - p * (s1 / 4) + (s1 / 4) ^ 2)
            (v15_quartic_factorWitness_of_shifted
              s1 s2 s3 s4 (s1 / 4) u v p q hfactor)
    | · let k : ℤ := -(s1 / 4) - 1
        refine ⟨v15QuarticShiftS1 (-s1) k,
          v15QuarticShiftS2 (-s1) s2 k,
          v15QuarticShiftS3 (-s1) s2 (-s3) k,
          v15QuarticShiftS4 (-s1) s2 (-s3) s4 k,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
        · right
          left
          simp only [v15QuarticShiftS1, k]
          omega
        · rw [v15_quartic_shift_spread, v15_quartic_neg_spread]
        · rw [v15_quartic_shift_hermiteMinorThree,
            v15_quartic_neg_hermiteMinorThree]
        · rw [v15_quartic_shift_discriminant,
            v15_quartic_neg_discriminant]
        · intro z hz
          have hshift :
              v15QuarticEval (-s1) s2 (-s3) s4 (z + k) = 0 := by
            rw [← v15_quartic_shift_eval]
            exact hz
          rw [v15_quartic_neg_eval] at hshift
          exact hnoRoot (-(z + k)) hshift
        · intro u v p q hfactor
          have hneg := v15_quartic_factorWitness_of_shifted
            (-s1) s2 (-s3) s4 k u v p q hfactor
          exact hnoQuadratic
            (-(u - 2 * k)) (v - u * k + k ^ 2)
            (-(p - 2 * k)) (q - p * k + k ^ 2)
            (v15_quartic_factorWitness_of_negated
              s1 s2 s3 s4
              (u - 2 * k) (v - u * k + k ^ 2)
              (p - 2 * k) (q - p * k + k ^ 2) hneg)

/-- The spread inequalities force a small second coefficient once the trace
coefficient is normalized. -/
theorem v15_quartic_s2_bounds_of_normalized
    (s1 s2 : ℤ) (hs1 : s1 = 0 ∨ s1 = 1 ∨ s1 = 2)
    (hspreadPos : 0 < v15QuarticSpread s1 s2)
    (hspreadLt : v15QuarticSpread s1 s2 < 29) :
    -4 ≤ s2 ∧ s2 ≤ 2 := by
  rcases hs1 with rfl | rfl | rfl <;>
    simp only [v15QuarticSpread, v15QuarticSecondPowerSum] at hspreadPos hspreadLt
  all_goals omega

private instance (s1 s2 s3 s4 u v p q : ℤ) :
    Decidable (V15QuarticQuadraticFactorWitness s1 s2 s3 s4 u v p q) := by
  unfold V15QuarticQuadraticFactorWitness
  infer_instance

private def v15QuarticS1Range : List ℤ := [0, 1, 2]

private def v15QuarticS2Range : List ℤ :=
  (List.range 7).map (fun n ↦ (n : ℤ) - 4)

private def v15QuarticS3Range : List ℤ :=
  (List.range 49).map (fun n ↦ (n : ℤ) - 24)

private def v15QuarticS4Range : List ℤ :=
  (List.range 9).map (fun n ↦ (n : ℤ) - 4)

private def v15QuarticSmallRange : List ℤ :=
  (List.range 7).map (fun n ↦ (n : ℤ) - 3)

private def v15QuarticRootSearch (s1 s2 s3 s4 : ℤ) : Bool :=
  v15QuarticSmallRange.any fun z ↦
    decide (v15QuarticEval s1 s2 s3 s4 z = 0)

private def v15QuarticFactorSearch (s1 s2 s3 s4 : ℤ) : Bool :=
  v15QuarticSmallRange.any fun u ↦
    v15QuarticSmallRange.any fun v ↦
      v15QuarticSmallRange.any fun p ↦
        v15QuarticSmallRange.any fun q ↦
          decide (V15QuarticQuadraticFactorWitness
            s1 s2 s3 s4 u v p q)

private def v15QuarticAdmissible (s1 s2 s3 s4 : ℤ) : Bool :=
  decide (0 < v15QuarticSpread s1 s2 ∧
    v15QuarticSpread s1 s2 < 29 ∧
    0 < v15QuarticHermiteMinorThree s1 s2 s3 s4 ∧
    0 < v15QuarticDiscriminant s1 s2 s3 s4)

private def v15QuarticOutcome (s1 s2 s3 s4 : ℤ) : Bool :=
  decide (v15QuarticDiscriminant s1 s2 s3 s4 = 725) ||
    v15QuarticRootSearch s1 s2 s3 s4 ||
    v15QuarticFactorSearch s1 s2 s3 s4

/-- The complete finite check behind the quartic arithmetic reduction. -/
private def v15QuarticFiniteCheck : Bool :=
  v15QuarticS1Range.all fun s1 ↦
    v15QuarticS2Range.all fun s2 ↦
      v15QuarticS3Range.all fun s3 ↦
        v15QuarticS4Range.all fun s4 ↦
          !v15QuarticAdmissible s1 s2 s3 s4 ||
            v15QuarticOutcome s1 s2 s3 s4

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every point in the finite quartic coefficient box.
private theorem v15_quarticFiniteCheck_true :
    v15QuarticFiniteCheck = true := by
  decide

/-- Under the normalized Hunter and Hermite inequalities, an irreducible
quartic in the coefficient box has discriminant exactly `725`. -/
theorem v15_normalized_quartic_discriminant_eq_725
    (s1 s2 s3 s4 : ℤ)
    (hs1 : 0 ≤ s1) (hs1' : s1 ≤ 2)
    (hs2 : -4 ≤ s2) (hs2' : s2 ≤ 2)
    (hs3 : -24 ≤ s3) (hs3' : s3 ≤ 24)
    (hs4 : -4 ≤ s4) (hs4' : s4 ≤ 4)
    (hspreadPos : 0 < v15QuarticSpread s1 s2)
    (hspreadLt : v15QuarticSpread s1 s2 < 29)
    (hminor : 0 < v15QuarticHermiteMinorThree s1 s2 s3 s4)
    (hdisc : 0 < v15QuarticDiscriminant s1 s2 s3 s4)
    (hnoRoot : ∀ z : ℤ, v15QuarticEval s1 s2 s3 s4 z ≠ 0)
    (hnoQuadratic : ∀ u v p q : ℤ,
      ¬V15QuarticQuadraticFactorWitness s1 s2 s3 s4 u v p q) :
    v15QuarticDiscriminant s1 s2 s3 s4 = 725 := by
  have hs1mem : s1 ∈ v15QuarticS1Range := by
    interval_cases s1 <;> decide
  have hs2mem : s2 ∈ v15QuarticS2Range := by
    interval_cases s2 <;> decide
  have hs3mem : s3 ∈ v15QuarticS3Range := by
    interval_cases s3 <;> decide
  have hs4mem : s4 ∈ v15QuarticS4Range := by
    interval_cases s4 <;> decide
  have hall1 := List.all_eq_true.mp v15_quarticFiniteCheck_true
  have hall2 := List.all_eq_true.mp (hall1 s1 hs1mem)
  have hall3 := List.all_eq_true.mp (hall2 s2 hs2mem)
  have hall4 := List.all_eq_true.mp (hall3 s3 hs3mem)
  have hrow := hall4 s4 hs4mem
  have hadmissible : v15QuarticAdmissible s1 s2 s3 s4 = true := by
    simp [v15QuarticAdmissible, hspreadPos, hspreadLt, hminor, hdisc]
  have houtcome : v15QuarticOutcome s1 s2 s3 s4 = true := by
    simpa [hadmissible] using hrow
  simp only [v15QuarticOutcome, Bool.or_eq_true, decide_eq_true_eq] at houtcome
  rcases houtcome with (hdisc725 | hroot) | hfactor
  · exact hdisc725
  · change v15QuarticSmallRange.any (fun z ↦
      decide (v15QuarticEval s1 s2 s3 s4 z = 0)) = true at hroot
    obtain ⟨z, -, hz⟩ := List.any_eq_true.mp hroot
    exact ((hnoRoot z) (of_decide_eq_true hz)).elim
  · change v15QuarticSmallRange.any (fun u ↦
      v15QuarticSmallRange.any fun v ↦
        v15QuarticSmallRange.any fun p ↦
          v15QuarticSmallRange.any fun q ↦
            decide (V15QuarticQuadraticFactorWitness
              s1 s2 s3 s4 u v p q)) = true at hfactor
    obtain ⟨u, -, hu⟩ := List.any_eq_true.mp hfactor
    obtain ⟨v, -, hv⟩ := List.any_eq_true.mp hu
    obtain ⟨p, -, hp⟩ := List.any_eq_true.mp hv
    obtain ⟨q, -, hq⟩ := List.any_eq_true.mp hp
    exact ((hnoQuadratic u v p q) (of_decide_eq_true hq)).elim

/-- The concrete normalized certificate needed below the hypothetical
degree-four discriminant bound.  The finite arithmetic of the certificate is
fully checked above. The field-theoretic reduction constructs its positivity,
irreducibility, and index fields from a primitive Hunter generator. -/
def V15DegreeFourHunterCertificateInput : Prop :=
  ∀ (K : CodedNumberField), NumberField.IsTotallyReal K.1 →
    Module.finrank ℚ K.1 = 4 →
      |K.discriminant| < 725 →
      ∃ s1 s2 s3 s4 : ℤ, ∃ index : ℕ,
        (s1 = 0 ∨ s1 = 1 ∨ s1 = 2) ∧
        -24 ≤ s3 ∧ s3 ≤ 24 ∧
        -4 ≤ s4 ∧ s4 ≤ 4 ∧
        0 < v15QuarticSpread s1 s2 ∧
        v15QuarticSpread s1 s2 < 29 ∧
        0 < v15QuarticHermiteMinorThree s1 s2 s3 s4 ∧
        0 < v15QuarticDiscriminant s1 s2 s3 s4 ∧
        (∀ z : ℤ, v15QuarticEval s1 s2 s3 s4 z ≠ 0) ∧
        (∀ u v p q : ℤ,
          ¬V15QuarticQuadraticFactorWitness s1 s2 s3 s4 u v p q) ∧
        0 < index ∧
        v15QuarticDiscriminant s1 s2 s3 s4 =
          (index : ℤ) ^ 2 * K.discriminant

/-- The normalized quartic Hunter certificate implies the exact lower bound
`|D_K| >= 725`. -/
theorem v15_coded_degree_four_discriminant_ge_725_of_hunterCertificate
    (hHunter : V15DegreeFourHunterCertificateInput)
    (K : CodedNumberField) (hreal : NumberField.IsTotallyReal K.1)
    (hdegree : Module.finrank ℚ K.1 = 4) :
    (725 : ℝ) ≤ ((|K.discriminant| : ℤ) : ℝ) := by
  have hfieldInt : (725 : ℤ) ≤ |K.discriminant| := by
    by_contra hnot
    have hlt : |K.discriminant| < 725 := by omega
    rcases hHunter K hreal hdegree hlt with
      ⟨s1, s2, s3, s4, index,
        hs1, hs3, hs3', hs4, hs4',
        hspreadPos, hspreadLt, hminor, hdiscPos,
        hnoRoot, hnoQuadratic, hindex, hrelation⟩
    have hs1Bounds : 0 ≤ s1 ∧ s1 ≤ 2 := by omega
    have hs2Bounds := v15_quartic_s2_bounds_of_normalized
      s1 s2 hs1 hspreadPos hspreadLt
    have hpoly := v15_normalized_quartic_discriminant_eq_725
      s1 s2 s3 s4 hs1Bounds.1 hs1Bounds.2
      hs2Bounds.1 hs2Bounds.2 hs3 hs3' hs4 hs4'
      hspreadPos hspreadLt hminor hdiscPos hnoRoot hnoQuadratic
    rw [hpoly] at hrelation
    letI : NumberField.IsTotallyReal K.1 := hreal
    have hsign : K.discriminant.sign = 1 := by
      rw [NumberFieldCode.discriminant, NumberField.sign_discr,
        NumberField.IsTotallyReal.nrComplexPlaces_eq_zero]
      norm_num
    have hfieldPos : 0 < K.discriminant :=
      Int.sign_eq_one_iff_pos.mp hsign
    have hminkowski : (1024 / 9 : ℝ) ≤
        ((|K.discriminant| : ℤ) : ℝ) := by
      have h := NumberField.abs_discr_ge' K.1
      rw [hdegree, NumberField.IsTotallyReal.nrComplexPlaces_eq_zero] at h
      norm_num [NumberFieldCode.discriminant, Int.cast_abs] at h ⊢
      exact h
    have hfieldGt : (29 : ℤ) < K.discriminant := by
      have hcast : (29 : ℝ) < ((|K.discriminant| : ℤ) : ℝ) := by
        linarith
      rw [abs_of_pos hfieldPos] at hcast
      exact_mod_cast hcast
    have hindexLt : index < 5 := by
      by_contra hnotIndex
      have hindexFive : 5 ≤ (index : ℤ) := by exact_mod_cast (by omega : 5 ≤ index)
      have hfieldThirty : (30 : ℤ) ≤ K.discriminant := by omega
      have hsquare : (25 : ℤ) ≤ (index : ℤ) ^ 2 := by nlinarith
      nlinarith
    interval_cases index
    · norm_num at hrelation
      rw [abs_of_pos hfieldPos, ← hrelation] at hlt
      omega
    all_goals norm_num at hrelation
    all_goals omega
  exact_mod_cast hfieldInt

end

end TraceEuclidean
