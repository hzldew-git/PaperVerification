import TraceEuclidean.DegreeThreeDiscriminant

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
def quarticSecondPowerSum (s1 s2 : ℤ) : ℤ :=
  s1 ^ 2 - 2 * s2

/-- Four times the squared norm after centering the four conjugates. -/
def quarticSpread (s1 s2 : ℤ) : ℤ :=
  4 * quarticSecondPowerSum s1 s2 - s1 ^ 2

/-- The third leading principal minor of the quartic Hermite matrix. -/
def quarticHermiteMinorThree (s1 s2 s3 s4 : ℤ) : ℤ :=
  -2 * (3 * s1 ^ 3 * s3 - s1 ^ 2 * s2 ^ 2 +
    6 * s1 ^ 2 * s4 - 14 * s1 * s2 * s3 + 4 * s2 ^ 3 -
    16 * s2 * s4 + 18 * s3 ^ 2)

/-- The discriminant of `X^4 - s1*X^3 + s2*X^2 - s3*X + s4`. -/
def quarticDiscriminant (s1 s2 s3 s4 : ℤ) : ℤ :=
  -27 * s1 ^ 4 * s4 ^ 2 + 18 * s1 ^ 3 * s2 * s3 * s4 -
    4 * s1 ^ 3 * s3 ^ 3 - 4 * s1 ^ 2 * s2 ^ 3 * s4 +
    s1 ^ 2 * s2 ^ 2 * s3 ^ 2 + 144 * s1 ^ 2 * s2 * s4 ^ 2 -
    6 * s1 ^ 2 * s3 ^ 2 * s4 - 80 * s1 * s2 ^ 2 * s3 * s4 +
    18 * s1 * s2 * s3 ^ 3 - 192 * s1 * s3 * s4 ^ 2 +
    16 * s2 ^ 4 * s4 - 4 * s2 ^ 3 * s3 ^ 2 -
    128 * s2 ^ 2 * s4 ^ 2 + 144 * s2 * s3 ^ 2 * s4 -
    27 * s3 ^ 4 + 256 * s4 ^ 3

/-- Evaluation of the normalized monic quartic at an integer. -/
def quarticEval (s1 s2 s3 s4 z : ℤ) : ℤ :=
  z ^ 4 - s1 * z ^ 3 + s2 * z ^ 2 - s3 * z + s4

/-- Coefficients after replacing a quartic root `alpha` by `alpha - k`. -/
def quarticShiftS1 (s1 k : ℤ) : ℤ :=
  s1 - 4 * k

def quarticShiftS2 (s1 s2 k : ℤ) : ℤ :=
  s2 - 3 * s1 * k + 6 * k ^ 2

def quarticShiftS3 (s1 s2 s3 k : ℤ) : ℤ :=
  s3 - 2 * s2 * k + 3 * s1 * k ^ 2 - 4 * k ^ 3

def quarticShiftS4 (s1 s2 s3 s4 k : ℤ) : ℤ :=
  s4 - s3 * k + s2 * k ^ 2 - s1 * k ^ 3 + k ^ 4

/-- Translation of a quartic root gives the displayed translated
polynomial. -/
theorem quartic_shift_eval (s1 s2 s3 s4 k z : ℤ) :
    quarticEval
        (quarticShiftS1 s1 k)
        (quarticShiftS2 s1 s2 k)
        (quarticShiftS3 s1 s2 s3 k)
        (quarticShiftS4 s1 s2 s3 s4 k) z =
      quarticEval s1 s2 s3 s4 (z + k) := by
  simp only [quarticEval, quarticShiftS1,
    quarticShiftS2, quarticShiftS3, quarticShiftS4]
  ring

/-- The centered quartic spread is invariant under integral translation. -/
theorem quartic_shift_spread (s1 s2 k : ℤ) :
    quarticSpread
        (quarticShiftS1 s1 k)
        (quarticShiftS2 s1 s2 k) =
      quarticSpread s1 s2 := by
  simp only [quarticSpread, quarticSecondPowerSum,
    quarticShiftS1, quarticShiftS2]
  ring

/-- The third Hermite minor is invariant under translating all roots. -/
theorem quartic_shift_hermiteMinorThree
    (s1 s2 s3 s4 k : ℤ) :
    quarticHermiteMinorThree
        (quarticShiftS1 s1 k)
        (quarticShiftS2 s1 s2 k)
        (quarticShiftS3 s1 s2 s3 k)
        (quarticShiftS4 s1 s2 s3 s4 k) =
      quarticHermiteMinorThree s1 s2 s3 s4 := by
  simp only [quarticHermiteMinorThree, quarticShiftS1,
    quarticShiftS2, quarticShiftS3, quarticShiftS4]
  ring

/-- The quartic discriminant is invariant under integral translation. -/
theorem quartic_shift_discriminant (s1 s2 s3 s4 k : ℤ) :
    quarticDiscriminant
        (quarticShiftS1 s1 k)
        (quarticShiftS2 s1 s2 k)
        (quarticShiftS3 s1 s2 s3 k)
        (quarticShiftS4 s1 s2 s3 s4 k) =
      quarticDiscriminant s1 s2 s3 s4 := by
  simp only [quarticDiscriminant, quarticShiftS1,
    quarticShiftS2, quarticShiftS3, quarticShiftS4]
  ring

/-- Replacing every quartic root by its negative transforms the coefficients
as shown. -/
theorem quartic_neg_eval (s1 s2 s3 s4 z : ℤ) :
    quarticEval (-s1) s2 (-s3) s4 z =
      quarticEval s1 s2 s3 s4 (-z) := by
  simp only [quarticEval]
  ring

theorem quartic_neg_spread (s1 s2 : ℤ) :
    quarticSpread (-s1) s2 = quarticSpread s1 s2 := by
  simp only [quarticSpread, quarticSecondPowerSum]
  ring

theorem quartic_neg_hermiteMinorThree (s1 s2 s3 s4 : ℤ) :
    quarticHermiteMinorThree (-s1) s2 (-s3) s4 =
      quarticHermiteMinorThree s1 s2 s3 s4 := by
  simp only [quarticHermiteMinorThree]
  ring

theorem quartic_neg_discriminant (s1 s2 s3 s4 : ℤ) :
    quarticDiscriminant (-s1) s2 (-s3) s4 =
      quarticDiscriminant s1 s2 s3 s4 := by
  simp only [quarticDiscriminant]
  ring

/-- Coefficient equalities witnessing a factorization into two monic
quadratics. -/
def QuarticQuadraticFactorWitness
    (s1 s2 s3 s4 u v p q : ℤ) : Prop :=
  u + p = -s1 ∧
  v + q + u * p = s2 ∧
  u * q + v * p = -s3 ∧
  v * q = s4

/-- A monic quadratic factorization of a translated quartic pulls back to a
monic quadratic factorization of the original quartic. -/
theorem quartic_factorWitness_of_shifted
    (s1 s2 s3 s4 k u v p q : ℤ)
    (hfactor : QuarticQuadraticFactorWitness
      (quarticShiftS1 s1 k)
      (quarticShiftS2 s1 s2 k)
      (quarticShiftS3 s1 s2 s3 k)
      (quarticShiftS4 s1 s2 s3 s4 k) u v p q) :
    QuarticQuadraticFactorWitness s1 s2 s3 s4
      (u - 2 * k) (v - u * k + k ^ 2)
      (p - 2 * k) (q - p * k + k ^ 2) := by
  unfold QuarticQuadraticFactorWitness at hfactor ⊢
  simp only [quarticShiftS1, quarticShiftS2,
    quarticShiftS3, quarticShiftS4] at hfactor
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
theorem quartic_factorWitness_of_negated
    (s1 s2 s3 s4 u v p q : ℤ)
    (hfactor : QuarticQuadraticFactorWitness
      (-s1) s2 (-s3) s4 u v p q) :
    QuarticQuadraticFactorWitness s1 s2 s3 s4
      (-u) v (-p) q := by
  unfold QuarticQuadraticFactorWitness at hfactor ⊢
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
theorem normalize_quartic_coefficients
    (s1 s2 s3 s4 : ℤ)
    (hnoRoot : ∀ z : ℤ, quarticEval s1 s2 s3 s4 z ≠ 0)
    (hnoQuadratic : ∀ u v p q : ℤ,
      ¬QuarticQuadraticFactorWitness s1 s2 s3 s4 u v p q) :
    ∃ t1 t2 t3 t4 : ℤ,
      (t1 = 0 ∨ t1 = 1 ∨ t1 = 2) ∧
      quarticSpread t1 t2 = quarticSpread s1 s2 ∧
      quarticHermiteMinorThree t1 t2 t3 t4 =
        quarticHermiteMinorThree s1 s2 s3 s4 ∧
      quarticDiscriminant t1 t2 t3 t4 =
        quarticDiscriminant s1 s2 s3 s4 ∧
      (∀ z : ℤ, quarticEval t1 t2 t3 t4 z ≠ 0) ∧
      ∀ u v p q : ℤ,
        ¬QuarticQuadraticFactorWitness t1 t2 t3 t4 u v p q := by
  have hremNonneg : 0 ≤ s1 % 4 :=
    Int.emod_nonneg s1 (by norm_num)
  have hremLt : s1 % 4 < 4 :=
    Int.emod_lt_of_pos s1 (by norm_num)
  have hdecomp : s1 / 4 * 4 + s1 % 4 = s1 :=
    Int.ediv_mul_add_emod s1 4
  interval_cases hrem : s1 % 4
  all_goals first
    | · refine ⟨quarticShiftS1 s1 (s1 / 4),
          quarticShiftS2 s1 s2 (s1 / 4),
          quarticShiftS3 s1 s2 s3 (s1 / 4),
          quarticShiftS4 s1 s2 s3 s4 (s1 / 4), ?_,
          quartic_shift_spread s1 s2 (s1 / 4),
          quartic_shift_hermiteMinorThree s1 s2 s3 s4 (s1 / 4),
          quartic_shift_discriminant s1 s2 s3 s4 (s1 / 4), ?_, ?_⟩
        · simp only [quarticShiftS1]
          omega
        · intro z hz
          apply hnoRoot (z + s1 / 4)
          rw [← quartic_shift_eval]
          exact hz
        · intro u v p q hfactor
          exact hnoQuadratic
            (u - 2 * (s1 / 4)) (v - u * (s1 / 4) + (s1 / 4) ^ 2)
            (p - 2 * (s1 / 4)) (q - p * (s1 / 4) + (s1 / 4) ^ 2)
            (quartic_factorWitness_of_shifted
              s1 s2 s3 s4 (s1 / 4) u v p q hfactor)
    | · let k : ℤ := -(s1 / 4) - 1
        refine ⟨quarticShiftS1 (-s1) k,
          quarticShiftS2 (-s1) s2 k,
          quarticShiftS3 (-s1) s2 (-s3) k,
          quarticShiftS4 (-s1) s2 (-s3) s4 k,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
        · right
          left
          simp only [quarticShiftS1, k]
          omega
        · rw [quartic_shift_spread, quartic_neg_spread]
        · rw [quartic_shift_hermiteMinorThree,
            quartic_neg_hermiteMinorThree]
        · rw [quartic_shift_discriminant,
            quartic_neg_discriminant]
        · intro z hz
          have hshift :
              quarticEval (-s1) s2 (-s3) s4 (z + k) = 0 := by
            rw [← quartic_shift_eval]
            exact hz
          rw [quartic_neg_eval] at hshift
          exact hnoRoot (-(z + k)) hshift
        · intro u v p q hfactor
          have hneg := quartic_factorWitness_of_shifted
            (-s1) s2 (-s3) s4 k u v p q hfactor
          exact hnoQuadratic
            (-(u - 2 * k)) (v - u * k + k ^ 2)
            (-(p - 2 * k)) (q - p * k + k ^ 2)
            (quartic_factorWitness_of_negated
              s1 s2 s3 s4
              (u - 2 * k) (v - u * k + k ^ 2)
              (p - 2 * k) (q - p * k + k ^ 2) hneg)

/-- The spread inequalities force a small second coefficient once the trace
coefficient is normalized. -/
theorem quartic_s2_bounds_of_normalized
    (s1 s2 : ℤ) (hs1 : s1 = 0 ∨ s1 = 1 ∨ s1 = 2)
    (hspreadPos : 0 < quarticSpread s1 s2)
    (hspreadLt : quarticSpread s1 s2 < 29) :
    -4 ≤ s2 ∧ s2 ≤ 2 := by
  rcases hs1 with rfl | rfl | rfl <;>
    simp only [quarticSpread, quarticSecondPowerSum] at hspreadPos hspreadLt
  all_goals omega

set_option maxHeartbeats 0 in
-- The lower bound for the constant coefficient is the costly case: after
-- the other three bounds have been obtained by nonlinear arithmetic, Lean
-- checks the remaining finite interval for `s3` exactly.
/-- The normalized spread bound and positivity of the next two Hermite
minors force the coefficient box used by the quartic finite search. -/
theorem quartic_s3_s4_bounds_of_normalized
    (s1 s2 s3 s4 : ℤ)
    (hs1 : s1 = 0 ∨ s1 = 1 ∨ s1 = 2)
    (hspreadPos : 0 < quarticSpread s1 s2)
    (hspreadLt : quarticSpread s1 s2 < 29)
    (hminor : 0 < quarticHermiteMinorThree s1 s2 s3 s4)
    (hdisc : 0 < quarticDiscriminant s1 s2 s3 s4) :
    -24 ≤ s3 ∧ s3 ≤ 24 ∧ -4 ≤ s4 ∧ s4 ≤ 4 := by
  have hs2 := quartic_s2_bounds_of_normalized
    s1 s2 hs1 hspreadPos hspreadLt
  rcases hs1 with rfl | rfl | rfl <;>
    rcases hs2 with ⟨hs2lo, hs2hi⟩ <;>
    interval_cases s2
  all_goals norm_num [quarticHermiteMinorThree] at hminor
  all_goals norm_num [quarticDiscriminant] at hdisc
  all_goals norm_num [quarticSpread,
    quarticSecondPowerSum] at hspreadPos
  all_goals norm_num [quarticSpread,
    quarticSecondPowerSum] at hspreadLt
  all_goals
    have hs3lo : -24 ≤ s3 := by
      nlinarith [sq_nonneg s3, sq_nonneg (s3 + 25)]
    have hs3hi : s3 ≤ 24 := by
      nlinarith [sq_nonneg s3, sq_nonneg (s3 - 25)]
    have hs4hi : s4 ≤ 4 := by
      nlinarith [sq_nonneg s3, sq_nonneg s4,
        sq_nonneg (s4 - 5)]
    refine ⟨hs3lo, hs3hi, ?_, hs4hi⟩
    interval_cases s3 <;>
      nlinarith [sq_nonneg s4, sq_nonneg (s4 + 5),
        sq_nonneg (s4 + 6), sq_nonneg (s4 + 7)]

/-- The elementary Minkowski ball gives the weaker spread bound `35`; after
trace normalization this still confines the second coefficient to a finite
interval. -/
theorem quartic_s2_bounds_of_normalized_thirtyFive
    (s1 s2 : ℤ) (hs1 : s1 = 0 ∨ s1 = 1 ∨ s1 = 2)
    (hspreadPos : 0 < quarticSpread s1 s2)
    (hspreadLt : quarticSpread s1 s2 < 35) :
    -4 ≤ s2 ∧ s2 ≤ 1 := by
  rcases hs1 with rfl | rfl | rfl <;>
    simp only [quarticSpread, quarticSecondPowerSum] at hspreadPos hspreadLt
  all_goals omega

set_option maxHeartbeats 0 in
-- Exact nonlinear elimination is repeated over the normalized coefficient cases.
/-- The coefficient box remains finite under the weaker Minkowski spread
bound. -/
theorem quartic_s3_s4_bounds_of_normalized_thirtyFive
    (s1 s2 s3 s4 : ℤ)
    (hs1 : s1 = 0 ∨ s1 = 1 ∨ s1 = 2)
    (hspreadPos : 0 < quarticSpread s1 s2)
    (hspreadLt : quarticSpread s1 s2 < 35)
    (hminor : 0 < quarticHermiteMinorThree s1 s2 s3 s4)
    (hdisc : 0 < quarticDiscriminant s1 s2 s3 s4) :
    -24 ≤ s3 ∧ s3 ≤ 24 ∧ -4 ≤ s4 ∧ s4 ≤ 4 := by
  have hs2 := quartic_s2_bounds_of_normalized_thirtyFive
    s1 s2 hs1 hspreadPos hspreadLt
  rcases hs1 with rfl | rfl | rfl <;>
    rcases hs2 with ⟨hs2lo, hs2hi⟩ <;>
    interval_cases s2
  all_goals norm_num [quarticHermiteMinorThree] at hminor
  all_goals norm_num [quarticDiscriminant] at hdisc
  all_goals norm_num [quarticSpread,
    quarticSecondPowerSum] at hspreadPos
  all_goals norm_num [quarticSpread,
    quarticSecondPowerSum] at hspreadLt
  all_goals
    have hs3lo : -24 ≤ s3 := by
      nlinarith [sq_nonneg s3, sq_nonneg (s3 + 25)]
    have hs3hi : s3 ≤ 24 := by
      nlinarith [sq_nonneg s3, sq_nonneg (s3 - 25)]
    have hs4hi : s4 ≤ 4 := by
      nlinarith [sq_nonneg s3, sq_nonneg s4,
        sq_nonneg (s4 - 5)]
    refine ⟨hs3lo, hs3hi, ?_, hs4hi⟩
    interval_cases s3 <;>
      nlinarith [sq_nonneg s4, sq_nonneg (s4 + 5),
        sq_nonneg (s4 + 6), sq_nonneg (s4 + 7)]

private instance (s1 s2 s3 s4 u v p q : ℤ) :
    Decidable (QuarticQuadraticFactorWitness s1 s2 s3 s4 u v p q) := by
  unfold QuarticQuadraticFactorWitness
  infer_instance

private def quarticS1Range : List ℤ := [0, 1, 2]

private def quarticS2Range : List ℤ :=
  (List.range 7).map (fun n ↦ (n : ℤ) - 4)

private def quarticS3Range : List ℤ :=
  (List.range 49).map (fun n ↦ (n : ℤ) - 24)

private def quarticS4Range : List ℤ :=
  (List.range 9).map (fun n ↦ (n : ℤ) - 4)

private def quarticSmallRange : List ℤ :=
  (List.range 7).map (fun n ↦ (n : ℤ) - 3)

private def quarticRootSearch (s1 s2 s3 s4 : ℤ) : Bool :=
  quarticSmallRange.any fun z ↦
    decide (quarticEval s1 s2 s3 s4 z = 0)

private def quarticFactorSearch (s1 s2 s3 s4 : ℤ) : Bool :=
  quarticSmallRange.any fun u ↦
    quarticSmallRange.any fun v ↦
      quarticSmallRange.any fun p ↦
        quarticSmallRange.any fun q ↦
          decide (QuarticQuadraticFactorWitness
            s1 s2 s3 s4 u v p q)

private def quarticAdmissible (s1 s2 s3 s4 : ℤ) : Bool :=
  decide (0 < quarticSpread s1 s2 ∧
    quarticSpread s1 s2 < 29 ∧
    0 < quarticHermiteMinorThree s1 s2 s3 s4 ∧
    0 < quarticDiscriminant s1 s2 s3 s4)

private def quarticOutcome (s1 s2 s3 s4 : ℤ) : Bool :=
  decide (quarticDiscriminant s1 s2 s3 s4 = 725) ||
    quarticRootSearch s1 s2 s3 s4 ||
    quarticFactorSearch s1 s2 s3 s4

/-- The complete finite check behind the quartic arithmetic reduction. -/
private def quarticFiniteCheck : Bool :=
  quarticS1Range.all fun s1 ↦
    quarticS2Range.all fun s2 ↦
      quarticS3Range.all fun s3 ↦
        quarticS4Range.all fun s4 ↦
          !quarticAdmissible s1 s2 s3 s4 ||
            quarticOutcome s1 s2 s3 s4

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every point in the finite quartic coefficient box.
private theorem quarticFiniteCheck_true :
    quarticFiniteCheck = true := by
  decide

/-- Under the normalized Hunter and Hermite inequalities, an irreducible
quartic in the coefficient box has discriminant exactly `725`. -/
theorem normalized_quartic_discriminant_eq_725
    (s1 s2 s3 s4 : ℤ)
    (hs1 : 0 ≤ s1) (hs1' : s1 ≤ 2)
    (hs2 : -4 ≤ s2) (hs2' : s2 ≤ 2)
    (hs3 : -24 ≤ s3) (hs3' : s3 ≤ 24)
    (hs4 : -4 ≤ s4) (hs4' : s4 ≤ 4)
    (hspreadPos : 0 < quarticSpread s1 s2)
    (hspreadLt : quarticSpread s1 s2 < 29)
    (hminor : 0 < quarticHermiteMinorThree s1 s2 s3 s4)
    (hdisc : 0 < quarticDiscriminant s1 s2 s3 s4)
    (hnoRoot : ∀ z : ℤ, quarticEval s1 s2 s3 s4 z ≠ 0)
    (hnoQuadratic : ∀ u v p q : ℤ,
      ¬QuarticQuadraticFactorWitness s1 s2 s3 s4 u v p q) :
    quarticDiscriminant s1 s2 s3 s4 = 725 := by
  have hs1mem : s1 ∈ quarticS1Range := by
    interval_cases s1 <;> decide
  have hs2mem : s2 ∈ quarticS2Range := by
    interval_cases s2 <;> decide
  have hs3mem : s3 ∈ quarticS3Range := by
    interval_cases s3 <;> decide
  have hs4mem : s4 ∈ quarticS4Range := by
    interval_cases s4 <;> decide
  have hall1 := List.all_eq_true.mp quarticFiniteCheck_true
  have hall2 := List.all_eq_true.mp (hall1 s1 hs1mem)
  have hall3 := List.all_eq_true.mp (hall2 s2 hs2mem)
  have hall4 := List.all_eq_true.mp (hall3 s3 hs3mem)
  have hrow := hall4 s4 hs4mem
  have hadmissible : quarticAdmissible s1 s2 s3 s4 = true := by
    simp [quarticAdmissible, hspreadPos, hspreadLt, hminor, hdisc]
  have houtcome : quarticOutcome s1 s2 s3 s4 = true := by
    simpa [hadmissible] using hrow
  simp only [quarticOutcome, Bool.or_eq_true, decide_eq_true_eq] at houtcome
  rcases houtcome with (hdisc725 | hroot) | hfactor
  · exact hdisc725
  · change quarticSmallRange.any (fun z ↦
      decide (quarticEval s1 s2 s3 s4 z = 0)) = true at hroot
    obtain ⟨z, -, hz⟩ := List.any_eq_true.mp hroot
    exact ((hnoRoot z) (of_decide_eq_true hz)).elim
  · change quarticSmallRange.any (fun u ↦
      quarticSmallRange.any fun v ↦
        quarticSmallRange.any fun p ↦
          quarticSmallRange.any fun q ↦
            decide (QuarticQuadraticFactorWitness
              s1 s2 s3 s4 u v p q)) = true at hfactor
    obtain ⟨u, -, hu⟩ := List.any_eq_true.mp hfactor
    obtain ⟨v, -, hv⟩ := List.any_eq_true.mp hu
    obtain ⟨p, -, hp⟩ := List.any_eq_true.mp hv
    obtain ⟨q, -, hq⟩ := List.any_eq_true.mp hp
    exact ((hnoQuadratic u v p q) (of_decide_eq_true hq)).elim

private def quarticAdmissibleThirtyFive
    (s1 s2 s3 s4 : ℤ) : Bool :=
  decide (0 < quarticSpread s1 s2 ∧
    quarticSpread s1 s2 < 35 ∧
    0 < quarticHermiteMinorThree s1 s2 s3 s4 ∧
    0 < quarticDiscriminant s1 s2 s3 s4)

private def quarticExceptionalRowThirtyFive
    (s1 s2 s3 s4 : ℤ) : Bool :=
  decide ((s1 = 0 ∧ s2 = -4 ∧ s3 = -1 ∧ s4 = 1) ∨
    (s1 = 0 ∧ s2 = -4 ∧ s3 = 0 ∧ s4 = 1) ∨
    (s1 = 0 ∧ s2 = -4 ∧ s3 = 0 ∧ s4 = 2) ∨
    (s1 = 0 ∧ s2 = -4 ∧ s3 = 1 ∧ s4 = 1) ∨
    (s1 = 1 ∧ s2 = -3 ∧ s3 = -1 ∧ s4 = 1) ∨
    (s1 = 2 ∧ s2 = -2 ∧ s3 = -3 ∧ s4 = 1))

private def quarticOutcomeThirtyFive
    (s1 s2 s3 s4 : ℤ) : Bool :=
  quarticExceptionalRowThirtyFive s1 s2 s3 s4 ||
    quarticRootSearch s1 s2 s3 s4 ||
    quarticFactorSearch s1 s2 s3 s4

private def quarticFiniteCheckThirtyFive : Bool :=
  quarticS1Range.all fun s1 ↦
    quarticS2Range.all fun s2 ↦
      quarticS3Range.all fun s3 ↦
        quarticS4Range.all fun s4 ↦
          !quarticAdmissibleThirtyFive s1 s2 s3 s4 ||
            quarticOutcomeThirtyFive s1 s2 s3 s4

set_option maxHeartbeats 0 in
-- Kernel reduction checks every row in the enlarged quartic coefficient box.
set_option maxRecDepth 100000 in
private theorem quarticFiniteCheckThirtyFive_true :
    quarticFiniteCheckThirtyFive = true := by
  decide

/-- Under the weaker Minkowski spread bound, every irreducible normalized
quartic is one of six explicitly checked coefficient rows. -/
theorem normalized_quartic_rows_of_spread_lt_thirtyFive
    (s1 s2 s3 s4 : ℤ)
    (hs1 : 0 ≤ s1) (hs1' : s1 ≤ 2)
    (hs2 : -4 ≤ s2) (hs2' : s2 ≤ 2)
    (hs3 : -24 ≤ s3) (hs3' : s3 ≤ 24)
    (hs4 : -4 ≤ s4) (hs4' : s4 ≤ 4)
    (hspreadPos : 0 < quarticSpread s1 s2)
    (hspreadLt : quarticSpread s1 s2 < 35)
    (hminor : 0 < quarticHermiteMinorThree s1 s2 s3 s4)
    (hdisc : 0 < quarticDiscriminant s1 s2 s3 s4)
    (hnoRoot : ∀ z : ℤ, quarticEval s1 s2 s3 s4 z ≠ 0)
    (hnoQuadratic : ∀ u v p q : ℤ,
      ¬QuarticQuadraticFactorWitness s1 s2 s3 s4 u v p q) :
    (s1 = 0 ∧ s2 = -4 ∧ s3 = -1 ∧ s4 = 1) ∨
      (s1 = 0 ∧ s2 = -4 ∧ s3 = 0 ∧ s4 = 1) ∨
      (s1 = 0 ∧ s2 = -4 ∧ s3 = 0 ∧ s4 = 2) ∨
      (s1 = 0 ∧ s2 = -4 ∧ s3 = 1 ∧ s4 = 1) ∨
      (s1 = 1 ∧ s2 = -3 ∧ s3 = -1 ∧ s4 = 1) ∨
      (s1 = 2 ∧ s2 = -2 ∧ s3 = -3 ∧ s4 = 1) := by
  have hs1mem : s1 ∈ quarticS1Range := by
    interval_cases s1 <;> decide
  have hs2mem : s2 ∈ quarticS2Range := by
    interval_cases s2 <;> decide
  have hs3mem : s3 ∈ quarticS3Range := by
    interval_cases s3 <;> decide
  have hs4mem : s4 ∈ quarticS4Range := by
    interval_cases s4 <;> decide
  have hall1 := List.all_eq_true.mp quarticFiniteCheckThirtyFive_true
  have hall2 := List.all_eq_true.mp (hall1 s1 hs1mem)
  have hall3 := List.all_eq_true.mp (hall2 s2 hs2mem)
  have hall4 := List.all_eq_true.mp (hall3 s3 hs3mem)
  have hrow := hall4 s4 hs4mem
  have hadmissible :
      quarticAdmissibleThirtyFive s1 s2 s3 s4 = true := by
    simp [quarticAdmissibleThirtyFive, hspreadPos, hspreadLt,
      hminor, hdisc]
  have houtcome : quarticOutcomeThirtyFive s1 s2 s3 s4 = true := by
    simpa [hadmissible] using hrow
  simp only [quarticOutcomeThirtyFive,
    quarticExceptionalRowThirtyFive, Bool.or_eq_true,
    decide_eq_true_eq] at houtcome
  rcases houtcome with (hrow | hroot) | hfactor
  · exact hrow
  · change quarticSmallRange.any (fun z ↦
      decide (quarticEval s1 s2 s3 s4 z = 0)) = true at hroot
    obtain ⟨z, -, hz⟩ := List.any_eq_true.mp hroot
    exact ((hnoRoot z) (of_decide_eq_true hz)).elim
  · change quarticSmallRange.any (fun u ↦
      quarticSmallRange.any fun v ↦
        quarticSmallRange.any fun p ↦
          quarticSmallRange.any fun q ↦
            decide (QuarticQuadraticFactorWitness
              s1 s2 s3 s4 u v p q)) = true at hfactor
    obtain ⟨u, -, hu⟩ := List.any_eq_true.mp hfactor
    obtain ⟨v, -, hv⟩ := List.any_eq_true.mp hu
    obtain ⟨p, -, hp⟩ := List.any_eq_true.mp hv
    obtain ⟨q, -, hq⟩ := List.any_eq_true.mp hp
    exact ((hnoQuadratic u v p q) (of_decide_eq_true hq)).elim

/-- The six coefficient rows above have exactly four polynomial
discriminants. -/
theorem normalized_quartic_discriminant_candidates_of_spread_lt_thirtyFive
    (s1 s2 s3 s4 : ℤ)
    (hs1 : 0 ≤ s1) (hs1' : s1 ≤ 2)
    (hs2 : -4 ≤ s2) (hs2' : s2 ≤ 2)
    (hs3 : -24 ≤ s3) (hs3' : s3 ≤ 24)
    (hs4 : -4 ≤ s4) (hs4' : s4 ≤ 4)
    (hspreadPos : 0 < quarticSpread s1 s2)
    (hspreadLt : quarticSpread s1 s2 < 35)
    (hminor : 0 < quarticHermiteMinorThree s1 s2 s3 s4)
    (hdisc : 0 < quarticDiscriminant s1 s2 s3 s4)
    (hnoRoot : ∀ z : ℤ, quarticEval s1 s2 s3 s4 z ≠ 0)
    (hnoQuadratic : ∀ u v p q : ℤ,
      ¬QuarticQuadraticFactorWitness s1 s2 s3 s4 u v p q) :
    quarticDiscriminant s1 s2 s3 s4 = 725 ∨
      quarticDiscriminant s1 s2 s3 s4 = 1957 ∨
      quarticDiscriminant s1 s2 s3 s4 = 2048 ∨
      quarticDiscriminant s1 s2 s3 s4 = 2304 := by
  rcases normalized_quartic_rows_of_spread_lt_thirtyFive
      s1 s2 s3 s4 hs1 hs1' hs2 hs2' hs3 hs3' hs4 hs4'
      hspreadPos hspreadLt hminor hdisc hnoRoot hnoQuadratic with
    h | h | h | h | h | h
  all_goals rcases h with ⟨rfl, rfl, rfl, rfl⟩
  all_goals norm_num [quarticDiscriminant]

/-- If the field discriminant lies strictly between `29` and `725`, the
`725` and `1957` polynomial-discriminant outcomes are arithmetically
impossible. Thus the weaker Minkowski route leaves only the two even-index
cases. -/
theorem quartic_small_field_candidates_reduce_to_2048_or_2304
    (s1 s2 s3 s4 d : ℤ) (index : ℕ)
    (hindex : 0 < index) (hdLower : 29 < d) (hdUpper : d < 725)
    (hrelation : quarticDiscriminant s1 s2 s3 s4 =
      (index : ℤ) ^ 2 * d)
    (hcandidates :
      quarticDiscriminant s1 s2 s3 s4 = 725 ∨
      quarticDiscriminant s1 s2 s3 s4 = 1957 ∨
      quarticDiscriminant s1 s2 s3 s4 = 2048 ∨
      quarticDiscriminant s1 s2 s3 s4 = 2304) :
    quarticDiscriminant s1 s2 s3 s4 = 2048 ∨
      quarticDiscriminant s1 s2 s3 s4 = 2304 := by
  rcases hcandidates with h725 | h1957 | h2048 | h2304
  · have hindexLt : index < 5 := by
      by_contra hnot
      have hi : (5 : ℤ) ≤ index := by exact_mod_cast (by omega : 5 ≤ index)
      rw [h725] at hrelation
      nlinarith [sq_nonneg ((index : ℤ) - 5)]
    interval_cases index <;> norm_num at hrelation <;> omega
  · have hindexLt : index < 9 := by
      by_contra hnot
      have hi : (9 : ℤ) ≤ index := by exact_mod_cast (by omega : 9 ≤ index)
      rw [h1957] at hrelation
      nlinarith [sq_nonneg ((index : ℤ) - 9)]
    interval_cases index <;> norm_num at hrelation <;> omega
  · exact Or.inl h2048
  · exact Or.inr h2304

/-- The concrete normalized certificate needed below the hypothetical
degree-four discriminant bound.  The finite arithmetic of the certificate is
fully checked above. The field-theoretic reduction constructs its positivity,
irreducibility, and index fields from a primitive Hunter generator. -/
def DegreeFourHunterCertificateInput : Prop :=
  ∀ (K : CodedNumberField), NumberField.IsTotallyReal K.1 →
    Module.finrank ℚ K.1 = 4 →
      |K.discriminant| < 725 →
      ∃ s1 s2 s3 s4 : ℤ, ∃ index : ℕ,
        (s1 = 0 ∨ s1 = 1 ∨ s1 = 2) ∧
        -24 ≤ s3 ∧ s3 ≤ 24 ∧
        -4 ≤ s4 ∧ s4 ≤ 4 ∧
        0 < quarticSpread s1 s2 ∧
        quarticSpread s1 s2 < 29 ∧
        0 < quarticHermiteMinorThree s1 s2 s3 s4 ∧
        0 < quarticDiscriminant s1 s2 s3 s4 ∧
        (∀ z : ℤ, quarticEval s1 s2 s3 s4 z ≠ 0) ∧
        (∀ u v p q : ℤ,
          ¬QuarticQuadraticFactorWitness s1 s2 s3 s4 u v p q) ∧
        0 < index ∧
        quarticDiscriminant s1 s2 s3 s4 =
          (index : ℤ) ^ 2 * K.discriminant

/-- The normalized quartic Hunter certificate implies the exact lower bound
`|D_K| >= 725`. -/
theorem coded_degree_four_discriminant_ge_725_of_hunterCertificate
    (hHunter : DegreeFourHunterCertificateInput)
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
    have hs2Bounds := quartic_s2_bounds_of_normalized
      s1 s2 hs1 hspreadPos hspreadLt
    have hpoly := normalized_quartic_discriminant_eq_725
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
