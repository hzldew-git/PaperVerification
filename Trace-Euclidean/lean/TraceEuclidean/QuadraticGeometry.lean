import TraceEuclidean.Basic
import TraceEuclidean.QuadraticArithmetic
import Mathlib.Algebra.Order.Round

namespace TraceEuclidean

noncomputable section

abbrev PlanePoint (K : Type*) := K × K
abbrev IntegralPoint := ℤ × ℤ

def caseICostOver {K : Type*} [Ring K] (m : K)
    (x : PlanePoint K) (z : IntegralPoint) : K :=
  2 * ((x.1 - (z.1 : K)) ^ 2 + m * (x.2 - (z.2 : K)) ^ 2)

def caseIICostOver {K : Type*} [Field K] (m : K)
    (x : PlanePoint K) (z : IntegralPoint) : K :=
  let u := x.1 - (z.1 : K)
  let v := x.2 - (z.2 : K)
  2 * u ^ 2 + 2 * u * v + (m + 1) / 2 * v ^ 2

def caseIRadiusSqOver {K : Type*} [Field K] (m : K) : K :=
  (m + 1) / 2

def caseIIRadiusSqOver {K : Type*} [Field K] (m : K) : K :=
  (m + 1) ^ 2 / (8 * m)

theorem abs_sub_round_field {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FloorRing K] (x : K) :
    |x - (round x : K)| ≤ 1 / 2 :=
  abs_sub_round x

theorem caseI_two_upper_over {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FloorRing K] (x : PlanePoint K) :
    ∃ z : IntegralPoint, caseICostOver (2 : K) x z < 2 := by
  let a : ℤ := round x.1
  let b : ℤ := round x.2
  refine ⟨(a, b), ?_⟩
  have hu := abs_sub_round_field x.1
  have hv := abs_sub_round_field x.2
  have hu' := abs_le.mp hu
  have hv' := abs_le.mp hv
  dsimp [caseICostOver, a, b]
  nlinarith [sq_nonneg (x.1 - (round x.1 : K) + 1 / 2),
    sq_nonneg (1 / 2 - (x.1 - (round x.1 : K))),
    sq_nonneg (x.2 - (round x.2 : K) + 1 / 2),
    sq_nonneg (1 / 2 - (x.2 - (round x.2 : K)))]

theorem caseII_completedSquare_over {K : Type*} [Field K] [CharZero K] (m : K)
    (x : PlanePoint K) (z : IntegralPoint) :
    caseIICostOver m x z =
      2 * (x.1 - (z.1 : K) + (x.2 - (z.2 : K)) / 2) ^ 2 +
        m / 2 * (x.2 - (z.2 : K)) ^ 2 := by
  simp only [caseIICostOver]
  ring

theorem caseII_half_region_bound_over {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {m a b : K} (hm : 0 < m)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) (hb0 : 0 ≤ b)
    (hline : 2 * a + m * b ≤ (m + 1) / 2) :
    2 * a ^ 2 + m / 2 * b ^ 2 ≤ (m + 1) ^ 2 / (8 * m) := by
  let c : K := ((m + 1) / 2 - 2 * a) / m
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    apply div_nonneg
    · have hmb := mul_nonneg (le_of_lt hm) hb0
      linarith
    · exact le_of_lt hm
  have hbc : b ≤ c := by
    dsimp only [c]
    apply (le_div_iff₀ hm).2
    linarith
  have hbSq : b ^ 2 ≤ c ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hbc) (add_nonneg hb0 hc0)
    nlinarith
  have hmul : m / 2 * b ^ 2 ≤ m / 2 * c ^ 2 :=
    mul_le_mul_of_nonneg_left hbSq (by positivity)
  have hprod : 0 ≤ a * (1 - 2 * a) * (m + 1) / m := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg ha0 (by linarith)) (by linarith)
    · exact le_of_lt hm
  have hid :
      (m + 1) ^ 2 / (8 * m) -
          (2 * a ^ 2 + m / 2 * c ^ 2) =
        a * (1 - 2 * a) * (m + 1) / m := by
    dsimp only [c]
    field_simp [ne_of_gt hm]
    ring
  linarith

theorem caseII_cover_pair_over {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {m a b : K} (hm : 0 < m)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) :
    2 * a ^ 2 + m / 2 * b ^ 2 ≤ (m + 1) ^ 2 / (8 * m) ∨
      2 * (1 / 2 - a) ^ 2 + m / 2 * (1 - b) ^ 2 ≤
        (m + 1) ^ 2 / (8 * m) := by
  by_cases hline : 2 * a + m * b ≤ (m + 1) / 2
  · exact Or.inl (caseII_half_region_bound_over hm ha0 ha1 hb0 hline)
  · right
    apply caseII_half_region_bound_over hm
    · linarith
    · linarith
    · linarith
    · push Not at hline
      linarith

theorem caseII_upper_over {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]
    {m : K} (hm : 0 < m) (x : PlanePoint K) :
    ∃ z : IntegralPoint,
      caseIICostOver m x z ≤ caseIIRadiusSqOver m := by
  let b : ℤ := round x.2
  let δ : K := x.2 - (b : K)
  let a : ℤ := round (x.1 + δ / 2)
  let w : K := x.1 + δ / 2 - (a : K)
  have hδ : |δ| ≤ 1 / 2 := by
    simpa only [δ, b] using abs_sub_round_field x.2
  have hw : |w| ≤ 1 / 2 := by
    simpa only [w, a] using abs_sub_round_field (x.1 + δ / 2)
  rcases caseII_cover_pair_over hm (abs_nonneg w) hw (abs_nonneg δ) hδ with
      hbase | halt
  · refine ⟨(a, b), ?_⟩
    rw [caseII_completedSquare_over]
    have hv : x.2 - (b : K) = δ := by rfl
    have hu : x.1 - (a : K) + (x.2 - (b : K)) / 2 = w := by
      rw [hv]
      dsimp only [w]
      ring
    rw [hu, hv]
    simpa only [caseIIRadiusSqOver, sq_abs] using hbase
  · by_cases hδ0 : 0 ≤ δ
    · by_cases hw0 : 0 ≤ w
      · simp only [abs_of_nonneg hw0, abs_of_nonneg hδ0] at halt
        refine ⟨(a, b + 1), ?_⟩
        rw [caseII_completedSquare_over]
        have hv : x.2 - ((b + 1 : ℤ) : K) = δ - 1 := by
          dsimp only [δ]
          push_cast
          ring
        have hu :
            x.1 - (a : K) + (x.2 - ((b + 1 : ℤ) : K)) / 2 =
              w - 1 / 2 := by
          rw [hv]
          dsimp only [w]
          ring
        rw [hu, hv]
        unfold caseIIRadiusSqOver
        ring_nf at halt ⊢
        exact halt
      · have hwneg : w < 0 := lt_of_not_ge hw0
        simp only [abs_of_neg hwneg, abs_of_nonneg hδ0] at halt
        refine ⟨(a - 1, b + 1), ?_⟩
        rw [caseII_completedSquare_over]
        have hv : x.2 - ((b + 1 : ℤ) : K) = δ - 1 := by
          dsimp only [δ]
          push_cast
          ring
        have hu :
            x.1 - ((a - 1 : ℤ) : K) +
                (x.2 - ((b + 1 : ℤ) : K)) / 2 = w + 1 / 2 := by
          rw [hv]
          dsimp only [w]
          push_cast
          ring
        rw [hu, hv]
        unfold caseIIRadiusSqOver
        ring_nf at halt ⊢
        exact halt
    · have hδneg : δ < 0 := lt_of_not_ge hδ0
      by_cases hw0 : 0 ≤ w
      · simp only [abs_of_nonneg hw0, abs_of_neg hδneg] at halt
        refine ⟨(a + 1, b - 1), ?_⟩
        rw [caseII_completedSquare_over]
        have hv : x.2 - ((b - 1 : ℤ) : K) = δ + 1 := by
          dsimp only [δ]
          push_cast
          ring
        have hu :
            x.1 - ((a + 1 : ℤ) : K) +
                (x.2 - ((b - 1 : ℤ) : K)) / 2 = w - 1 / 2 := by
          rw [hv]
          dsimp only [w]
          push_cast
          ring
        rw [hu, hv]
        unfold caseIIRadiusSqOver
        ring_nf at halt ⊢
        exact halt
      · have hwneg : w < 0 := lt_of_not_ge hw0
        simp only [abs_of_neg hwneg, abs_of_neg hδneg] at halt
        refine ⟨(a, b - 1), ?_⟩
        rw [caseII_completedSquare_over]
        have hv : x.2 - ((b - 1 : ℤ) : K) = δ + 1 := by
          dsimp only [δ]
          push_cast
          ring
        have hu :
            x.1 - (a : K) + (x.2 - ((b - 1 : ℤ) : K)) / 2 =
              w + 1 / 2 := by
          rw [hv]
          dsimp only [w]
          ring
        rw [hu, hv]
        unfold caseIIRadiusSqOver
        ring_nf at halt ⊢
        exact halt

theorem sq_le_quarter_of_abs_le_half {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {x : K} (hx : |x| ≤ 1 / 2) : x ^ 2 ≤ 1 / 4 := by
  have h := abs_le.mp hx
  have hp := mul_nonneg (show 0 ≤ x + 1 / 2 by linarith)
    (show 0 ≤ 1 / 2 - x by linarith)
  nlinarith

theorem caseI_upper_over {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]
    {m : K} (hm : 0 ≤ m) (x : PlanePoint K) :
    ∃ z : IntegralPoint,
      caseICostOver m x z ≤ caseIRadiusSqOver m := by
  let a : ℤ := round x.1
  let b : ℤ := round x.2
  refine ⟨(a, b), ?_⟩
  have hu := sq_le_quarter_of_abs_le_half (abs_sub_round_field x.1)
  have hv := sq_le_quarter_of_abs_le_half (abs_sub_round_field x.2)
  have hmv := mul_le_mul_of_nonneg_left hv hm
  dsimp only [caseICostOver, caseIRadiusSqOver, a, b]
  linarith

theorem halfIntegerSquare_ge_quarter_over {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (a : ℤ) : (1 / 2 - (a : K)) ^ 2 ≥ 1 / 4 := by
  have ha : a ≤ 0 ∨ 1 ≤ a := by omega
  rcases ha with ha | ha
  · have haq : (a : K) ≤ 0 := by exact_mod_cast ha
    nlinarith [sq_nonneg (1 / 2 - (a : K))]
  · have haq : (1 : K) ≤ a := by exact_mod_cast ha
    nlinarith [sq_nonneg (1 / 2 - (a : K))]

theorem caseI_midpoint_lower_over {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {m : K} (hm : 0 ≤ m) (z : IntegralPoint) :
    caseIRadiusSqOver m ≤
      caseICostOver m (1 / 2, 1 / 2) z := by
  have ha := halfIntegerSquare_ge_quarter_over (K := K) z.1
  have hb := halfIntegerSquare_ge_quarter_over (K := K) z.2
  have hmb := mul_le_mul_of_nonneg_left hb hm
  simp only [caseIRadiusSqOver, caseICostOver]
  linarith

theorem integral_difference_nonneg_over {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {A : K} (hA : 3 ≤ A) (a b : ℤ) :
    0 ≤ 2 * (a : K) ^ 2 + 2 * a * b - 2 * a +
      A * (b : K) ^ 2 - A * b := by
  by_cases hb : b = 0
  · subst b
    have ha : a ≤ 0 ∨ 1 ≤ a := by omega
    rcases ha with ha | ha
    · have haq : (a : K) ≤ 0 := by exact_mod_cast ha
      have hp := mul_nonneg_of_nonpos_of_nonpos haq
        (show (a : K) - 1 ≤ 0 by linarith)
      norm_num
      nlinarith
    · have haq : (1 : K) ≤ a := by exact_mod_cast ha
      have hp := mul_nonneg (show 0 ≤ (a : K) by linarith)
        (show 0 ≤ (a : K) - 1 by linarith)
      norm_num
      nlinarith
  · have hbCases : b ≤ -1 ∨ 1 ≤ b := by omega
    rcases hbCases with hbneg | hbpos
    · have hbq : (b : K) ≤ -1 := by exact_mod_cast hbneg
      have hA0 : 0 ≤ A - 1 := by linarith
      have hmul : (A - 1) * (b : K) ≤ (A - 1) * (-1) :=
        mul_le_mul_of_nonneg_left hbq hA0
      have hfac2 : (A - 1) * (b : K) + 1 ≤ 0 := by linarith
      have hfac1 : (b : K) - 1 ≤ 0 := by linarith
      have hprod :
          0 ≤ ((b : K) - 1) * ((A - 1) * (b : K) + 1) :=
        mul_nonneg_of_nonpos_of_nonpos hfac1 hfac2
      nlinarith [sq_nonneg ((a : K) + (b : K) - 1),
        sq_nonneg (a : K)]
    · have hbq : (1 : K) ≤ b := by exact_mod_cast hbpos
      have hfac1 : 0 ≤ (b : K) - 1 := by linarith
      have hfac2 : 0 ≤ (A - 1) * (b : K) + 1 := by
        have hp := mul_nonneg (show 0 ≤ A - 1 by linarith)
          (show 0 ≤ (b : K) by linarith)
        linarith
      have hprod :
          0 ≤ ((b : K) - 1) * ((A - 1) * (b : K) + 1) :=
        mul_nonneg hfac1 hfac2
      nlinarith [sq_nonneg ((a : K) + (b : K) - 1),
        sq_nonneg (a : K)]

def caseIIVertexOver {K : Type*} [Field K] (m : K) : PlanePoint K :=
  ((m + 1) / (4 * m), (m - 1) / (2 * m))

theorem caseII_vertex_lower_over {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {m : K} (hm : 5 ≤ m) (z : IntegralPoint) :
    caseIIRadiusSqOver m ≤
      caseIICostOver m (caseIIVertexOver m) z := by
  have hm0 : m ≠ 0 := by linarith
  have hA : (3 : K) ≤ (m + 1) / 2 := by linarith
  have hdiff := integral_difference_nonneg_over hA z.1 z.2
  have hid :
      caseIICostOver m (caseIIVertexOver m) z =
        caseIIRadiusSqOver m +
          (2 * (z.1 : K) ^ 2 + 2 * z.1 * z.2 - 2 * z.1 +
            (m + 1) / 2 * (z.2 : K) ^ 2 -
              (m + 1) / 2 * z.2) := by
    simp only [caseIICostOver, caseIIVertexOver, caseIIRadiusSqOver]
    field_simp [hm0]
    ring
  rw [hid]
  linarith

/-- An exact squared covering-radius specification over an ordered field. -/
structure SquaredCoveringRadiusSpecOver {K X Y : Type*}
    [LT K] [LE K] (cost : X → Y → K) (ρsq : K) : Prop where
  upper : ∀ x, ∃ y, cost x y ≤ ρsq
  sharp : ∀ r, r < ρsq → ∃ x, ∀ y, r < cost x y

theorem caseI_exact_radius_over {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]
    {m : K} (hm : 0 ≤ m) :
    SquaredCoveringRadiusSpecOver
      (caseICostOver m : PlanePoint K → IntegralPoint → K)
      (caseIRadiusSqOver m) := by
  constructor
  · exact caseI_upper_over hm
  · intro r hr
    refine ⟨(1 / 2, 1 / 2), fun z ↦ ?_⟩
    exact hr.trans_le (caseI_midpoint_lower_over hm z)

theorem caseII_exact_radius_over {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]
    {m : K} (hm : 5 ≤ m) :
    SquaredCoveringRadiusSpecOver
      (caseIICostOver m : PlanePoint K → IntegralPoint → K)
      (caseIIRadiusSqOver m) := by
  constructor
  · exact caseII_upper_over (by linarith)
  · intro r hr
    refine ⟨caseIIVertexOver m, fun z ↦ ?_⟩
    exact hr.trans_le (caseII_vertex_lower_over hm z)

def realQuadraticCostReal (m : ℕ) :
    PlanePoint ℝ → IntegralPoint → ℝ :=
  if m % 4 = 1 then caseIICostOver (m : ℝ)
  else caseICostOver (m : ℝ)

def realQuadraticRadiusSq (m : ℕ) : ℝ :=
  if m % 4 = 1 then caseIIRadiusSqOver (m : ℝ)
  else caseIRadiusSqOver (m : ℝ)

/-- Coordinate form of Proposition 6.1 on the full Minkowski plane. -/
theorem realQuadratic_coveringRadiusSq {m : ℕ}
    (hm : 1 < m) (_hsq : IsSquarefreeNat m) :
    SquaredCoveringRadiusSpecOver (realQuadraticCostReal m)
      (realQuadraticRadiusSq m) := by
  by_cases hmod : m % 4 = 1
  · have hm5 : 5 ≤ m := by omega
    simpa [realQuadraticCostReal, realQuadraticRadiusSq, hmod] using
      (caseII_exact_radius_over (K := ℝ) (m := (m : ℝ))
        (by exact_mod_cast hm5))
  · simpa [realQuadraticCostReal, realQuadraticRadiusSq, hmod] using
      (caseI_exact_radius_over (K := ℝ) (m := (m : ℝ))
        (by positivity))

/-- Proposition 6.1(i), with the two possible non-one residue classes stated explicitly. -/
theorem realQuadratic_coveringRadiusSq_caseI {m : ℕ}
    (hm : 1 < m) (hsq : IsSquarefreeNat m)
    (hmod : m % 4 = 2 ∨ m % 4 = 3) :
    SquaredCoveringRadiusSpecOver (realQuadraticCostReal m)
      (((m : ℝ) + 1) / 2) := by
  have hnot : m % 4 ≠ 1 := by omega
  simpa [realQuadraticRadiusSq, hnot, caseIRadiusSqOver] using
    realQuadratic_coveringRadiusSq hm hsq

/-- Proposition 6.1(ii), in the integral basis used when `m ≡ 1 (mod 4)`. -/
theorem realQuadratic_coveringRadiusSq_caseII {m : ℕ}
    (hm : 1 < m) (hsq : IsSquarefreeNat m) (hmod : m % 4 = 1) :
    SquaredCoveringRadiusSpecOver (realQuadraticCostReal m)
      ((((m : ℝ) + 1) ^ 2) / (8 * m)) := by
  simpa [realQuadraticRadiusSq, hmod, caseIIRadiusSqOver] using
    realQuadratic_coveringRadiusSq hm hsq

end

end TraceEuclidean
