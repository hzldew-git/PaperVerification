import TraceEuclidean.QuadraticGeometry
import TraceEuclidean.V15SixRadii

/-!
The remaining non-scalar binary covering calculation in Theorem 1.7.
The Gram matrix `(5, 2, 5)` has quadratic form `5u² + 4uv + 5v²`.
The proof below works directly with every point of the real plane and every
integer translate; the sharp point has rational coordinates.
-/

namespace TraceEuclidean

noncomputable section

private def q21 (u v : ℝ) : ℝ := 5 * u ^ 2 + 4 * u * v + 5 * v ^ 2

def v15TwentyOneCost (x : PlanePoint ℝ) (z : IntegralPoint) : ℝ :=
  q21 (x.1 - (z.1 : ℝ)) (x.2 - (z.2 : ℝ))

/-- The real binary quadratic cost represented by a reduced trace Gram matrix. -/
def v15GramCost (a b c : ℕ) (x : PlanePoint ℝ) (z : IntegralPoint) : ℝ :=
  let u := x.1 - (z.1 : ℝ)
  let v := x.2 - (z.2 : ℝ)
  (a : ℝ) * u ^ 2 + 2 * b * u * v + (c : ℝ) * v ^ 2

private theorem q21_opposite_box {u w : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1 / 2) :
    q21 u (-w) ≤ 3 / 2 := by
  have huSq : u ^ 2 ≤ u / 2 := by
    nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu1)]
  have hwSq : w ^ 2 ≤ w / 2 := by
    nlinarith [mul_nonneg hw0 (sub_nonneg.mpr hw1)]
  have hprod := mul_nonneg (sub_nonneg.mpr hu1) (sub_nonneg.mpr hw1)
  dsimp [q21]
  nlinarith

private theorem q21_positive_triangle {u v : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2)
    (hv0 : 0 ≤ v) (hvu : v ≤ u) :
    q21 u v ≤ 25 / 14 ∨ q21 (u - 1) v ≤ 25 / 14 := by
  by_cases hline : 10 * u + 4 * v ≤ 5
  · left
    let U : ℝ := (5 - 4 * v) / 10
    have hU : u ≤ U := by dsimp [U]; linarith
    have hU0 : 0 ≤ U := le_trans hu0 hU
    have hfac : 0 ≤ 5 * (U + u) + 4 * v := by positivity
    have hmono := mul_nonneg (sub_nonneg.mpr hU) hfac
    have hv5 : v ≤ 5 / 14 := by linarith
    have hvSq : v ^ 2 ≤ (5 / 14 : ℝ) ^ 2 := by
      nlinarith [mul_nonneg
        (show 0 ≤ (5 / 14 : ℝ) - v by linarith)
        (show 0 ≤ (5 / 14 : ℝ) + v by linarith)]
    have hformula : q21 U v = 5 / 4 + 21 / 5 * v ^ 2 := by
      dsimp [q21, U]
      ring
    have hqu : q21 u v ≤ q21 U v := by
      dsimp [q21] at *
      nlinarith [hmono]
    rw [hformula] at hqu
    nlinarith
  · right
    have hline' : 5 < 10 * u + 4 * v := lt_of_not_ge hline
    let W : ℝ := 1 - u
    have hW0 : 1 / 2 ≤ W := by dsimp [W]; linarith
    have hv1 : v ≤ 1 / 2 := le_trans hvu hu1
    by_cases hv5 : v ≤ 5 / 14
    · let U : ℝ := 1 / 2 + 2 * v / 5
      have hWU : W ≤ U := by dsimp [W, U]; linarith
      have hfac : 0 ≤ 5 * (U + W) - 4 * v := by
        dsimp [U]
        linarith
      have hmono := mul_nonneg (sub_nonneg.mpr hWU) hfac
      have hvSq : v ^ 2 ≤ (5 / 14 : ℝ) ^ 2 := by
        nlinarith [mul_nonneg
          (show 0 ≤ (5 / 14 : ℝ) - v by linarith)
          (show 0 ≤ (5 / 14 : ℝ) + v by linarith)]
      have hformula : q21 (-U) v = 5 / 4 + 21 / 5 * v ^ 2 := by
        dsimp [q21, U]
        ring
      have hqu : q21 (u - 1) v ≤ q21 (-U) v := by
        dsimp [q21] at *
        dsimp [W] at hmono
        nlinarith [hmono]
      rw [hformula] at hqu
      nlinarith
    · let U : ℝ := 1 - v
      have hWU : W ≤ U := by dsimp [W, U]; linarith
      have hfac : 0 ≤ 5 * (U + W) - 4 * v := by
        dsimp [U]
        linarith
      have hmono := mul_nonneg (sub_nonneg.mpr hWU) hfac
      have hformula : q21 (-U) v = 5 - 14 * v + 14 * v ^ 2 := by
        dsimp [q21, U]
        ring
      have hqu : q21 (u - 1) v ≤ q21 (-U) v := by
        dsimp [q21] at *
        dsimp [W] at hmono
        nlinarith [hmono]
      have hvlo : 5 / 14 ≤ v := le_of_lt (lt_of_not_ge hv5)
      have hvhi : v ≤ 9 / 14 := by linarith
      have hprod := mul_nonneg (sub_nonneg.mpr hvlo) (sub_nonneg.mpr hvhi)
      rw [hformula] at hqu
      nlinarith

private theorem q21_box_cover {u v : ℝ}
    (hu : |u| ≤ 1 / 2) (hv : |v| ≤ 1 / 2) :
    ∃ z : IntegralPoint,
      q21 (u - (z.1 : ℝ)) (v - (z.2 : ℝ)) ≤ 25 / 14 := by
  have huAbs := abs_le.mp hu
  have hvAbs := abs_le.mp hv
  by_cases hu0 : 0 ≤ u
  · by_cases hv0 : 0 ≤ v
    · by_cases huv : v ≤ u
      · rcases q21_positive_triangle hu0 huAbs.2 hv0 huv with h | h
        · exact ⟨(0, 0), by simpa using h⟩
        · exact ⟨(1, 0), by simpa using h⟩
      · have h := q21_positive_triangle hv0 hvAbs.2 hu0 (le_of_lt (lt_of_not_ge huv))
        rcases h with h | h
        · refine ⟨(0, 0), ?_⟩
          dsimp [q21] at h ⊢
          nlinarith [h]
        · refine ⟨(0, 1), ?_⟩
          dsimp [q21] at h ⊢
          nlinarith [h]
    · have hv0' : 0 ≤ -v := by linarith
      have hv1' : -v ≤ 1 / 2 := by linarith
      have h := q21_opposite_box hu0 huAbs.2 hv0' hv1'
      refine ⟨(0, 0), ?_⟩
      have : q21 u v ≤ 3 / 2 := by simpa using h
      simpa using (this.trans (by norm_num : (3 / 2 : ℝ) ≤ 25 / 14))
  · have hu0' : 0 ≤ -u := by linarith
    have hu1' : -u ≤ 1 / 2 := by linarith
    by_cases hv0 : 0 ≤ v
    · have h := q21_opposite_box hv0 hvAbs.2 hu0' hu1'
      refine ⟨(0, 0), ?_⟩
      have : q21 u v ≤ 3 / 2 := by
        dsimp [q21] at h ⊢
        nlinarith [h]
      simpa using (this.trans (by norm_num : (3 / 2 : ℝ) ≤ 25 / 14))
    · have hv0' : 0 ≤ -v := by linarith
      have hv1' : -v ≤ 1 / 2 := by linarith
      by_cases huv : -v ≤ -u
      · rcases q21_positive_triangle hu0' hu1' hv0' huv with h | h
        · refine ⟨(0, 0), ?_⟩
          simpa [q21] using h
        · refine ⟨(-1, 0), ?_⟩
          dsimp [q21] at h ⊢
          nlinarith [h]
      · have h := q21_positive_triangle hv0' hv1' hu0'
          (le_of_lt (lt_of_not_ge huv))
        rcases h with h | h
        · refine ⟨(0, 0), ?_⟩
          dsimp [q21] at h ⊢
          nlinarith [h]
        · refine ⟨(0, -1), ?_⟩
          dsimp [q21] at h ⊢
          nlinarith [h]

theorem v15_twenty_one_upper (x : PlanePoint ℝ) :
    ∃ z : IntegralPoint, v15TwentyOneCost x z ≤ 25 / 14 := by
  let a : ℤ := round x.1
  let b : ℤ := round x.2
  let u : ℝ := x.1 - (a : ℝ)
  let v : ℝ := x.2 - (b : ℝ)
  have hu : |u| ≤ 1 / 2 := by simpa [u, a] using abs_sub_round x.1
  have hv : |v| ≤ 1 / 2 := by simpa [v, b] using abs_sub_round x.2
  obtain ⟨z, hz⟩ := q21_box_cover hu hv
  refine ⟨(a + z.1, b + z.2), ?_⟩
  convert hz using 1 <;> simp [v15TwentyOneCost, u, v, q21] <;> ring

private theorem q21_integer_difference_nonneg (a b : ℤ) :
    0 ≤ 5 * (a : ℝ) ^ 2 + 4 * (a : ℝ) * b + 5 * (b : ℝ) ^ 2 -
      5 * (a : ℝ) - 5 * (b : ℝ) := by
  let s : ℤ := a + b
  have hid : 5 * (a : ℝ) ^ 2 + 4 * (a : ℝ) * b + 5 * (b : ℝ) ^ 2 -
        5 * (a : ℝ) - 5 * (b : ℝ) =
      (7 / 2 : ℝ) * (s : ℝ) ^ 2 +
        (3 / 2 : ℝ) * ((a : ℝ) - b) ^ 2 - 5 * (s : ℝ) := by
    dsimp [s]
    push_cast
    ring
  rw [hid]
  have hs : s ≤ 0 ∨ s = 1 ∨ 2 ≤ s := by omega
  rcases hs with hs | hs | hs
  · have hs' : (s : ℝ) ≤ 0 := by exact_mod_cast hs
    nlinarith [sq_nonneg (s : ℝ), sq_nonneg ((a : ℝ) - b)]
  · have hd : a - b ≤ -1 ∨ 1 ≤ a - b := by dsimp [s] at hs; omega
    rcases hd with hd | hd
    · have hd' : (a : ℝ) - b ≤ -1 := by exact_mod_cast hd
      have hdSq : (1 : ℝ) ≤ ((a : ℝ) - b) ^ 2 := by nlinarith
      simp only [hs, Int.cast_one]
      nlinarith
    · have hd' : (1 : ℝ) ≤ (a : ℝ) - b := by exact_mod_cast hd
      have hdSq : (1 : ℝ) ≤ ((a : ℝ) - b) ^ 2 := by nlinarith
      simp only [hs, Int.cast_one]
      nlinarith
  · have hs' : (2 : ℝ) ≤ s := by exact_mod_cast hs
    have hprod : 0 ≤ (s : ℝ) * ((s : ℝ) - 2) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [sq_nonneg ((a : ℝ) - b)]

theorem v15_twenty_one_vertex_lower (z : IntegralPoint) :
    (25 / 14 : ℝ) ≤ v15TwentyOneCost (5 / 14, 5 / 14) z := by
  have h := q21_integer_difference_nonneg z.1 z.2
  dsimp [v15TwentyOneCost, q21]
  nlinarith

/-- The `(5,2,5)` candidate has exact squared covering radius `25/14`. -/
theorem v15_twenty_one_exact_radius :
    SquaredCoveringRadiusSpecOver v15TwentyOneCost (25 / 14 : ℝ) := by
  constructor
  · exact v15_twenty_one_upper
  · intro r hr
    exact ⟨(5 / 14, 5 / 14), fun z ↦ hr.trans_le (v15_twenty_one_vertex_lower z)⟩

private theorem radius_spec_scale {X Y : Type*} {cost : X → Y → ℝ}
    {r : ℝ} (h : SquaredCoveringRadiusSpecOver cost r)
    (c : ℝ) (hc : 0 < c) :
    SquaredCoveringRadiusSpecOver (fun x y ↦ c * cost x y) (c * r) := by
  constructor
  · intro x
    obtain ⟨y, hy⟩ := h.upper x
    exact ⟨y, mul_le_mul_of_nonneg_left hy (le_of_lt hc)⟩
  · intro s hs
    have hs' : s / c < r := (div_lt_iff₀ hc).2 (by nlinarith)
    obtain ⟨x, hx⟩ := h.sharp (s / c) hs'
    refine ⟨x, fun y ↦ ?_⟩
    have hy := hx y
    have := mul_lt_mul_of_pos_left hy hc
    have hid : s / c * c = s := by field_simp [ne_of_gt hc]
    nlinarith

private theorem radius_spec_congr {X Y : Type*}
    {f g : X → Y → ℝ} {r s : ℝ}
    (h : SquaredCoveringRadiusSpecOver f r)
    (hfg : ∀ x y, f x y = g x y) (hrs : r = s) :
    SquaredCoveringRadiusSpecOver g s := by
  have hf : f = g := by funext x y; exact hfg x y
  simpa only [← hf, ← hrs] using h

/-- Each of the six surviving reduced trace Gram forms has its exact squared
covering radius on the full real plane, with all integer translates allowed. -/
theorem v15_six_exact_covering_radii :
    SquaredCoveringRadiusSpecOver (v15GramCost 2 0 4) (3 / 2 : ℝ) ∧
    SquaredCoveringRadiusSpecOver (v15GramCost 4 2 4) (4 / 3 : ℝ) ∧
    SquaredCoveringRadiusSpecOver (v15GramCost 2 1 3) (9 / 10 : ℝ) ∧
    SquaredCoveringRadiusSpecOver (v15GramCost 4 2 6) (9 / 5 : ℝ) ∧
    SquaredCoveringRadiusSpecOver (v15GramCost 2 1 7) (49 / 26 : ℝ) ∧
    SquaredCoveringRadiusSpecOver (v15GramCost 5 2 5) (25 / 14 : ℝ) := by
  have h2 := caseI_exact_radius_over (K := ℝ) (m := (2 : ℝ)) (by norm_num)
  have h3 := caseII_exact_radius_over (K := ℝ) (m := (3 : ℝ)) (by norm_num)
  have h5 := caseII_exact_radius_over (K := ℝ) (m := (5 : ℝ)) (by norm_num)
  have h13 := caseII_exact_radius_over (K := ℝ) (m := (13 : ℝ)) (by norm_num)
  have h3two := radius_spec_scale h3 2 (by norm_num)
  have h5two := radius_spec_scale h5 2 (by norm_num)
  constructor
  · apply radius_spec_congr h2
    · intro x z
      dsimp [v15GramCost, caseICostOver]
      ring
    · norm_num [caseIRadiusSqOver]
  constructor
  · apply radius_spec_congr h3two
    · intro x z
      dsimp [v15GramCost, caseIICostOver]
      ring
    · norm_num [caseIIRadiusSqOver]
  constructor
  · apply radius_spec_congr h5
    · intro x z
      dsimp [v15GramCost, caseIICostOver]
      ring
    · norm_num [caseIIRadiusSqOver]
  constructor
  · apply radius_spec_congr h5two
    · intro x z
      dsimp [v15GramCost, caseIICostOver]
      ring
    · norm_num [caseIIRadiusSqOver]
  constructor
  · apply radius_spec_congr h13
    · intro x z
      dsimp [v15GramCost, caseIICostOver]
      ring
    · norm_num [caseIIRadiusSqOver]
  · apply radius_spec_congr v15_twenty_one_exact_radius
    · intro x z
      dsimp [v15GramCost, v15TwentyOneCost, q21]
      ring
    · rfl

end

end TraceEuclidean
