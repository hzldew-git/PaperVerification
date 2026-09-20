import TraceEuclidean.V15BinaryCriterion

/-!
The exact squared covering radius of every reduced positive binary trace Gram
form. The lower bound is the rational deep-hole theorem; the upper bound uses
the two triangles of a unit square and a barycentric average of vertex costs.
-/

namespace TraceEuclidean

noncomputable section

private def realGramForm (a b c : ℕ) (u v : ℝ) : ℝ :=
  (a : ℝ) * u ^ 2 + 2 * b * u * v + (c : ℝ) * v ^ 2

private def realGramDeepHole (a b c : ℕ) : PlanePoint ℝ :=
  ((c : ℝ) * ((a : ℝ) - b) /
      (2 * ((a : ℝ) * c - (b : ℝ) ^ 2)),
    (a : ℝ) * ((c : ℝ) - b) /
      (2 * ((a : ℝ) * c - (b : ℝ) ^ 2)))

private def realGramRadius (a b c : ℕ) : ℝ :=
  (a : ℝ) * c * ((a : ℝ) + c - 2 * b) /
    (4 * ((a : ℝ) * c - (b : ℝ) ^ 2))

private theorem realGramDet_pos {a b c : ℕ} (h : V15ReducedGram a b c) :
    0 < (a : ℝ) * c - (b : ℝ) ^ 2 := by
  rcases h with ⟨ha, hac, hba⟩
  have hab : b < a := by omega
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hb_lt : (b : ℝ) < a := by exact_mod_cast hab
  have hprod : 0 < ((a : ℝ) - b) * ((a : ℝ) + b) := by
    apply mul_pos
    · linarith
    · positivity
  have hacR : (a : ℝ) ≤ c := by exact_mod_cast hac
  have hmult : (a : ℝ) * a ≤ (a : ℝ) * c :=
    mul_le_mul_of_nonneg_left hacR ha0.le
  nlinarith

private theorem realGramForm_nonneg {a b c : ℕ}
    (h : V15ReducedGram a b c) (u v : ℝ) :
    0 ≤ realGramForm a b c u v := by
  have ha : (0 : ℝ) < a := by
    have haNat : 0 < a := by have h2 := h.1; omega
    exact_mod_cast haNat
  have hd := realGramDet_pos h
  have hid : (a : ℝ) * realGramForm a b c u v =
      ((a : ℝ) * u + b * v) ^ 2 +
        ((a : ℝ) * c - (b : ℝ) ^ 2) * v ^ 2 := by
    dsimp [realGramForm]
    ring
  have hmul : 0 ≤ (a : ℝ) * realGramForm a b c u v := by
    rw [hid]
    exact add_nonneg (sq_nonneg _) (mul_nonneg hd.le (sq_nonneg _))
  nlinarith

private theorem realGram_average_complete {a b c : ℕ}
    (h : V15ReducedGram a b c) (u v : ℝ) :
    (a : ℝ) * u + (c : ℝ) * v - realGramForm a b c u v =
      realGramRadius a b c -
        realGramForm a b c
          (u - (realGramDeepHole a b c).1)
          (v - (realGramDeepHole a b c).2) := by
  have hd : (a : ℝ) * c - (b : ℝ) ^ 2 ≠ 0 :=
    ne_of_gt (realGramDet_pos h)
  dsimp [realGramForm, realGramDeepHole, realGramRadius]
  field_simp [hd]
  ring

private theorem realGram_triangle_upper {a b c : ℕ}
    (h : V15ReducedGram a b c) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hsum : u + v ≤ 1) :
    ∃ z : IntegralPoint,
      realGramForm a b c (u - (z.1 : ℝ)) (v - (z.2 : ℝ)) ≤
        realGramRadius a b c := by
  let q₀ := realGramForm a b c u v
  let q₁ := realGramForm a b c (u - 1) v
  let q₂ := realGramForm a b c u (v - 1)
  let R := realGramRadius a b c
  have havg : (1 - u - v) * q₀ + u * q₁ + v * q₂ ≤ R := by
    have hid : (1 - u - v) * q₀ + u * q₁ + v * q₂ =
        (a : ℝ) * u + (c : ℝ) * v - realGramForm a b c u v := by
      dsimp [q₀, q₁, q₂, realGramForm]
      ring
    rw [hid, realGram_average_complete h]
    exact sub_le_self _ (realGramForm_nonneg h _ _)
  let m := min q₀ (min q₁ q₂)
  have hm₀ : 0 ≤ q₀ - m := sub_nonneg.mpr (min_le_left _ _)
  have hm₁ : 0 ≤ q₁ - m :=
    sub_nonneg.mpr ((min_le_right _ _).trans (min_le_left _ _))
  have hm₂ : 0 ≤ q₂ - m :=
    sub_nonneg.mpr ((min_le_right _ _).trans (min_le_right _ _))
  have hw : 0 ≤ 1 - u - v := by linarith
  have hp₀ := mul_nonneg hw hm₀
  have hp₁ := mul_nonneg hu hm₁
  have hp₂ := mul_nonneg hv hm₂
  have hm : m ≤ R := by nlinarith [havg, hp₀, hp₁, hp₂]
  change min q₀ (min q₁ q₂) ≤ R at hm
  simp only [min_le_iff] at hm
  rcases hm with h₀ | h₁ | h₂
  · exact ⟨(0, 0), by simpa [q₀] using h₀⟩
  · exact ⟨(1, 0), by simpa [q₁] using h₁⟩
  · exact ⟨(0, 1), by simpa [q₂] using h₂⟩

private theorem realGram_square_upper {a b c : ℕ}
    (h : V15ReducedGram a b c) {u v : ℝ}
    (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1) :
    ∃ z : IntegralPoint,
      realGramForm a b c (u - (z.1 : ℝ)) (v - (z.2 : ℝ)) ≤
        realGramRadius a b c := by
  by_cases htri : u + v ≤ 1
  · exact realGram_triangle_upper h hu₀ hv₀ htri
  · obtain ⟨z, hz⟩ := realGram_triangle_upper h
        (show 0 ≤ 1 - u by linarith)
        (show 0 ≤ 1 - v by linarith)
        (show (1 - u) + (1 - v) ≤ 1 by linarith)
    refine ⟨(1 - z.1, 1 - z.2), ?_⟩
    convert hz using 1
    dsimp [realGramForm]
    push_cast
    ring

private theorem realGram_upper {a b c : ℕ}
    (h : V15ReducedGram a b c) (x : PlanePoint ℝ) :
    ∃ z : IntegralPoint, v15GramCost a b c x z ≤ realGramRadius a b c := by
  let i : ℤ := ⌊x.1⌋
  let j : ℤ := ⌊x.2⌋
  let u : ℝ := x.1 - (i : ℝ)
  let v : ℝ := x.2 - (j : ℝ)
  have hu₀ : 0 ≤ u := by
    change 0 ≤ Int.fract x.1
    exact Int.fract_nonneg x.1
  have hu₁ : u ≤ 1 := by
    change Int.fract x.1 ≤ 1
    exact (Int.fract_lt_one x.1).le
  have hv₀ : 0 ≤ v := by
    change 0 ≤ Int.fract x.2
    exact Int.fract_nonneg x.2
  have hv₁ : v ≤ 1 := by
    change Int.fract x.2 ≤ 1
    exact (Int.fract_lt_one x.2).le
  obtain ⟨z, hz⟩ := realGram_square_upper h hu₀ hu₁ hv₀ hv₁
  refine ⟨(i + z.1, j + z.2), ?_⟩
  convert hz using 1
  dsimp [v15GramCost, realGramForm, u, v]
  push_cast
  ring

private theorem realGramRadius_cast (a b c : ℕ) :
    ((v15GramRadius a b c : ℚ) : ℝ) = realGramRadius a b c := by
  dsimp [v15GramRadius, realGramRadius]
  push_cast
  ring

private theorem realGramDeepHole_cast (a b c : ℕ) :
    (((v15RationalDeepHole a b c).1 : ℝ),
      ((v15RationalDeepHole a b c).2 : ℝ)) =
        realGramDeepHole a b c := by
  dsimp [v15RationalDeepHole, realGramDeepHole]
  push_cast
  rfl

/-- Every trace-relevant reduced integral binary Gram form (`2 ≤ a`) has the
exact squared covering radius stated in Proposition 6.1 on the real plane. -/
theorem v15_reduced_gram_exact_radius {a b c : ℕ}
    (h : V15ReducedGram a b c) :
    SquaredCoveringRadiusSpecOver (v15GramCost a b c)
      ((v15GramRadius a b c : ℚ) : ℝ) := by
  constructor
  · intro x
    obtain ⟨z, hz⟩ := realGram_upper h x
    exact ⟨z, by rw [realGramRadius_cast] ; exact hz⟩
  · intro r hr
    let p : PlanePoint ℝ :=
      (((v15RationalDeepHole a b c).1 : ℝ),
        ((v15RationalDeepHole a b c).2 : ℝ))
    refine ⟨p, fun z ↦ ?_⟩
    have hlo := v15_deep_hole_lower h z
    have hcast : ((v15GramCostRat a b c (v15RationalDeepHole a b c) z : ℚ) : ℝ) =
        v15GramCost a b c p z := by
      dsimp [v15GramCostRat, v15GramCost, p]
      push_cast
      ring
    have hreal : ((v15GramRadius a b c : ℚ) : ℝ) ≤
        v15GramCost a b c p z := by
      have hreal' : ((v15GramRadius a b c : ℚ) : ℝ) ≤
          ((v15GramCostRat a b c (v15RationalDeepHole a b c) z : ℚ) : ℝ) := by
        exact_mod_cast hlo
      rw [hcast] at hreal'
      exact hreal'
    exact hr.trans_le hreal

/-- The same radius formula for the rational ambient plane used by the
number-field lattice. The sharp point is already rational. -/
theorem v15_reduced_gram_exact_radius_rat {a b c : ℕ}
    (h : V15ReducedGram a b c) :
    SquaredCoveringRadiusSpecOver (v15GramCostRat a b c)
      (v15GramRadius a b c) := by
  constructor
  · intro x
    obtain ⟨z, hz⟩ :=
      (v15_reduced_gram_exact_radius h).upper ((x.1 : ℝ), (x.2 : ℝ))
    refine ⟨z, ?_⟩
    have hcast : ((v15GramCostRat a b c x z : ℚ) : ℝ) =
        v15GramCost a b c ((x.1 : ℝ), (x.2 : ℝ)) z := by
      dsimp [v15GramCostRat, v15GramCost]
      push_cast
      ring
    have hreal : ((v15GramCostRat a b c x z : ℚ) : ℝ) ≤
        ((v15GramRadius a b c : ℚ) : ℝ) := by
      rw [hcast]
      exact hz
    exact_mod_cast hreal
  · intro r hr
    exact ⟨v15RationalDeepHole a b c,
      fun z ↦ hr.trans_le (v15_deep_hole_lower h z)⟩

end

end TraceEuclidean
