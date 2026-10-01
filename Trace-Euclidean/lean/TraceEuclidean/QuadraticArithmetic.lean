import Mathlib

/-!
Arithmetic endgame of the real-quadratic classification.  The geometric
covering-radius formula is verified separately up to its Voronoi-cell input.
-/

namespace TraceEuclidean

def caseIRadiusSq (m : ℕ) : ℚ := (m + 1 : ℚ) / 2

def caseIIRadiusSq (m : ℕ) : ℚ := (m + 1 : ℚ) ^ 2 / (8 * m)

/-- Elementary square-free predicate sufficient for the bounded case split. -/
def IsSquarefreeNat (m : ℕ) : Prop :=
  ∀ k : ℕ, k * k ∣ m → k = 1

theorem squarefreeNat_ne_nine {m : ℕ} (hsq : IsSquarefreeNat m) : m ≠ 9 := by
  intro hm
  subst m
  have hdiv : 3 * 3 ∣ (9 : ℕ) := by norm_num
  have := hsq 3 hdiv
  norm_num at this

theorem caseI_closed_candidates {m : ℕ} (hm : 1 < m)
    (hρ : caseIRadiusSq m ≤ 2) : m = 2 ∨ m = 3 := by
  have hmle : m ≤ 3 := by
    unfold caseIRadiusSq at hρ
    have hmleq : (m : ℚ) ≤ 3 := by linarith
    exact_mod_cast hmleq
  omega

theorem caseII_polynomial_bound {m : ℕ} (hm : 0 < m)
    (hρ : caseIIRadiusSq m ≤ 2) :
    (m : ℚ) ^ 2 - 14 * m + 1 ≤ 0 := by
  unfold caseIIRadiusSq at hρ
  have hmq : (0 : ℚ) < m := by exact_mod_cast hm
  have hmne : (m : ℚ) ≠ 0 := ne_of_gt hmq
  field_simp [hmne] at hρ
  nlinarith

theorem caseII_le_thirteen {m : ℕ} (hm : 0 < m)
    (hρ : caseIIRadiusSq m ≤ 2) : m ≤ 13 := by
  have hpoly := caseII_polynomial_bound hm hρ
  by_contra hnot
  have h14 : 14 ≤ m := by omega
  have hmq : (0 : ℚ) ≤ m := by positivity
  have h14q : (14 : ℚ) ≤ m := by exact_mod_cast h14
  have hprod : 0 ≤ (m : ℚ) * ((m : ℚ) - 14) :=
    mul_nonneg hmq (sub_nonneg.mpr h14q)
  nlinarith

theorem caseII_closed_candidates {m : ℕ} (hm : 1 < m)
    (hsq : IsSquarefreeNat m) (hmod : m % 4 = 1)
    (hρ : caseIIRadiusSq m ≤ 2) : m = 5 ∨ m = 13 := by
  have hmle : m ≤ 13 := caseII_le_thirteen (by omega) hρ
  have hnine : m ≠ 9 := squarefreeNat_ne_nine hsq
  omega

theorem halfIntegerSquare_ge_quarter (a : ℤ) :
    (1 / 2 - (a : ℚ)) ^ 2 ≥ 1 / 4 := by
  have ha : a ≤ 0 ∨ 1 ≤ a := by omega
  rcases ha with ha | ha
  · have haq : (a : ℚ) ≤ 0 := by exact_mod_cast ha
    nlinarith [sq_nonneg (1 / 2 - (a : ℚ))]
  · have haq : (1 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith [sq_nonneg (1 / 2 - (a : ℚ))]

/-- The explicit midpoint used to exclude `m = 3` has cost at least two. -/
theorem mThree_midpoint_obstruction (a b : ℤ) :
    2 * (1 / 2 - (a : ℚ)) ^ 2 + 6 * (1 / 2 - (b : ℚ)) ^ 2 ≥ 2 := by
  nlinarith [halfIntegerSquare_ge_quarter a, halfIntegerSquare_ge_quarter b]

theorem radiusSq_two : caseIRadiusSq 2 = 3 / 2 := by
  norm_num [caseIRadiusSq]

theorem radiusSq_five : caseIIRadiusSq 5 = 9 / 10 := by
  norm_num [caseIIRadiusSq]

theorem radiusSq_thirteen : caseIIRadiusSq 13 = 49 / 26 := by
  norm_num [caseIIRadiusSq]

theorem candidateRadii_strictlyBelowTwo :
    caseIRadiusSq 2 < 2 ∧ caseIIRadiusSq 5 < 2 ∧ caseIIRadiusSq 13 < 2 := by
  norm_num [caseIRadiusSq, caseIIRadiusSq]

end TraceEuclidean
