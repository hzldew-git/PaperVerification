import Mathlib

/-!
Exact reduced integral Gram enumeration from Theorem 1.7 of the frozen
Trace-Euclidean v15 manuscript. The bridge from an arbitrary rank-one ideal
lattice to these Gram conditions is a separate theorem obligation.
-/

namespace TraceEuclidean

/-- The strict reduced-Gram inequality equivalent to squared radius below two. -/
def V15AdmissibleGram (a b c : ℕ) : Prop :=
  2 ≤ a ∧ a ≤ c ∧ 2 * b ≤ a ∧
    (a : ℤ) * c * ((a : ℤ) + c - 2 * b) <
      8 * ((a : ℤ) * c - (b : ℤ) ^ 2)

/-- The manuscript's twenty-two candidate triples in its `A ≤ C` order. -/
def v15GramTriples : List (ℕ × ℕ × ℕ) :=
  [(2, 0, 2), (2, 0, 3), (2, 0, 4), (2, 0, 5),
   (2, 1, 2), (2, 1, 3), (2, 1, 4), (2, 1, 5), (2, 1, 6), (2, 1, 7),
   (3, 0, 3), (3, 0, 4), (3, 1, 3), (3, 1, 4), (3, 1, 5), (3, 1, 6),
   (4, 1, 4), (4, 1, 5), (4, 2, 4), (4, 2, 5), (4, 2, 6), (5, 2, 5)]

theorem v15_gram_c_le_seven {a b c : ℕ} (h : V15AdmissibleGram a b c) : c ≤ 7 := by
  rcases h with ⟨ha, hac, hba, hnum⟩
  have haZ : (2 : ℤ) ≤ a := by exact_mod_cast ha
  have hacZ : (a : ℤ) ≤ c := by exact_mod_cast hac
  have hbaZ : 2 * (b : ℤ) ≤ a := by exact_mod_cast hba
  have hb_lt_a : b < a := by omega
  have hbZ : (b : ℤ) < a := by exact_mod_cast hb_lt_a
  have hgap : 0 < ((a : ℤ) - b) * ((a : ℤ) + b) := by
    apply mul_pos
    · omega
    · omega
  have hmult : (a : ℤ) * a ≤ (a : ℤ) * c := by
    exact mul_le_mul_of_nonneg_left hacZ (by omega)
  have hdet : 0 < (a : ℤ) * c - (b : ℤ) ^ 2 := by
    nlinarith [hgap, hmult]
  have hsq : 0 ≤ (c : ℤ) * ((a : ℤ) - b) ^ 2 := by positivity
  have hcd : (c : ℤ) * ((a : ℤ) * c - (b : ℤ) ^ 2) <
      8 * ((a : ℤ) * c - (b : ℤ) ^ 2) := by
    nlinarith [hsq]
  by_contra hnot
  have hc8 : 8 ≤ c := by omega
  have hc8Z : (8 : ℤ) ≤ c := by exact_mod_cast hc8
  have hprod : 0 ≤ ((c : ℤ) - 8) * ((a : ℤ) * c - (b : ℤ) ^ 2) := by
    apply mul_nonneg
    · omega
    · omega
  nlinarith

/-- Every reduced Gram triple satisfying the strict paper inequality is in
the explicit finite list. The reverse inclusion is a finite decidable check. -/
theorem v15_admissible_gram_mem {a b c : ℕ} (h : V15AdmissibleGram a b c) :
    (a, b, c) ∈ v15GramTriples := by
  have hc : c ≤ 7 := v15_gram_c_le_seven h
  have ha : a ≤ 7 := le_trans h.2.1 hc
  have hba : 2 * b ≤ a := h.2.2.1
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
    norm_num [V15AdmissibleGram, v15GramTriples] at *

theorem v15_gram_mem_admissible {a b c : ℕ}
    (h : (a, b, c) ∈ v15GramTriples) : V15AdmissibleGram a b c := by
  have ha : a ≤ 5 := by
    simp [v15GramTriples] at h
    omega
  have hb : b ≤ 2 := by
    simp [v15GramTriples] at h
    omega
  have hc : c ≤ 7 := by
    simp [v15GramTriples] at h
    omega
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
    norm_num [v15GramTriples, V15AdmissibleGram] at *

theorem v15_admissible_gram_iff_mem {a b c : ℕ} :
    V15AdmissibleGram a b c ↔ (a, b, c) ∈ v15GramTriples :=
  ⟨v15_admissible_gram_mem, v15_gram_mem_admissible⟩

theorem v15_gram_list_length : v15GramTriples.length = 22 := by
  decide

/-- The determinant range used to bound the quadratic field discriminant. -/
theorem v15_gram_determinant_bounds {a b c : ℕ}
    (h : V15AdmissibleGram a b c) :
    0 < a * c - b ^ 2 ∧ a * c - b ^ 2 ≤ 21 := by
  have hc : c ≤ 7 := v15_gram_c_le_seven h
  have ha : a ≤ 7 := le_trans h.2.1 hc
  have hb : b ≤ 3 := by
    have hba : 2 * b ≤ a := h.2.2.1
    omega
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
    norm_num [V15AdmissibleGram] at *

end TraceEuclidean
