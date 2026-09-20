import TraceEuclidean.V15GramEnumeration
import TraceEuclidean.QuadraticArithmetic

/-!
The finite discriminant and parity sieve in the proof of Theorem 1.7.
The inputs are the reduced trace Gram matrix and the standard quadratic-field
discriminant identity; no existence of a lattice is inferred from a candidate.
-/

namespace TraceEuclidean

def v15QuadraticDiscriminant (m : ℕ) : ℕ :=
  if m % 4 = 1 then m else 4 * m

/-- The bounded square-free real-quadratic radicands. -/
theorem v15_bounded_quadratic_radicands {m : ℕ}
    (hm : 1 < m) (hsq : IsSquarefreeNat m)
    (hdisc : v15QuadraticDiscriminant m ≤ 21) :
    m = 2 ∨ m = 3 ∨ m = 5 ∨ m = 13 ∨ m = 17 ∨ m = 21 := by
  have hle : m ≤ 21 := by
    unfold v15QuadraticDiscriminant at hdisc
    split at hdisc
    · omega
    · omega
  have h4 : m ≠ 4 := by
    intro h
    subst m
    have := hsq 2 (by norm_num)
    norm_num at this
  have h8 : m ≠ 8 := by
    intro h
    subst m
    have := hsq 2 (by norm_num)
    norm_num at this
  have h9 : m ≠ 9 := squarefreeNat_ne_nine hsq
  have h12 : m ≠ 12 := by
    intro h
    subst m
    have := hsq 2 (by norm_num)
    norm_num at this
  have h16 : m ≠ 16 := by
    intro h
    subst m
    have := hsq 2 (by norm_num)
    norm_num at this
  have h20 : m ≠ 20 := by
    intro h
    subst m
    have := hsq 2 (by norm_num)
    norm_num at this
  interval_cases m <;> simp_all [v15QuadraticDiscriminant]

def V15QuadraticCandidate (m a b c n : ℕ) : Prop :=
  1 < m ∧ IsSquarefreeNat m ∧ V15AdmissibleGram a b c ∧ 0 < n ∧
    a * c - b ^ 2 = v15QuadraticDiscriminant m * n ∧
    (m % 4 ≠ 1 → a % 2 = 0 ∧ b % 2 = 0 ∧ c % 2 = 0)

/-- The nine entries remaining after determinant divisibility and trace parity. -/
def v15NineCandidates : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(2, 2, 0, 4, 1), (3, 4, 2, 4, 1), (5, 2, 1, 3, 1),
   (5, 2, 0, 5, 2), (5, 4, 1, 4, 3), (5, 4, 2, 6, 4),
   (13, 2, 1, 7, 1), (17, 3, 1, 6, 1), (21, 5, 2, 5, 1)]

theorem v15_nine_candidates_length : v15NineCandidates.length = 9 := by
  decide

set_option maxHeartbeats 1000000 in
-- Exhaustive arithmetic over twenty-two triples and six possible radicands.
theorem v15_quadratic_candidate_mem {m a b c n : ℕ}
    (h : V15QuadraticCandidate m a b c n) :
    (m, a, b, c, n) ∈ v15NineCandidates := by
  rcases h with ⟨hm, hsq, hgram, hn, hdet, hpar⟩
  have hbound := v15_gram_determinant_bounds hgram
  have hdiscpos : 0 < v15QuadraticDiscriminant m := by
    unfold v15QuadraticDiscriminant
    split <;> omega
  have hdiscle : v15QuadraticDiscriminant m ≤ 21 := by
    have hmul : v15QuadraticDiscriminant m ≤
        v15QuadraticDiscriminant m * n := by
      calc
        v15QuadraticDiscriminant m = v15QuadraticDiscriminant m * 1 := by omega
        _ ≤ v15QuadraticDiscriminant m * n := Nat.mul_le_mul_left _ hn
    omega
  have hmcase := v15_bounded_quadratic_radicands hm hsq hdiscle
  have htrip := v15_admissible_gram_mem hgram
  simp only [v15GramTriples, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at htrip
  simp only [v15NineCandidates, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq]
  rcases htrip with
    htrip | htrip | htrip | htrip | htrip | htrip | htrip | htrip |
    htrip | htrip | htrip | htrip | htrip | htrip | htrip | htrip |
    htrip | htrip | htrip | htrip | htrip | htrip <;>
    rcases htrip with ⟨rfl, rfl, rfl⟩ <;>
    rcases hmcase with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [v15QuadraticDiscriminant] <;>
    omega

/-- The first trace/norm equation used to discard three of the nine rows. -/
def V15TraceNormCondition (m a n : ℕ) : Prop :=
  ∃ t : ℤ, ∃ k : ℕ, 0 < k ∧
    (a : ℤ) ^ 2 - (v15QuadraticDiscriminant m : ℤ) * t ^ 2 =
      4 * (n : ℤ) * (k : ℤ) ^ 2

private theorem int_square_zero_or_ge_one (t : ℤ) :
    t ^ 2 = 0 ∨ 1 ≤ t ^ 2 := by
  by_cases ht : t = 0
  · left
    simp [ht]
  · right
    have hcase : t ≤ -1 ∨ 1 ≤ t := by omega
    rcases hcase with h | h <;> nlinarith

theorem v15_exclude_five_two_two
    (h : V15TraceNormCondition 5 2 2) : False := by
  rcases h with ⟨t, k, hk, heq⟩
  have hkZ : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have hkSq : (1 : ℤ) ≤ (k : ℤ) ^ 2 := by nlinarith
  norm_num [v15QuadraticDiscriminant] at heq
  nlinarith [sq_nonneg t]

theorem v15_exclude_five_four_three
    (h : V15TraceNormCondition 5 4 3) : False := by
  rcases h with ⟨t, k, hk, heq⟩
  norm_num [v15QuadraticDiscriminant] at heq
  have hkone : k = 1 := by
    by_contra hne
    have hk2 : (2 : ℤ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
    nlinarith [sq_nonneg t]
  subst k
  rcases int_square_zero_or_ge_one t with h0 | h1 <;> norm_num at heq <;> omega

theorem v15_exclude_seventeen_three_one
    (h : V15TraceNormCondition 17 3 1) : False := by
  rcases h with ⟨t, k, hk, heq⟩
  norm_num [v15QuadraticDiscriminant] at heq
  have hkone : k = 1 := by
    by_contra hne
    have hk2 : (2 : ℤ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
    nlinarith [sq_nonneg t]
  subst k
  rcases int_square_zero_or_ge_one t with h0 | h1 <;> norm_num at heq <;> omega

def v15SixSurvivingGrams : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(2, 2, 0, 4, 1), (3, 4, 2, 4, 1), (5, 2, 1, 3, 1),
   (5, 4, 2, 6, 4), (13, 2, 1, 7, 1), (21, 5, 2, 5, 1)]

theorem v15_six_surviving_gram_length : v15SixSurvivingGrams.length = 6 := by
  decide

/-- The arithmetic sieve leaves exactly the six Gram rows used in the
classification proof. This is a necessary-condition theorem; realizing and
classifying lattices requires the remaining geometric and ideal arguments. -/
theorem v15_quadratic_candidate_six_rows {m a b c n : ℕ}
    (h : V15QuadraticCandidate m a b c n)
    (htrace : V15TraceNormCondition m a n) :
    (m, a, b, c, n) ∈ v15SixSurvivingGrams := by
  have hmem := v15_quadratic_candidate_mem h
  have hnot1 : (m, a, b, c, n) ≠ (5, 2, 0, 5, 2) := by
    intro he
    have hh : m = 5 ∧ a = 2 ∧ b = 0 ∧ c = 5 ∧ n = 2 := by
      simpa only [Prod.mk.injEq] using he
    rcases hh with ⟨rfl, rfl, _, _, rfl⟩
    exact v15_exclude_five_two_two htrace
  have hnot2 : (m, a, b, c, n) ≠ (5, 4, 1, 4, 3) := by
    intro he
    have hh : m = 5 ∧ a = 4 ∧ b = 1 ∧ c = 4 ∧ n = 3 := by
      simpa only [Prod.mk.injEq] using he
    rcases hh with ⟨rfl, rfl, _, _, rfl⟩
    exact v15_exclude_five_four_three htrace
  have hnot3 : (m, a, b, c, n) ≠ (17, 3, 1, 6, 1) := by
    intro he
    have hh : m = 17 ∧ a = 3 ∧ b = 1 ∧ c = 6 ∧ n = 1 := by
      simpa only [Prod.mk.injEq] using he
    rcases hh with ⟨rfl, rfl, _, _, rfl⟩
    exact v15_exclude_seventeen_three_one htrace
  simp only [v15NineCandidates, List.mem_cons, List.not_mem_nil, or_false] at hmem
  simp only [v15SixSurvivingGrams, List.mem_cons, List.not_mem_nil, or_false]
  tauto

end TraceEuclidean
