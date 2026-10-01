import TraceEuclidean.GramEnumeration
import TraceEuclidean.QuadraticArithmetic

/-!
The finite discriminant and parity sieve in the proof of Theorem 1.7.
The inputs are the reduced trace Gram matrix and the standard quadratic-field
discriminant identity; no existence of a lattice is inferred from a candidate.
-/

namespace TraceEuclidean

def quadraticDiscriminant (m : ℕ) : ℕ :=
  if m % 4 = 1 then m else 4 * m

/-- The bounded square-free real-quadratic radicands. -/
theorem bounded_quadratic_radicands {m : ℕ}
    (hm : 1 < m) (hsq : IsSquarefreeNat m)
    (hdisc : quadraticDiscriminant m ≤ 21) :
    m = 2 ∨ m = 3 ∨ m = 5 ∨ m = 13 ∨ m = 17 ∨ m = 21 := by
  have hle : m ≤ 21 := by
    unfold quadraticDiscriminant at hdisc
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
  interval_cases m <;> simp_all [quadraticDiscriminant]

def QuadraticCandidate (m a b c n : ℕ) : Prop :=
  1 < m ∧ IsSquarefreeNat m ∧ AdmissibleGram a b c ∧ 0 < n ∧
    a * c - b ^ 2 = quadraticDiscriminant m * n ∧
    (m % 4 ≠ 1 → a % 2 = 0 ∧ b % 2 = 0 ∧ c % 2 = 0)

/-- The nine entries remaining after determinant divisibility and trace parity. -/
def nineCandidates : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(2, 2, 0, 4, 1), (3, 4, 2, 4, 1), (5, 2, 1, 3, 1),
   (5, 2, 0, 5, 2), (5, 4, 1, 4, 3), (5, 4, 2, 6, 4),
   (13, 2, 1, 7, 1), (17, 3, 1, 6, 1), (21, 5, 2, 5, 1)]

theorem nine_candidates_length : nineCandidates.length = 9 := by
  decide

set_option maxHeartbeats 1000000 in
-- Exhaustive arithmetic over twenty-two triples and six possible radicands.
theorem quadratic_candidate_mem {m a b c n : ℕ}
    (h : QuadraticCandidate m a b c n) :
    (m, a, b, c, n) ∈ nineCandidates := by
  rcases h with ⟨hm, hsq, hgram, hn, hdet, hpar⟩
  have hbound := gram_determinant_bounds hgram
  have hdiscpos : 0 < quadraticDiscriminant m := by
    unfold quadraticDiscriminant
    split <;> omega
  have hdiscle : quadraticDiscriminant m ≤ 21 := by
    have hmul : quadraticDiscriminant m ≤
        quadraticDiscriminant m * n := by
      calc
        quadraticDiscriminant m = quadraticDiscriminant m * 1 := by omega
        _ ≤ quadraticDiscriminant m * n := Nat.mul_le_mul_left _ hn
    omega
  have hmcase := bounded_quadratic_radicands hm hsq hdiscle
  have htrip := admissible_gram_mem hgram
  simp only [gramTriples, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at htrip
  simp only [nineCandidates, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq]
  rcases htrip with
    htrip | htrip | htrip | htrip | htrip | htrip | htrip | htrip |
    htrip | htrip | htrip | htrip | htrip | htrip | htrip | htrip |
    htrip | htrip | htrip | htrip | htrip | htrip <;>
    rcases htrip with ⟨rfl, rfl, rfl⟩ <;>
    rcases hmcase with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [quadraticDiscriminant] <;>
    omega

/-- The first trace/norm equation used to discard three of the nine rows. -/
def TraceNormCondition (m a n : ℕ) : Prop :=
  ∃ t : ℤ, ∃ k : ℕ, 0 < k ∧
    (a : ℤ) ^ 2 - (quadraticDiscriminant m : ℤ) * t ^ 2 =
      4 * (n : ℤ) * (k : ℤ) ^ 2

private theorem int_square_zero_or_ge_one (t : ℤ) :
    t ^ 2 = 0 ∨ 1 ≤ t ^ 2 := by
  by_cases ht : t = 0
  · left
    simp [ht]
  · right
    have hcase : t ≤ -1 ∨ 1 ≤ t := by omega
    rcases hcase with h | h <;> nlinarith

theorem exclude_five_two_two
    (h : TraceNormCondition 5 2 2) : False := by
  rcases h with ⟨t, k, hk, heq⟩
  have hkZ : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have hkSq : (1 : ℤ) ≤ (k : ℤ) ^ 2 := by nlinarith
  norm_num [quadraticDiscriminant] at heq
  nlinarith [sq_nonneg t]

theorem exclude_five_four_three
    (h : TraceNormCondition 5 4 3) : False := by
  rcases h with ⟨t, k, hk, heq⟩
  norm_num [quadraticDiscriminant] at heq
  have hkone : k = 1 := by
    by_contra hne
    have hk2 : (2 : ℤ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
    nlinarith [sq_nonneg t]
  subst k
  rcases int_square_zero_or_ge_one t with h0 | h1 <;> norm_num at heq <;> omega

theorem exclude_seventeen_three_one
    (h : TraceNormCondition 17 3 1) : False := by
  rcases h with ⟨t, k, hk, heq⟩
  norm_num [quadraticDiscriminant] at heq
  have hkone : k = 1 := by
    by_contra hne
    have hk2 : (2 : ℤ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
    nlinarith [sq_nonneg t]
  subst k
  rcases int_square_zero_or_ge_one t with h0 | h1 <;> norm_num at heq <;> omega

def sixSurvivingGrams : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(2, 2, 0, 4, 1), (3, 4, 2, 4, 1), (5, 2, 1, 3, 1),
   (5, 4, 2, 6, 4), (13, 2, 1, 7, 1), (21, 5, 2, 5, 1)]

theorem six_surviving_gram_length : sixSurvivingGrams.length = 6 := by
  decide

/-- The arithmetic sieve leaves exactly the six Gram rows used in the
classification proof. This is a necessary-condition theorem; realizing and
classifying lattices requires the remaining geometric and ideal arguments. -/
theorem quadratic_candidate_six_rows {m a b c n : ℕ}
    (h : QuadraticCandidate m a b c n)
    (htrace : TraceNormCondition m a n) :
    (m, a, b, c, n) ∈ sixSurvivingGrams := by
  have hmem := quadratic_candidate_mem h
  have hnot1 : (m, a, b, c, n) ≠ (5, 2, 0, 5, 2) := by
    intro he
    have hh : m = 5 ∧ a = 2 ∧ b = 0 ∧ c = 5 ∧ n = 2 := by
      simpa only [Prod.mk.injEq] using he
    rcases hh with ⟨rfl, rfl, _, _, rfl⟩
    exact exclude_five_two_two htrace
  have hnot2 : (m, a, b, c, n) ≠ (5, 4, 1, 4, 3) := by
    intro he
    have hh : m = 5 ∧ a = 4 ∧ b = 1 ∧ c = 4 ∧ n = 3 := by
      simpa only [Prod.mk.injEq] using he
    rcases hh with ⟨rfl, rfl, _, _, rfl⟩
    exact exclude_five_four_three htrace
  have hnot3 : (m, a, b, c, n) ≠ (17, 3, 1, 6, 1) := by
    intro he
    have hh : m = 17 ∧ a = 3 ∧ b = 1 ∧ c = 6 ∧ n = 1 := by
      simpa only [Prod.mk.injEq] using he
    rcases hh with ⟨rfl, rfl, _, _, rfl⟩
    exact exclude_seventeen_three_one htrace
  simp only [nineCandidates, List.mem_cons, List.not_mem_nil, or_false] at hmem
  simp only [sixSurvivingGrams, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem index_one_if_short_trace {m a n k : ℕ} {t : ℤ}
    (hn : 0 < n) (hk : 0 < k)
    (hshort : a ^ 2 < 16 * n)
    (heq : (a : ℤ) ^ 2 - (quadraticDiscriminant m : ℤ) * t ^ 2 =
      4 * (n : ℤ) * (k : ℤ) ^ 2) :
    k = 1 := by
  by_contra hne
  have hk2 : (2 : ℤ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
  have hmD : (0 : ℤ) ≤ quadraticDiscriminant m := by positivity
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  have hshortZ : (a : ℤ) ^ 2 < 16 * (n : ℤ) := by exact_mod_cast hshort
  nlinarith [sq_nonneg t, sq_nonneg ((k : ℤ) - 2)]

/-- For every surviving row except `m=3`, the first ideal index equals one.
The exceptional row requires both basis vectors and their cross trace. -/
theorem survivor_first_index_one_except_three
    {m a b c n : ℕ} {t : ℤ} {k : ℕ}
    (hrow : (m, a, b, c, n) ∈ sixSurvivingGrams)
    (hm3 : m ≠ 3) (hk : 0 < k)
    (heq : (a : ℤ) ^ 2 - (quadraticDiscriminant m : ℤ) * t ^ 2 =
      4 * (n : ℤ) * (k : ℤ) ^ 2) :
    k = 1 := by
  simp only [sixSurvivingGrams, List.mem_cons, List.not_mem_nil,
    or_false, Prod.mk.injEq] at hrow
  rcases hrow with h | h | h | h | h | h
  · rcases h with ⟨rfl, rfl, _, _, rfl⟩
    exact index_one_if_short_trace (by omega) hk
      (by norm_num) heq
  · exact (hm3 h.1).elim
  · rcases h with ⟨rfl, rfl, _, _, rfl⟩
    exact index_one_if_short_trace (by omega) hk
      (by norm_num) heq
  · rcases h with ⟨rfl, rfl, _, _, rfl⟩
    exact index_one_if_short_trace (by omega) hk
      (by norm_num) heq
  · rcases h with ⟨rfl, rfl, _, _, rfl⟩
    exact index_one_if_short_trace (by omega) hk
      (by norm_num) heq
  · rcases h with ⟨rfl, rfl, _, _, rfl⟩
    have hk_le_two : k ≤ 2 := by
      by_contra hnot
      have hk3 : (3 : ℤ) ≤ k := by exact_mod_cast (show 3 ≤ k by omega)
      norm_num [quadraticDiscriminant] at heq
      nlinarith [sq_nonneg t]
    have hk_case : k = 1 ∨ k = 2 := by omega
    rcases hk_case with h1 | h2
    · exact h1
    · subst k
      norm_num [quadraticDiscriminant] at heq
      rcases int_square_zero_or_ge_one t with ht0 | ht1 <;> omega

/-- The exceptional `m=3` row permits exactly the three first-vector
trace/norm/index solutions recorded in the manuscript. A separate two-vector
lemma below forces one index to be one after the coordinate bridge. -/
theorem m_three_trace_norm_solutions {t : ℤ} {k : ℕ}
    (hk : 0 < k)
    (heq : (4 : ℤ) ^ 2 - (quadraticDiscriminant 3 : ℤ) * t ^ 2 =
      4 * (1 : ℤ) * (k : ℤ) ^ 2) :
    (t = -1 ∧ k = 1) ∨ (t = 1 ∧ k = 1) ∨ (t = 0 ∧ k = 2) := by
  have hcase : t ≤ -2 ∨ t = -1 ∨ t = 0 ∨ t = 1 ∨ 2 ≤ t := by omega
  rcases hcase with ht | ht | ht | ht | ht
  · norm_num [quadraticDiscriminant] at heq
    nlinarith

  · subst t
    norm_num [quadraticDiscriminant] at heq
    have hkone : k = 1 := by
      by_contra hne
      have hk2 : (2 : ℤ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
      omega
    exact Or.inl ⟨rfl, hkone⟩
  · subst t
    norm_num [quadraticDiscriminant] at heq
    have hktwo : k = 2 := by
      by_contra hne
      have hcase : k = 1 ∨ 3 ≤ k := by omega
      rcases hcase with h1 | h3
      · subst k
        norm_num at heq
      · have hk3 : (3 : ℤ) ≤ k := by exact_mod_cast h3
        nlinarith
    exact Or.inr (Or.inr ⟨rfl, hktwo⟩)
  · subst t
    norm_num [quadraticDiscriminant] at heq
    have hkone : k = 1 := by
      by_contra hne
      have hk2 : (2 : ℤ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
      omega
    exact Or.inr (Or.inl ⟨rfl, hkone⟩)
  · norm_num [quadraticDiscriminant] at heq
    nlinarith

/-- The second-basis step in the exceptional `m=3` row. The zero-trace
hypotheses express `bᵢ = aβᵢ² = 2`; no principality is assumed. -/
theorem m_three_basis_forces_one_index_one
    {F : Type*} [Field F]
    {a β₁ β₂ : F} {t₁ t₂ : ℤ} {k₁ k₂ : ℕ}
    (ha : a ≠ 0) (hβ₁ : β₁ ≠ β₂) (hβ₂ : β₁ ≠ -β₂)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (heq₁ : (4 : ℤ) ^ 2 - (quadraticDiscriminant 3 : ℤ) * t₁ ^ 2 =
      4 * (1 : ℤ) * (k₁ : ℤ) ^ 2)
    (heq₂ : (4 : ℤ) ^ 2 - (quadraticDiscriminant 3 : ℤ) * t₂ ^ 2 =
      4 * (1 : ℤ) * (k₂ : ℤ) ^ 2)
    (hzero₁ : t₁ = 0 → a * β₁ ^ 2 = 2)
    (hzero₂ : t₂ = 0 → a * β₂ ^ 2 = 2) :
    k₁ = 1 ∨ k₂ = 1 := by
  have hs₁ := m_three_trace_norm_solutions hk₁ heq₁
  have hs₂ := m_three_trace_norm_solutions hk₂ heq₂
  by_contra hnot
  have hne₁ : k₁ ≠ 1 := by aesop
  have hne₂ : k₂ ≠ 1 := by aesop
  have ht₁ : t₁ = 0 := by rcases hs₁ with h | h | h <;> aesop
  have ht₂ : t₂ = 0 := by rcases hs₂ with h | h | h <;> aesop
  have hsq : β₁ ^ 2 = β₂ ^ 2 := by
    apply mul_left_cancel₀ ha
    exact (hzero₁ ht₁).trans (hzero₂ ht₂).symm
  have hfactor : (β₁ - β₂) * (β₁ + β₂) = 0 := by
    calc
      (β₁ - β₂) * (β₁ + β₂) = β₁ ^ 2 - β₂ ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr hsq
  rcases mul_eq_zero.mp hfactor with h | h
  · exact hβ₁ (sub_eq_zero.mp h)
  · exact hβ₂ (eq_neg_of_add_eq_zero_left h)

end TraceEuclidean
