import TraceEuclidean.QuadraticIntegralBasis
import TraceEuclidean.V15QuadraticSieve

/-!
The first-vector trace/norm equation in Theorem 1.7, derived from an actual
algebraic integer in the concrete real quadratic algebra.
-/

namespace TraceEuclidean

noncomputable section

/-- An integral quadratic-field element whose trace and norm have the values
used in the ideal sieve satisfies the exact discriminant equation. -/
theorem v15_trace_norm_equation_of_integral_element
    {m A n k : ℕ}
    (hm : 1 < m) (hsq : IsSquarefreeNat m) (hk : 0 < k) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare hm hsq⟩
    ∀ b : RealQuadraticAlgebra m,
      IsIntegral ℤ b →
      Algebra.trace ℚ (RealQuadraticAlgebra m) b = (A : ℚ) →
      Algebra.norm ℚ b = (n : ℚ) * (k : ℚ) ^ 2 →
      ∃ t : ℤ,
        (A : ℤ) ^ 2 - (v15QuadraticDiscriminant m : ℤ) * t ^ 2 =
          4 * (n : ℤ) * (k : ℤ) ^ 2 := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  intro b hb htrace hnorm
  have hA : (A : ℚ) = 2 * b.re :=
    htrace.symm.trans (realQuadratic_trace b)
  have hN : (n : ℚ) * (k : ℚ) ^ 2 =
      b.re ^ 2 - (m : ℚ) * b.im ^ 2 :=
    hnorm.symm.trans (realQuadratic_norm b)
  rcases squarefree_mod_four_cases hsq with hmod | hmod
  · obtain ⟨s, t, hs, ht⟩ := integral_coordinates_caseII hsq hmod hb
    refine ⟨t, ?_⟩
    have hD : v15QuadraticDiscriminant m = m := by
      simp [v15QuadraticDiscriminant, hmod]
    have hEqQ :
        (A : ℚ) ^ 2 - (v15QuadraticDiscriminant m : ℚ) * (t : ℚ) ^ 2 =
          4 * (n : ℚ) * (k : ℚ) ^ 2 := by
      rw [hD]
      rw [hs] at hA hN
      rw [ht] at hN
      nlinarith [congrArg (fun q : ℚ ↦ q ^ 2) hA]
    exact_mod_cast hEqQ
  · obtain ⟨s, t, hs, ht⟩ := integral_coordinates_caseI hsq hmod hb
    refine ⟨t, ?_⟩
    have hnot : m % 4 ≠ 1 := by omega
    have hD : v15QuadraticDiscriminant m = 4 * m := by
      simp [v15QuadraticDiscriminant, hnot]
    have hEqQ :
        (A : ℚ) ^ 2 - (v15QuadraticDiscriminant m : ℚ) * (t : ℚ) ^ 2 =
          4 * (n : ℚ) * (k : ℚ) ^ 2 := by
      rw [hD]
      rw [hs] at hA hN
      rw [ht] at hN
      push_cast
      nlinarith [congrArg (fun q : ℚ ↦ q ^ 2) hA]
    exact_mod_cast hEqQ

/-- The existential condition used by the arithmetic sieve follows from
the stronger equation with the same quotient-ideal index `k`. -/
theorem v15_trace_norm_condition_of_integral_element
    {m A n k : ℕ}
    (hm : 1 < m) (hsq : IsSquarefreeNat m) (hk : 0 < k) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare hm hsq⟩
    ∀ b : RealQuadraticAlgebra m,
      IsIntegral ℤ b →
      Algebra.trace ℚ (RealQuadraticAlgebra m) b = (A : ℚ) →
      Algebra.norm ℚ b = (n : ℚ) * (k : ℚ) ^ 2 →
      V15TraceNormCondition m A n := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  intro b hb htrace hnorm
  obtain ⟨t, ht⟩ :=
    v15_trace_norm_equation_of_integral_element hm hsq hk b hb htrace hnorm
  exact ⟨t, k, hk, ht⟩

end

end TraceEuclidean
