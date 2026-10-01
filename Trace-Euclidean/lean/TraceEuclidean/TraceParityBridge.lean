import TraceEuclidean.IdealSieveBridge

/-!
The trace parity condition in the quadratic arithmetic sieve comes from
actual integral values of an arbitrary fractional-ideal lattice.
-/

namespace TraceEuclidean

open scoped NumberField nonZeroDivisors

noncomputable section

theorem integral_trace_even_caseI
    {m : ℕ} (hm : 1 < m) (hsq : IsSquarefreeNat m)
    (hmod : m % 4 = 2 ∨ m % 4 = 3) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare hm hsq⟩
    ∀ z : RealQuadraticAlgebra m,
      IsIntegral ℤ z → ∃ t : ℤ,
        Algebra.trace ℚ (RealQuadraticAlgebra m) z = 2 * (t : ℚ) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  intro z hz
  obtain ⟨t, u, ht, hu⟩ := integral_coordinates_caseI hsq hmod hz
  exact ⟨t, by rw [realQuadratic_trace, ht]⟩

/-- In the `m ≡ 2,3 (mod 4)` cases, every entry of the actual ideal trace
Gram matrix is even, including its off-diagonal entry. -/
theorem actual_ideal_trace_gram_even
    {m a b c : ℕ} (hm : 1 < m) (hsq : IsSquarefreeNat m)
    (hmod : m % 4 = 2 ∨ m % 4 = 3) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare hm hsq⟩
    ∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra m)))
        (RealQuadraticAlgebra m)) (hI : I ≠ 0)
      (α : RealQuadraticAlgebra m),
      valueFractionalIdeal I α ≤ 1 →
      idealTraceGram I hI (QuadraticAlgebra.finrank_eq_two (m : ℚ) 0) α =
        ((a : ℚ), (b : ℚ), (c : ℚ)) →
      a % 2 = 0 ∧ b % 2 = 0 ∧ c % 2 = 0 := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  intro I hI α hintegral hGram
  let hd : Module.finrank ℚ (RealQuadraticAlgebra m) = 2 :=
    QuadraticAlgebra.finrank_eq_two (m : ℚ) 0
  let β₀ := idealFieldBasis I hI hd 0
  let β₁ := idealFieldBasis I hI hd 1
  have hmem (i : Fin 2) : idealFieldBasis I hI hd i ∈ I := by
    rw [ideal_field_basis_apply I hI hd i]
    exact (idealZBasis I hI hd i).2
  have hint (x y : Fin 2) :
      IsIntegral ℤ (α * idealFieldBasis I hI hd x *
        idealFieldBasis I hI hd y) :=
    value_integral_of_ideal_integral I α hintegral (hmem x) (hmem y)
  have hAint : IsIntegral ℤ (α * β₀ ^ 2) := by
    simpa only [pow_two, mul_assoc, β₀] using hint 0 0
  have hBint : IsIntegral ℤ (α * β₀ * β₁) := hint 0 1
  have hCint : IsIntegral ℤ (α * β₁ ^ 2) := by
    simpa only [pow_two, mul_assoc, β₁] using hint 1 1
  obtain ⟨tA, htA⟩ := integral_trace_even_caseI hm hsq hmod _ hAint
  obtain ⟨tB, htB⟩ := integral_trace_even_caseI hm hsq hmod _ hBint
  obtain ⟨tC, htC⟩ := integral_trace_even_caseI hm hsq hmod _ hCint
  have hA : (a : ℚ) = 2 * (tA : ℚ) := by
    have h := congrArg Prod.fst hGram
    dsimp [idealTraceGram] at h
    exact h.symm.trans htA
  have hB : (b : ℚ) = 2 * (tB : ℚ) := by
    have h := congrArg (fun z : ℚ × ℚ × ℚ ↦ z.2.1) hGram
    dsimp [idealTraceGram] at h
    exact h.symm.trans htB
  have hC : (c : ℚ) = 2 * (tC : ℚ) := by
    have h := congrArg (fun z : ℚ × ℚ × ℚ ↦ z.2.2) hGram
    dsimp [idealTraceGram] at h
    exact h.symm.trans htC
  have hAZ : (a : ℤ) = 2 * tA := by exact_mod_cast hA
  have hBZ : (b : ℤ) = 2 * tB := by exact_mod_cast hB
  have hCZ : (c : ℤ) = 2 * tC := by exact_mod_cast hC
  omega

end

end TraceEuclidean
