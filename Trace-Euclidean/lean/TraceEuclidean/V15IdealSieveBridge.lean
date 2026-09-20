import TraceEuclidean.V15IdealNormQuotient
import TraceEuclidean.V15TraceNormBridge

/-!
For an actual fractional-ideal presentation of a real quadratic lattice,
value integrality yields the arithmetic first-vector equation used in the
finite six-row sieve. No freeness of the ideal is assumed.
-/

namespace TraceEuclidean

open scoped NumberField nonZeroDivisors

noncomputable section

/-- A chosen basis vector of any nonzero fractional ideal has the trace/norm
equation of the paper. The same quotient-ideal index detects principality. -/
theorem v15_actual_ideal_vector_trace_norm
    {m a : ℕ} (hm : 1 < m) (hsq : IsSquarefreeNat m) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare hm hsq⟩
    ∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra m)))
        (RealQuadraticAlgebra m)) (hI : I ≠ 0)
      (α : RealQuadraticAlgebra m),
      0 < Algebra.norm ℚ α →
      v15ValueFractionalIdeal I α ≤ 1 →
      ∀ i : Fin 2,
        Algebra.trace ℚ (RealQuadraticAlgebra m)
            (α * (v15IdealFieldBasis I hI
              (QuadraticAlgebra.finrank_eq_two (m : ℚ) 0 :
                Module.finrank ℚ (RealQuadraticAlgebra m) = 2) i) ^ 2) = (a : ℚ) →
        ∃ n k : ℕ, ∃ t : ℤ,
          0 < n ∧ 0 < k ∧
          (n : ℚ) = |Algebra.norm ℚ α| * (FractionalIdeal.absNorm I) ^ 2 ∧
          Algebra.norm ℚ
            (α * (v15IdealFieldBasis I hI
              (QuadraticAlgebra.finrank_eq_two (m : ℚ) 0) i) ^ 2) =
                (n : ℚ) * (k : ℚ) ^ 2 ∧
          (a : ℤ) ^ 2 - (v15QuadraticDiscriminant m : ℤ) * t ^ 2 =
            4 * (n : ℤ) * (k : ℤ) ^ 2 ∧
          V15TraceNormCondition m a n ∧
          (k = 1 → I = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 _))
            (v15IdealFieldBasis I hI
              (QuadraticAlgebra.finrank_eq_two (m : ℚ) 0 :
                Module.finrank ℚ (RealQuadraticAlgebra m) = 2) i)) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  intro I hI α hαnorm hintegral i htrace
  let hdegree : Module.finrank ℚ (RealQuadraticAlgebra m) = 2 :=
    QuadraticAlgebra.finrank_eq_two (m : ℚ) 0
  let β := v15IdealFieldBasis I hI hdegree i
  have hβmem : β ∈ I := by
    change v15IdealFieldBasis I hI hdegree i ∈ I
    rw [v15_ideal_field_basis_apply I hI hdegree i]
    exact (v15IdealZBasis I hI hdegree i).2
  have hβ0 : β ≠ 0 :=
    (v15IdealFieldBasis I hI hdegree).linearIndependent.ne_zero i
  have hα0 : α ≠ 0 := by
    exact (Algebra.norm_ne_zero_iff).mp (ne_of_gt hαnorm)
  obtain ⟨n, hnpos, hn⟩ :=
    v15_value_ideal_positive_norm I hI α hα0 hintegral
  obtain ⟨k, hkpos, hnorm, hprincipal⟩ :=
    v15_ideal_vector_norm_index I hI α hαnorm n hn hβmem hβ0
  have hb : IsIntegral ℤ (α * β ^ 2) := by
    simpa only [pow_two, mul_assoc] using
      (v15_value_integral_of_ideal_integral I α hintegral hβmem hβmem)
  obtain ⟨t, heq⟩ :=
    v15_trace_norm_equation_of_integral_element hm hsq hkpos
      (α * β ^ 2) hb (by simpa only [β, hdegree] using htrace) hnorm
  exact ⟨n, k, t, hnpos, hkpos, hn, hnorm, heq,
    ⟨t, k, hkpos, heq⟩, hprincipal⟩

/-- The first reduced trace Gram entry of the ideal supplies the equation
needed to eliminate three arithmetic candidate rows. -/
theorem v15_actual_ideal_first_trace_norm
    {m a b c : ℕ} (hm : 1 < m) (hsq : IsSquarefreeNat m) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare hm hsq⟩
    ∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra m)))
        (RealQuadraticAlgebra m)) (hI : I ≠ 0)
      (α : RealQuadraticAlgebra m),
      0 < Algebra.norm ℚ α →
      v15ValueFractionalIdeal I α ≤ 1 →
      v15IdealTraceGram I hI (QuadraticAlgebra.finrank_eq_two (m : ℚ) 0) α =
        ((a : ℚ), (b : ℚ), (c : ℚ)) →
      ∃ n : ℕ,
        0 < n ∧
        (n : ℚ) = |Algebra.norm ℚ α| * (FractionalIdeal.absNorm I) ^ 2 ∧
        V15TraceNormCondition m a n := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  intro I hI α hαnorm hintegral hGram
  have htrace : Algebra.trace ℚ (RealQuadraticAlgebra m)
      (α * (v15IdealFieldBasis I hI
        (QuadraticAlgebra.finrank_eq_two (m : ℚ) 0) 0) ^ 2) =
      (a : ℚ) := by
    simpa only [v15IdealTraceGram] using congrArg Prod.fst hGram
  obtain ⟨n, k, t, hn, hk, hnorm, hβnorm, heq, hcond, hprincipal⟩ :=
    v15_actual_ideal_vector_trace_norm hm hsq I hI α hαnorm hintegral 0 htrace
  exact ⟨n, hn, hnorm, hcond⟩

end

end TraceEuclidean
