import TraceEuclidean.V15VariableDeterminant
import TraceEuclidean.V15QuadraticDiscriminant

/-!
The arithmetic sieve for a Gauss-reduced basis chosen inside an actual
fractional ideal, with no assumption that the ideal is principal.
-/

namespace TraceEuclidean

open Module
open scoped NumberField nonZeroDivisors

noncomputable section

/-- The trace of a nonzero positive integral quadratic value is at least two.
This supplies the lower bound missing from elementary Gauss reduction. -/
theorem v15_actual_ideal_trace_diagonal_ge_two
    {m : ℕ} (hm : 1 < m) (hsq : IsSquarefreeNat m) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare hm hsq⟩
    ∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra m)))
        (RealQuadraticAlgebra m)) (α : RealQuadraticAlgebra m),
      0 < Algebra.norm ℚ α →
      ∀ (hint : v15ValueFractionalIdeal I α ≤ 1),
        V15IdealTracePositive I α →
        ∀ x : I.coeToSubmodule, x ≠ 0 →
          2 ≤ v15IdealTraceNat I α hint x := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  intro I α hαnorm hint hpositive x hx0
  let β : RealQuadraticAlgebra m := x
  have hβ0 : β ≠ 0 := by
    intro h
    apply hx0
    apply Subtype.ext
    exact h
  have hβnorm0 : Algebra.norm ℚ β ≠ 0 :=
    (Algebra.norm_ne_zero_iff).mpr hβ0
  have hβnormSq : (0 : ℚ) < (Algebra.norm ℚ β) ^ 2 :=
    sq_pos_of_ne_zero hβnorm0
  let z := α * β ^ 2
  have hzNormPos : 0 < Algebra.norm ℚ z := by
    change 0 < Algebra.norm ℚ (α * β ^ 2)
    rw [map_mul, map_pow]
    exact mul_pos hαnorm hβnormSq
  have hzInt : IsIntegral ℤ z := by
    change IsIntegral ℤ (α * β ^ 2)
    simpa only [pow_two, mul_assoc] using
      (v15_value_integral_of_ideal_integral I α hint x.2 x.2)
  have hzNormInt : IsIntegral ℤ (Algebra.norm ℚ z) :=
    Algebra.isIntegral_norm ℚ hzInt
  obtain ⟨N, hN⟩ := IsIntegrallyClosed.isIntegral_iff.mp hzNormInt
  have hN' : (N : ℚ) = Algebra.norm ℚ z := by simpa using hN
  have hNposQ : (0 : ℚ) < N := by
    rw [hN']
    exact hzNormPos
  have hNpos : 0 < N := by exact_mod_cast hNposQ
  have hNge : (1 : ℚ) ≤ Algebra.norm ℚ z := by
    rw [← hN']
    exact_mod_cast (show (1 : ℤ) ≤ N by omega)
  have hmnonneg : (0 : ℚ) ≤ m := by positivity
  have hsqnonneg : 0 ≤ (m : ℚ) * z.im ^ 2 :=
    mul_nonneg hmnonneg (sq_nonneg _)
  have htraceSq : 4 * Algebra.norm ℚ z ≤
      (Algebra.trace ℚ (RealQuadraticAlgebra m) z) ^ 2 := by
    rw [realQuadratic_trace, realQuadratic_norm]
    nlinarith [hsqnonneg]
  have htraceNat : (v15IdealTraceNat I α hint x : ℚ) =
      Algebra.trace ℚ (RealQuadraticAlgebra m) z := by
    simpa only [z, β] using
      (v15_ideal_trace_nat_cast I α hint hpositive x)
  have hApos : (0 : ℚ) < v15IdealTraceNat I α hint x := by
    rw [htraceNat]
    change 0 < Algebra.trace ℚ (RealQuadraticAlgebra m)
      (α * (x : RealQuadraticAlgebra m) ^ 2)
    exact hpositive x hx0
  have hA2 : (4 : ℚ) ≤ (v15IdealTraceNat I α hint x : ℚ) ^ 2 := by
    rw [htraceNat]
    nlinarith [htraceSq, hNge]
  by_contra hnot
  have hAle : v15IdealTraceNat I α hint x ≤ 1 := by omega
  have hAleQ : (v15IdealTraceNat I α hint x : ℚ) ≤ 1 := by
    exact_mod_cast hAle
  nlinarith

/-- The trace/norm equation and quotient-ideal index of any nonzero ideal
vector. In particular, the index-one conclusion refers to the same `k` as
the equation. -/
theorem v15_actual_ideal_vector_equation
    {m a : ℕ} (hm : 1 < m) (hsq : IsSquarefreeNat m) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare hm hsq⟩
    ∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra m)))
        (RealQuadraticAlgebra m)) (hI : I ≠ 0)
      (α β : RealQuadraticAlgebra m),
      0 < Algebra.norm ℚ α →
      v15ValueFractionalIdeal I α ≤ 1 →
      β ∈ I → β ≠ 0 →
      Algebra.trace ℚ (RealQuadraticAlgebra m) (α * β ^ 2) = (a : ℚ) →
      ∃ n k : ℕ, ∃ t : ℤ,
        0 < n ∧ 0 < k ∧
        (n : ℚ) = |Algebra.norm ℚ α| * (FractionalIdeal.absNorm I) ^ 2 ∧
        Algebra.norm ℚ (α * β ^ 2) = (n : ℚ) * (k : ℚ) ^ 2 ∧
        (a : ℤ) ^ 2 - (v15QuadraticDiscriminant m : ℤ) * t ^ 2 =
          4 * (n : ℤ) * (k : ℤ) ^ 2 ∧
        (k = 1 → I = FractionalIdeal.spanSingleton
          (nonZeroDivisors (𝓞 (RealQuadraticAlgebra m))) β) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  intro I hI α β hαnorm hint hβmem hβ0 htrace
  have hα0 : α ≠ 0 :=
    (Algebra.norm_ne_zero_iff).mp (ne_of_gt hαnorm)
  obtain ⟨n, hnpos, hn⟩ :=
    v15_value_ideal_positive_norm I hI α hα0 hint
  obtain ⟨k, hkpos, hnorm, hprincipal⟩ :=
    v15_ideal_vector_norm_index I hI α hαnorm n hn hβmem hβ0
  have hb : IsIntegral ℤ (α * β ^ 2) := by
    simpa only [pow_two, mul_assoc] using
      (v15_value_integral_of_ideal_integral I α hint hβmem hβmem)
  obtain ⟨t, heq⟩ :=
    v15_trace_norm_equation_of_integral_element hm hsq hkpos
      (α * β ^ 2) hb htrace hnorm
  exact ⟨n, k, t, hnpos, hkpos, hn, hnorm, heq, hprincipal⟩

/-- Trace parity for the Gram matrix attached to any selected ideal basis. -/
theorem v15_actual_ideal_trace_gram_even_of
    {m a b c : ℕ} (hm : 1 < m) (hsq : IsSquarefreeNat m)
    (hmod : m % 4 = 2 ∨ m % 4 = 3) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare hm hsq⟩
    ∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra m)))
        (RealQuadraticAlgebra m)) (hI : I ≠ 0)
      (B : Basis (Fin 2) ℤ I.coeToSubmodule)
      (α : RealQuadraticAlgebra m),
      v15ValueFractionalIdeal I α ≤ 1 →
      v15IdealTraceGramOf I hI B α =
        ((a : ℚ), (b : ℚ), (c : ℚ)) →
      a % 2 = 0 ∧ b % 2 = 0 ∧ c % 2 = 0 := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  intro I hI B α hint hGram
  let β₀ := v15IdealFieldBasisOf I hI B 0
  let β₁ := v15IdealFieldBasisOf I hI B 1
  have hmem (i : Fin 2) : v15IdealFieldBasisOf I hI B i ∈ I := by
    rw [v15_ideal_field_basis_of_apply I hI B i]
    exact (B i).2
  have hintxy (x y : Fin 2) :
      IsIntegral ℤ (α * v15IdealFieldBasisOf I hI B x *
        v15IdealFieldBasisOf I hI B y) :=
    v15_value_integral_of_ideal_integral I α hint (hmem x) (hmem y)
  have hAint : IsIntegral ℤ (α * β₀ ^ 2) := by
    simpa only [pow_two, mul_assoc, β₀] using hintxy 0 0
  have hBint : IsIntegral ℤ (α * β₀ * β₁) := hintxy 0 1
  have hCint : IsIntegral ℤ (α * β₁ ^ 2) := by
    simpa only [pow_two, mul_assoc, β₁] using hintxy 1 1
  obtain ⟨tA, htA⟩ := v15_integral_trace_even_caseI hm hsq hmod _ hAint
  obtain ⟨tB, htB⟩ := v15_integral_trace_even_caseI hm hsq hmod _ hBint
  obtain ⟨tC, htC⟩ := v15_integral_trace_even_caseI hm hsq hmod _ hCint
  have hA : (a : ℚ) = 2 * (tA : ℚ) := by
    have h := congrArg Prod.fst hGram
    dsimp [v15IdealTraceGramOf] at h
    exact h.symm.trans htA
  have hB : (b : ℚ) = 2 * (tB : ℚ) := by
    have h := congrArg (fun z : ℚ × ℚ × ℚ ↦ z.2.1) hGram
    dsimp [v15IdealTraceGramOf] at h
    exact h.symm.trans htB
  have hC : (c : ℚ) = 2 * (tC : ℚ) := by
    have h := congrArg (fun z : ℚ × ℚ × ℚ ↦ z.2.2) hGram
    dsimp [v15IdealTraceGramOf] at h
    exact h.symm.trans htC
  have hAZ : (a : ℤ) = 2 * tA := by exact_mod_cast hA
  have hBZ : (b : ℤ) = 2 * tB := by exact_mod_cast hB
  have hCZ : (c : ℤ) = 2 * tC := by exact_mod_cast hC
  omega

/-- The six-row arithmetic classification for any chosen reduced basis of
an actual fractional ideal. -/
theorem v15_actual_reduced_basis_six_rows
    {m a b c : ℕ} (hm : 1 < m) (hsq : IsSquarefreeNat m) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare hm hsq⟩
    ∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra m)))
        (RealQuadraticAlgebra m)) (hI : I ≠ 0)
      (B : Basis (Fin 2) ℤ I.coeToSubmodule)
      (α : RealQuadraticAlgebra m),
      0 < Algebra.norm ℚ α →
      v15ValueFractionalIdeal I α ≤ 1 →
      V15IdealTraceEuclidean I α →
      v15IdealTraceGramOf I hI B α =
        ((a : ℚ), (b : ℚ), (c : ℚ)) →
      V15ReducedGram a b c →
      ∃ n : ℕ,
        (n : ℚ) = |Algebra.norm ℚ α| * (FractionalIdeal.absNorm I) ^ 2 ∧
        V15QuadraticCandidate m a b c n ∧
        V15TraceNormCondition m a n ∧
        (m, a, b, c, n) ∈ v15SixSurvivingGrams := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  intro I hI B α hαnorm hint heucl hGram hred
  have hbinary : V15BinaryTraceEuclidean a b c :=
    (v15_ideal_trace_euclidean_iff_binary_of I hI B α hGram).mp heucl
  have hadm : V15AdmissibleGram a b c :=
    v15_binary_euclidean_implies_admissible hred hbinary
  let β := v15IdealFieldBasisOf I hI B 0
  have hβmem : β ∈ I := by
    change v15IdealFieldBasisOf I hI B 0 ∈ I
    rw [v15_ideal_field_basis_of_apply I hI B 0]
    exact (B 0).2
  have hβ0 : β ≠ 0 :=
    (v15IdealFieldBasisOf I hI B).linearIndependent.ne_zero 0
  have htrace : Algebra.trace ℚ (RealQuadraticAlgebra m)
      (α * β ^ 2) = (a : ℚ) := by
    simpa only [v15IdealTraceGramOf, β] using congrArg Prod.fst hGram
  obtain ⟨n, k, t, hnpos, hk, hn, hβnorm, heq, hprincipal⟩ :=
    v15_actual_ideal_vector_equation hm hsq I hI α β
      hαnorm hint hβmem hβ0 htrace
  have hdetQ := v15_actual_ideal_trace_gram_determinant_of I hI
    (QuadraticAlgebra.finrank_eq_two (m : ℚ) 0) B α hGram
  rw [v15_real_quadratic_field_discriminant hm hsq] at hdetQ
  have hdetQ' : (a : ℚ) * c - (b : ℚ) ^ 2 =
      (v15QuadraticDiscriminant m : ℚ) * n := by
    rw [hn, abs_of_pos hαnorm]
    nlinarith [hdetQ]
  have hb_le_a : b ≤ a := by
    have hba := hred.2.2
    omega
  have hbb : b * b ≤ a * a := Nat.mul_self_le_mul_self hb_le_a
  have haa : a * a ≤ a * c := Nat.mul_le_mul_left a hred.2.1
  have hle : b ^ 2 ≤ a * c := by nlinarith
  have hdet : a * c - b ^ 2 = v15QuadraticDiscriminant m * n := by
    have hq : ((a * c - b ^ 2 : ℕ) : ℚ) =
        ((v15QuadraticDiscriminant m * n : ℕ) : ℚ) := by
      calc
        ((a * c - b ^ 2 : ℕ) : ℚ) =
            (a : ℚ) * c - (b : ℚ) ^ 2 := by
              rw [Nat.cast_sub hle]
              norm_cast
        _ = (v15QuadraticDiscriminant m : ℚ) * n := hdetQ'
        _ = ((v15QuadraticDiscriminant m * n : ℕ) : ℚ) := by norm_cast
    exact_mod_cast hq
  have hpar : m % 4 ≠ 1 →
      a % 2 = 0 ∧ b % 2 = 0 ∧ c % 2 = 0 := by
    intro hnot
    rcases squarefree_mod_four_cases hsq with h1 | hcase
    · exact (hnot h1).elim
    · exact v15_actual_ideal_trace_gram_even_of
        hm hsq hcase I hI B α hint hGram
  have hcand : V15QuadraticCandidate m a b c n :=
    ⟨hm, hsq, hadm, hnpos, hdet, hpar⟩
  have htracecond : V15TraceNormCondition m a n := ⟨t, k, hk, heq⟩
  exact ⟨n, hn, hcand, htracecond,
    v15_quadratic_candidate_six_rows hcand htracecond⟩

/-- Gauss reduction supplies a reduced natural-number Gram triple for every
positive integral trace form on an actual nonzero fractional ideal. -/
theorem v15_actual_ideal_exists_reduced_basis
    {m : ℕ} (hm : 1 < m) (hsq : IsSquarefreeNat m) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare hm hsq⟩
    ∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra m)))
        (RealQuadraticAlgebra m)) (hI : I ≠ 0)
      (α : RealQuadraticAlgebra m)
      (hint : v15ValueFractionalIdeal I α ≤ 1),
      0 < Algebra.norm ℚ α →
      V15IdealTracePositive I α →
      ∃ (B : Basis (Fin 2) ℤ I.coeToSubmodule) (a b c : ℕ),
        v15IdealTraceGramOf I hI B α =
          ((a : ℚ), (b : ℚ), (c : ℚ)) ∧
        V15ReducedGram a b c := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  intro I hI α hint hαnorm hpositive
  obtain ⟨B, hle, hcross, htwice⟩ :=
    v15_actual_ideal_gauss_basis I hI
      (QuadraticAlgebra.finrank_eq_two (m : ℚ) 0) α hint hpositive
  let a := v15IdealTraceNat I α hint (B 0)
  let b := (v15IdealCrossTraceInt I α hint (B 0) (B 1)).toNat
  let c := v15IdealTraceNat I α hint (B 1)
  have hbZ : (b : ℤ) = v15IdealCrossTraceInt I α hint (B 0) (B 1) := by
    simpa only [b] using Int.toNat_of_nonneg hcross
  have hbQ : (b : ℚ) = Algebra.trace ℚ (RealQuadraticAlgebra m)
      (α * (B 0 : RealQuadraticAlgebra m) *
        (B 1 : RealQuadraticAlgebra m)) := by
    have hbCast : (b : ℚ) =
        (v15IdealCrossTraceInt I α hint (B 0) (B 1) : ℚ) := by
      exact_mod_cast hbZ
    exact hbCast.trans
      (v15_ideal_cross_trace_int_cast I α hint (B 0) (B 1))
  have haQ : (a : ℚ) = Algebra.trace ℚ (RealQuadraticAlgebra m)
      (α * (B 0 : RealQuadraticAlgebra m) ^ 2) :=
    v15_ideal_trace_nat_cast I α hint hpositive (B 0)
  have hcQ : (c : ℚ) = Algebra.trace ℚ (RealQuadraticAlgebra m)
      (α * (B 1 : RealQuadraticAlgebra m) ^ 2) :=
    v15_ideal_trace_nat_cast I α hint hpositive (B 1)
  have hGram : v15IdealTraceGramOf I hI B α =
      ((a : ℚ), (b : ℚ), (c : ℚ)) := by
    simp only [v15IdealTraceGramOf, v15_ideal_field_basis_of_apply]
    exact Prod.ext haQ.symm (Prod.ext hbQ.symm hcQ.symm)
  have hB0 : B 0 ≠ 0 := B.linearIndependent.ne_zero 0
  have ha2 : 2 ≤ a :=
    v15_actual_ideal_trace_diagonal_ge_two hm hsq I α
      hαnorm hint hpositive (B 0) hB0
  have hb2 : 2 * b ≤ a := by
    rw [← hbZ] at htwice
    exact_mod_cast htwice
  exact ⟨B, a, b, c, hGram, ha2, hle, hb2⟩

/-- The six-row sieve applies to every positive integral trace-Euclidean
rank-one ideal lattice, without choosing or assuming a reduced basis. -/
theorem v15_actual_ideal_six_rows
    {m : ℕ} (hm : 1 < m) (hsq : IsSquarefreeNat m) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare hm hsq⟩
    ∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra m)))
        (RealQuadraticAlgebra m)) (hI : I ≠ 0)
      (α : RealQuadraticAlgebra m),
      0 < Algebra.norm ℚ α →
      ∀ (hint : v15ValueFractionalIdeal I α ≤ 1),
        V15IdealTracePositive I α →
        V15IdealTraceEuclidean I α →
        ∃ (B : Basis (Fin 2) ℤ I.coeToSubmodule) (a b c n : ℕ),
          v15IdealTraceGramOf I hI B α =
            ((a : ℚ), (b : ℚ), (c : ℚ)) ∧
          V15ReducedGram a b c ∧
          (n : ℚ) = |Algebra.norm ℚ α| *
            (FractionalIdeal.absNorm I) ^ 2 ∧
          (m, a, b, c, n) ∈ v15SixSurvivingGrams := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  intro I hI α hαnorm hint hpositive heucl
  obtain ⟨B, a, b, c, hGram, hred⟩ :=
    v15_actual_ideal_exists_reduced_basis hm hsq I hI α hint
      hαnorm hpositive
  obtain ⟨n, hn, _, _, hrow⟩ :=
    v15_actual_reduced_basis_six_rows hm hsq I hI B α
      hαnorm hint heucl hGram hred
  exact ⟨B, a, b, c, n, hGram, hred, hn, hrow⟩

end

end TraceEuclidean
