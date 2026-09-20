import TraceEuclidean.V15QuadraticDiscriminant

/-!
The complete arithmetic and geometric sieve for an actual rank-one lattice
whose integral trace Gram matrix has been Gauss reduced. The remaining global
step is to supply such a reduced basis for every positive ideal lattice.
-/

namespace TraceEuclidean

open scoped NumberField nonZeroDivisors

noncomputable section

theorem v15_actual_reduced_ideal_six_rows
    {m a b c : ℕ} (hm : 1 < m) (hsq : IsSquarefreeNat m) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare hm hsq⟩
    ∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra m)))
        (RealQuadraticAlgebra m)) (hI : I ≠ 0)
      (α : RealQuadraticAlgebra m),
      0 < Algebra.norm ℚ α →
      v15ValueFractionalIdeal I α ≤ 1 →
      V15IdealTraceEuclidean I α →
      v15IdealTraceGram I hI (QuadraticAlgebra.finrank_eq_two (m : ℚ) 0) α =
        ((a : ℚ), (b : ℚ), (c : ℚ)) →
      V15ReducedGram a b c →
      ∃ n : ℕ,
        (n : ℚ) = |Algebra.norm ℚ α| * (FractionalIdeal.absNorm I) ^ 2 ∧
        V15QuadraticCandidate m a b c n ∧
        V15TraceNormCondition m a n ∧
        (m, a, b, c, n) ∈ v15SixSurvivingGrams := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  intro I hI α hαnorm hint heucl hGram hred
  let hd : Module.finrank ℚ (RealQuadraticAlgebra m) = 2 :=
    QuadraticAlgebra.finrank_eq_two (m : ℚ) 0
  have hbinary : V15BinaryTraceEuclidean a b c :=
    (v15_ideal_trace_euclidean_iff_binary I hI hd α hGram).mp heucl
  have hadm : V15AdmissibleGram a b c :=
    v15_binary_euclidean_implies_admissible hred hbinary
  obtain ⟨n, hnpos, hn, htrace⟩ :=
    v15_actual_ideal_first_trace_norm hm hsq I hI α hαnorm hint hGram
  have hdetQ := v15_actual_ideal_trace_gram_determinant I hI hd α hGram
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
    · exact v15_actual_ideal_trace_gram_even hm hsq hcase I hI α hint hGram
  have hcand : V15QuadraticCandidate m a b c n :=
    ⟨hm, hsq, hadm, hnpos, hdet, hpar⟩
  exact ⟨n, hn, hcand, htrace,
    v15_quadratic_candidate_six_rows hcand htrace⟩

end

end TraceEuclidean
