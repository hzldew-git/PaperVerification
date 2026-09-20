import TraceEuclidean.V15ActualSieve
import TraceEuclidean.V15VariableSieve

/-!
The ideal quotient norm converts the finite first-vector index calculation
into actual principality for every surviving row except `m = 3`.
-/

namespace TraceEuclidean

open Module
open scoped NumberField nonZeroDivisors

noncomputable section

theorem v15_actual_survivor_principal_except_three
    {m a b c n : ℕ} (hm : 1 < m) (hsq : IsSquarefreeNat m)
    (hm3 : m ≠ 3) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare hm hsq⟩
    ∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra m)))
        (RealQuadraticAlgebra m)) (hI : I ≠ 0)
      (α : RealQuadraticAlgebra m),
      0 < Algebra.norm ℚ α →
      v15ValueFractionalIdeal I α ≤ 1 →
      v15IdealTraceGram I hI (QuadraticAlgebra.finrank_eq_two (m : ℚ) 0) α =
        ((a : ℚ), (b : ℚ), (c : ℚ)) →
      (m, a, b, c, n) ∈ v15SixSurvivingGrams →
      (n : ℚ) = |Algebra.norm ℚ α| * (FractionalIdeal.absNorm I) ^ 2 →
      I = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 _))
        (v15IdealFieldBasis I hI
          (QuadraticAlgebra.finrank_eq_two (m : ℚ) 0) 0) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  intro I hI α hαnorm hint hGram hrow hn
  have htrace : Algebra.trace ℚ (RealQuadraticAlgebra m)
      (α * (v15IdealFieldBasis I hI
        (QuadraticAlgebra.finrank_eq_two (m : ℚ) 0) 0) ^ 2) =
      (a : ℚ) := by
    simpa only [v15IdealTraceGram] using congrArg Prod.fst hGram
  obtain ⟨n', k, t, hn', hk, hn'', hβnorm, heq, hcond, hprincipal⟩ :=
    v15_actual_ideal_vector_trace_norm hm hsq I hI α hαnorm hint 0 htrace
  have hnEq : n' = n := by
    exact_mod_cast hn''.trans hn.symm
  subst n'
  have hk1 := v15_survivor_first_index_one_except_three hrow hm3 hk heq
  exact hprincipal hk1

/-- For each nonexceptional reduced row, the original fractional ideal is
principal; thus nonfree rank-one ideal lattices cannot occur there. -/
theorem v15_actual_reduced_ideal_principal_except_three
    {m a b c : ℕ} (hm : 1 < m) (hsq : IsSquarefreeNat m)
    (hm3 : m ≠ 3) :
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
      I = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 _))
        (v15IdealFieldBasis I hI
          (QuadraticAlgebra.finrank_eq_two (m : ℚ) 0) 0) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  intro I hI α hαnorm hint heucl hGram hred
  obtain ⟨n, hn, hcand, htrace, hrow⟩ :=
    v15_actual_reduced_ideal_six_rows hm hsq I hI α hαnorm
      hint heucl hGram hred
  exact v15_actual_survivor_principal_except_three hm hsq hm3 I hI α
    hαnorm hint hGram hrow hn

/-- Trace four and norm four characterize the rational element two in
the concrete field `ℚ(√3)`. -/
private theorem v15_mthree_trace_norm_four_eq_two
    [Fact (∀ r : ℚ, r ^ 2 ≠ (3 : ℚ) + 0 * r)]
    (z : RealQuadraticAlgebra 3)
    (htrace : Algebra.trace ℚ (RealQuadraticAlgebra 3) z = 4)
    (hnorm : Algebra.norm ℚ z = 4) : z = 2 := by
  have hre : z.re = 2 := by
    have htr := realQuadratic_trace (m := 3) z
    have htr4 : 2 * z.re = 4 := htr.symm.trans htrace
    linarith
  have him : z.im = 0 := by
    rw [realQuadratic_norm, hre] at hnorm
    norm_num at hnorm
    nlinarith [sq_nonneg z.im]
  apply QuadraticAlgebra.ext
  · simpa [QuadraticAlgebra.re_ofNat] using hre
  · simpa [QuadraticAlgebra.im_ofNat] using him

/-- In the exceptional `m = 3` row, the two actual ideal basis vectors
cannot both have quotient-ideal index two. One of them generates the ideal. -/
theorem v15_actual_mthree_ideal_principal
    (hsq : IsSquarefreeNat 3) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (3 : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare (by norm_num) hsq⟩
    ∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra 3)))
        (RealQuadraticAlgebra 3)) (hI : I ≠ 0)
      (α : RealQuadraticAlgebra 3),
      0 < Algebra.norm ℚ α →
      v15ValueFractionalIdeal I α ≤ 1 →
      v15IdealTraceGram I hI (QuadraticAlgebra.finrank_eq_two (3 : ℚ) 0) α =
        ((4 : ℚ), (2 : ℚ), (4 : ℚ)) →
      (1 : ℚ) = |Algebra.norm ℚ α| * (FractionalIdeal.absNorm I) ^ 2 →
      ∃ i : Fin 2,
        I = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 _))
          (v15IdealFieldBasis I hI
            (QuadraticAlgebra.finrank_eq_two (3 : ℚ) 0) i) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (3 : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare (by norm_num) hsq⟩
  intro I hI α hαnorm hint hGram hn
  let hd : Module.finrank ℚ (RealQuadraticAlgebra 3) = 2 :=
    QuadraticAlgebra.finrank_eq_two (3 : ℚ) 0
  let B := v15IdealFieldBasis I hI hd
  have htrace0 : Algebra.trace ℚ (RealQuadraticAlgebra 3)
      (α * (B 0) ^ 2) = 4 := by
    simpa only [v15IdealTraceGram, B] using congrArg Prod.fst hGram
  have htrace1 : Algebra.trace ℚ (RealQuadraticAlgebra 3)
      (α * (B 1) ^ 2) = 4 := by
    simpa only [v15IdealTraceGram, B] using
      congrArg (fun z : ℚ × ℚ × ℚ ↦ z.2.2) hGram
  obtain ⟨n₀, k₀, t₀, hn₀, hk₀, hn₀', hnorm₀, heq₀, hc₀, hp₀⟩ :=
    v15_actual_ideal_vector_trace_norm (m := 3) (a := 4)
      (by norm_num) hsq I hI α hαnorm hint 0 htrace0
  obtain ⟨n₁, k₁, t₁, hn₁, hk₁, hn₁', hnorm₁, heq₁, hc₁, hp₁⟩ :=
    v15_actual_ideal_vector_trace_norm (m := 3) (a := 4)
      (by norm_num) hsq I hI α hαnorm hint 1 htrace1
  have hn₀eq : n₀ = 1 := by exact_mod_cast hn₀'.trans hn.symm
  have hn₁eq : n₁ = 1 := by exact_mod_cast hn₁'.trans hn.symm
  subst n₀
  subst n₁
  have hzero₀ : t₀ = 0 → α * (B 0) ^ 2 = 2 := by
    intro ht
    have hk2 : k₀ = 2 := by
      rcases v15_m_three_trace_norm_solutions hk₀ heq₀ with h | h | h
      · omega
      · omega
      · exact h.2
    have hnorm4 : Algebra.norm ℚ (α * (B 0) ^ 2) = 4 := by
      have h := hnorm₀
      change Algebra.norm ℚ (α * (B 0) ^ 2) =
        (1 : ℚ) * (k₀ : ℚ) ^ 2 at h
      rw [hk2] at h
      norm_num at h
      simpa only [map_mul, map_pow] using h
    exact v15_mthree_trace_norm_four_eq_two _ htrace0 hnorm4
  have hzero₁ : t₁ = 0 → α * (B 1) ^ 2 = 2 := by
    intro ht
    have hk2 : k₁ = 2 := by
      rcases v15_m_three_trace_norm_solutions hk₁ heq₁ with h | h | h
      · omega
      · omega
      · exact h.2
    have hnorm4 : Algebra.norm ℚ (α * (B 1) ^ 2) = 4 := by
      have h := hnorm₁
      change Algebra.norm ℚ (α * (B 1) ^ 2) =
        (1 : ℚ) * (k₁ : ℚ) ^ 2 at h
      rw [hk2] at h
      norm_num at h
      simpa only [map_mul, map_pow] using h
    exact v15_mthree_trace_norm_four_eq_two _ htrace1 hnorm4
  have hne : B 0 ≠ B 1 := B.linearIndependent.injective.ne (by decide)
  have hneNeg : B 0 ≠ -B 1 := by
    intro he
    have hz : B 0 + B 1 = 0 := add_eq_zero_iff_eq_neg.mpr he
    have hz' := congrArg (fun z : RealQuadraticAlgebra 3 ↦ B.repr z 0) hz
    simp at hz'
  have hkone := v15_m_three_basis_forces_one_index_one
    (ne_of_gt (show (0 : ℚ) < Algebra.norm ℚ α from hαnorm) |> fun h ↦
      (Algebra.norm_ne_zero_iff).mp h)
    hne hneNeg hk₀ hk₁ heq₀ heq₁ hzero₀ hzero₁
  rcases hkone with hk | hk
  · exact ⟨0, hp₀ hk⟩
  · exact ⟨1, hp₁ hk⟩

/-- Every actual reduced trace-Euclidean ideal lattice in the six-row range
has a principal underlying fractional ideal, including the exceptional row. -/
theorem v15_actual_reduced_ideal_principal
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
      ∃ i : Fin 2,
        I = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 _))
          (v15IdealFieldBasis I hI
            (QuadraticAlgebra.finrank_eq_two (m : ℚ) 0) i) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  intro I hI α hαnorm hint heucl hGram hred
  by_cases hm3 : m = 3
  · subst m
    obtain ⟨n, hn, hcand, htrace, hrow⟩ :=
      v15_actual_reduced_ideal_six_rows (by norm_num) hsq I hI α
        hαnorm hint heucl hGram hred
    have hshape : a = 4 ∧ b = 2 ∧ c = 4 ∧ n = 1 := by
      simp only [v15SixSurvivingGrams, List.mem_cons, List.not_mem_nil,
        or_false, Prod.mk.injEq] at hrow
      rcases hrow with h | h | h | h | h | h <;> omega
    rcases hshape with ⟨rfl, rfl, rfl, rfl⟩
    exact v15_actual_mthree_ideal_principal hsq I hI α hαnorm hint hGram hn
  · exact ⟨0, v15_actual_reduced_ideal_principal_except_three
      hm hsq hm3 I hI α hαnorm hint heucl hGram hred⟩

/-- For a selected reduced basis, each nonexceptional surviving row has
index one for its first actual ideal vector. -/
theorem v15_actual_survivor_principal_of_except_three
    {m a b c n : ℕ} (hm : 1 < m) (hsq : IsSquarefreeNat m)
    (hm3 : m ≠ 3) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare hm hsq⟩
    ∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra m)))
        (RealQuadraticAlgebra m)) (hI : I ≠ 0)
      (B : Basis (Fin 2) ℤ I.coeToSubmodule)
      (α : RealQuadraticAlgebra m),
      0 < Algebra.norm ℚ α →
      v15ValueFractionalIdeal I α ≤ 1 →
      v15IdealTraceGramOf I hI B α =
        ((a : ℚ), (b : ℚ), (c : ℚ)) →
      (m, a, b, c, n) ∈ v15SixSurvivingGrams →
      (n : ℚ) = |Algebra.norm ℚ α| *
        (FractionalIdeal.absNorm I) ^ 2 →
      I = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 _))
        (v15IdealFieldBasisOf I hI B 0) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  intro I hI B α hαnorm hint hGram hrow hn
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
  obtain ⟨n', k, t, _, hk, hn', _, heq, hprincipal⟩ :=
    v15_actual_ideal_vector_equation hm hsq I hI α β
      hαnorm hint hβmem hβ0 htrace
  have hnEq : n' = n := by exact_mod_cast hn'.trans hn.symm
  subst n'
  exact hprincipal (v15_survivor_first_index_one_except_three hrow hm3 hk heq)

/-- In the exceptional row, one of the two vectors in any selected ideal
basis generates the ideal. -/
theorem v15_actual_mthree_ideal_principal_of
    (hsq : IsSquarefreeNat 3) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (3 : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare (by norm_num) hsq⟩
    ∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra 3)))
        (RealQuadraticAlgebra 3)) (hI : I ≠ 0)
      (B : Basis (Fin 2) ℤ I.coeToSubmodule)
      (α : RealQuadraticAlgebra 3),
      0 < Algebra.norm ℚ α →
      v15ValueFractionalIdeal I α ≤ 1 →
      v15IdealTraceGramOf I hI B α =
        ((4 : ℚ), (2 : ℚ), (4 : ℚ)) →
      (1 : ℚ) = |Algebra.norm ℚ α| *
        (FractionalIdeal.absNorm I) ^ 2 →
      ∃ i : Fin 2,
        I = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 _))
          (v15IdealFieldBasisOf I hI B i) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (3 : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare (by norm_num) hsq⟩
  intro I hI B α hαnorm hint hGram hn
  let C := v15IdealFieldBasisOf I hI B
  have hmem (i : Fin 2) : C i ∈ I := by
    change v15IdealFieldBasisOf I hI B i ∈ I
    rw [v15_ideal_field_basis_of_apply I hI B i]
    exact (B i).2
  have hnz (i : Fin 2) : C i ≠ 0 := C.linearIndependent.ne_zero i
  have htrace0 : Algebra.trace ℚ (RealQuadraticAlgebra 3)
      (α * (C 0) ^ 2) = 4 := by
    simpa only [v15IdealTraceGramOf, C] using congrArg Prod.fst hGram
  have htrace1 : Algebra.trace ℚ (RealQuadraticAlgebra 3)
      (α * (C 1) ^ 2) = 4 := by
    simpa only [v15IdealTraceGramOf, C] using
      congrArg (fun z : ℚ × ℚ × ℚ ↦ z.2.2) hGram
  obtain ⟨n₀, k₀, t₀, _, hk₀, hn₀', hnorm₀, heq₀, hp₀⟩ :=
    v15_actual_ideal_vector_equation (m := 3) (a := 4)
      (by norm_num) hsq I hI α (C 0) hαnorm hint
      (hmem 0) (hnz 0) htrace0
  obtain ⟨n₁, k₁, t₁, _, hk₁, hn₁', hnorm₁, heq₁, hp₁⟩ :=
    v15_actual_ideal_vector_equation (m := 3) (a := 4)
      (by norm_num) hsq I hI α (C 1) hαnorm hint
      (hmem 1) (hnz 1) htrace1
  have hn₀eq : n₀ = 1 := by exact_mod_cast hn₀'.trans hn.symm
  have hn₁eq : n₁ = 1 := by exact_mod_cast hn₁'.trans hn.symm
  subst n₀
  subst n₁
  have hzero₀ : t₀ = 0 → α * (C 0) ^ 2 = 2 := by
    intro ht
    have hk2 : k₀ = 2 := by
      rcases v15_m_three_trace_norm_solutions hk₀ heq₀ with h | h | h
      · omega
      · omega
      · exact h.2
    have hnorm4 : Algebra.norm ℚ (α * (C 0) ^ 2) = 4 := by
      have h := hnorm₀
      change Algebra.norm ℚ (α * (C 0) ^ 2) =
        (1 : ℚ) * (k₀ : ℚ) ^ 2 at h
      rw [hk2] at h
      norm_num at h
      simpa only [map_mul, map_pow] using h
    exact v15_mthree_trace_norm_four_eq_two _ htrace0 hnorm4
  have hzero₁ : t₁ = 0 → α * (C 1) ^ 2 = 2 := by
    intro ht
    have hk2 : k₁ = 2 := by
      rcases v15_m_three_trace_norm_solutions hk₁ heq₁ with h | h | h
      · omega
      · omega
      · exact h.2
    have hnorm4 : Algebra.norm ℚ (α * (C 1) ^ 2) = 4 := by
      have h := hnorm₁
      change Algebra.norm ℚ (α * (C 1) ^ 2) =
        (1 : ℚ) * (k₁ : ℚ) ^ 2 at h
      rw [hk2] at h
      norm_num at h
      simpa only [map_mul, map_pow] using h
    exact v15_mthree_trace_norm_four_eq_two _ htrace1 hnorm4
  have hne : C 0 ≠ C 1 := C.linearIndependent.injective.ne (by decide)
  have hneNeg : C 0 ≠ -C 1 := by
    intro he
    have hz : C 0 + C 1 = 0 := add_eq_zero_iff_eq_neg.mpr he
    have hz' := congrArg (fun z : RealQuadraticAlgebra 3 ↦ C.repr z 0) hz
    simp at hz'
  have hkone := v15_m_three_basis_forces_one_index_one
    (ne_of_gt (show (0 : ℚ) < Algebra.norm ℚ α from hαnorm) |> fun h ↦
      (Algebra.norm_ne_zero_iff).mp h)
    hne hneNeg hk₀ hk₁ heq₀ heq₁ hzero₀ hzero₁
  rcases hkone with hk | hk
  · exact ⟨0, hp₀ hk⟩
  · exact ⟨1, hp₁ hk⟩

/-- Every positive integral trace-Euclidean fractional ideal over a real
quadratic field is principal, including the exceptional `m = 3` row. -/
theorem v15_actual_ideal_principal
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
        ∃ β : RealQuadraticAlgebra m, β ≠ 0 ∧
          I = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 _)) β := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  intro I hI α hαnorm hint hpositive heucl
  obtain ⟨B, a, b, c, n, hGram, _, hn, hrow⟩ :=
    v15_actual_ideal_six_rows hm hsq I hI α hαnorm hint hpositive heucl
  by_cases hm3 : m = 3
  · subst m
    have hshape : a = 4 ∧ b = 2 ∧ c = 4 ∧ n = 1 := by
      simp only [v15SixSurvivingGrams, List.mem_cons, List.not_mem_nil,
        or_false, Prod.mk.injEq] at hrow
      rcases hrow with h | h | h | h | h | h <;> omega
    rcases hshape with ⟨rfl, rfl, rfl, rfl⟩
    obtain ⟨i, hprincipal⟩ :=
      v15_actual_mthree_ideal_principal_of hsq I hI B α
        hαnorm hint hGram hn
    exact ⟨v15IdealFieldBasisOf I hI B i,
      (v15IdealFieldBasisOf I hI B).linearIndependent.ne_zero i,
      hprincipal⟩
  · let β := v15IdealFieldBasisOf I hI B 0
    have hprincipal := v15_actual_survivor_principal_of_except_three
      hm hsq hm3 I hI B α hαnorm hint hGram hrow hn
    exact ⟨β, (v15IdealFieldBasisOf I hI B).linearIndependent.ne_zero 0,
      hprincipal⟩

theorem v15_norm_of_principal_ideal_coefficient
    {F : Type*} [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (α β : F) (hαnorm : 0 < Algebra.norm ℚ α)
    (hprincipal : I = FractionalIdeal.spanSingleton
      (nonZeroDivisors (𝓞 F)) β)
    {n : ℕ} (hn : (n : ℚ) = |Algebra.norm ℚ α| *
      (FractionalIdeal.absNorm I) ^ 2) :
    Algebra.norm ℚ (α * β ^ 2) = (n : ℚ) := by
  have hInorm : FractionalIdeal.absNorm I = |Algebra.norm ℚ β| := by
    rw [hprincipal]
    exact FractionalIdeal.absNorm_span_singleton (K := F) (𝓞 F) β
  calc
    Algebra.norm ℚ (α * β ^ 2) =
        Algebra.norm ℚ α * (Algebra.norm ℚ β) ^ 2 := by
          rw [map_mul, map_pow]
    _ = |Algebra.norm ℚ α| * |Algebra.norm ℚ β| ^ 2 := by
          rw [abs_of_pos hαnorm, sq_abs]
    _ = |Algebra.norm ℚ α| * (FractionalIdeal.absNorm I) ^ 2 := by
          rw [hInorm]
    _ = n := hn.symm

/-- One ideal generator has the trace and norm of its surviving Gram row.
This is the coefficient of the free lattice obtained by ideal scaling. -/
theorem v15_actual_ideal_generator_trace_norm
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
        ∃ (a b c n : ℕ) (β : RealQuadraticAlgebra m),
          (m, a, b, c, n) ∈ v15SixSurvivingGrams ∧
          β ≠ 0 ∧
          I = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 _)) β ∧
          Algebra.trace ℚ (RealQuadraticAlgebra m) (α * β ^ 2) = (a : ℚ) ∧
          Algebra.norm ℚ (α * β ^ 2) = (n : ℚ) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  intro I hI α hαnorm hint hpositive heucl
  obtain ⟨B, a, b, c, n, hGram, _, hn, hrow⟩ :=
    v15_actual_ideal_six_rows hm hsq I hI α hαnorm hint hpositive heucl
  by_cases hm3 : m = 3
  · subst m
    have hshape : a = 4 ∧ b = 2 ∧ c = 4 ∧ n = 1 := by
      simp only [v15SixSurvivingGrams, List.mem_cons, List.not_mem_nil,
        or_false, Prod.mk.injEq] at hrow
      rcases hrow with h | h | h | h | h | h <;> omega
    rcases hshape with ⟨rfl, rfl, rfl, rfl⟩
    obtain ⟨i, hprincipal⟩ :=
      v15_actual_mthree_ideal_principal_of hsq I hI B α
        hαnorm hint hGram hn
    let β := v15IdealFieldBasisOf I hI B i
    have htrace : Algebra.trace ℚ (RealQuadraticAlgebra 3)
        (α * β ^ 2) = (4 : ℚ) := by
      fin_cases i
      · simpa [v15IdealTraceGramOf, β, Fin.zero_eta] using
          congrArg Prod.fst hGram
      · simpa [v15IdealTraceGramOf, β, Fin.mk_one] using
          congrArg (fun z : ℚ × ℚ × ℚ ↦ z.2.2) hGram
    exact ⟨4, 2, 4, 1, β, hrow,
      (v15IdealFieldBasisOf I hI B).linearIndependent.ne_zero i,
      hprincipal, htrace,
      v15_norm_of_principal_ideal_coefficient I α β hαnorm hprincipal hn⟩
  · let β := v15IdealFieldBasisOf I hI B 0
    have hprincipal := v15_actual_survivor_principal_of_except_three
      hm hsq hm3 I hI B α hαnorm hint hGram hrow hn
    have htrace : Algebra.trace ℚ (RealQuadraticAlgebra m)
        (α * β ^ 2) = (a : ℚ) := by
      simpa only [v15IdealTraceGramOf, β] using congrArg Prod.fst hGram
    exact ⟨a, b, c, n, β, hrow,
      (v15IdealFieldBasisOf I hI B).linearIndependent.ne_zero 0,
      hprincipal, htrace,
      v15_norm_of_principal_ideal_coefficient I α β hαnorm hprincipal hn⟩

end

end TraceEuclidean
