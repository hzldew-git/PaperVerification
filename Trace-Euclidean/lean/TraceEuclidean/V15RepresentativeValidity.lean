import TraceEuclidean.V15PositivityBridge

/-!
The six free representatives are themselves positive and integral, so the
classification theorem describes six realized classes rather than a list of
formal coefficient names.
-/

namespace TraceEuclidean

open scoped NumberField nonZeroDivisors

noncomputable section

/-- A named free coefficient represents an inhabited ideal-isometry class. -/
theorem v15_free_ideal_self_isometric
    {F : Type*} [Field F] [NumberField F] (δ : F) :
    V15IdealIsometricToFree
      (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) δ δ := by
  apply v15_ideal_isometric_to_free_of_unit_square
    (I := (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F))
    δ δ (β := 1) (by simp) (by simp) 1
  simp

theorem v15_free_value_ideal_integral_of_coefficient_integral
    {F : Type*} [Field F] [NumberField F]
    (δ : F) (hδ : IsIntegral ℤ δ) :
    v15ValueFractionalIdeal
      (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) δ ≤ 1 := by
  unfold v15ValueFractionalIdeal
  simp only [one_pow, mul_one]
  apply FractionalIdeal.spanSingleton_le_iff_mem.mpr
  exact (FractionalIdeal.mem_one_iff _).mpr ⟨⟨δ, hδ⟩, rfl⟩

theorem v15_mtwo_representative_valid :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (2 : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare (by norm_num) v15_small_squarefree_two⟩
    V15RealQuadraticTotallyPositive (1 : RealQuadraticAlgebra 2) ∧
      v15ValueFractionalIdeal
        (1 : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra 2)))
          (RealQuadraticAlgebra 2)) 1 ≤ 1 := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (2 : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare (by norm_num) v15_small_squarefree_two⟩
  constructor
  · apply (v15_total_positive_iff_re_norm_positive (by norm_num) 1).mpr
    norm_num [V15RealQuadraticCoefficientPositive, realQuadratic_norm,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · apply v15_free_value_ideal_integral_of_coefficient_integral
    simpa using ((1 : 𝓞 (RealQuadraticAlgebra 2)).isIntegral_coe)

theorem v15_mthree_representative_valid :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (3 : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare (by norm_num) v15_small_squarefree_three⟩
    V15RealQuadraticTotallyPositive v15mThreeCoefficient ∧
      v15ValueFractionalIdeal
        (1 : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra 3)))
          (RealQuadraticAlgebra 3)) v15mThreeCoefficient ≤ 1 := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (3 : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare (by norm_num) v15_small_squarefree_three⟩
  constructor
  · apply (v15_total_positive_iff_re_norm_positive (by norm_num)
      v15mThreeCoefficient).mpr
    norm_num [V15RealQuadraticCoefficientPositive, realQuadratic_norm,
      v15mThreeCoefficient]
  · apply v15_free_value_ideal_integral_of_coefficient_integral
    rw [← v15_mthree_unit_value]
    exact ((v15mThreeUnit : (𝓞 (RealQuadraticAlgebra 3))ˣ) :
      𝓞 (RealQuadraticAlgebra 3)).isIntegral_coe

theorem v15_mfive_one_representative_valid :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (5 : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare (by norm_num) v15_small_squarefree_five⟩
    V15RealQuadraticTotallyPositive (1 : RealQuadraticAlgebra 5) ∧
      v15ValueFractionalIdeal
        (1 : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra 5)))
          (RealQuadraticAlgebra 5)) 1 ≤ 1 := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (5 : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare (by norm_num) v15_small_squarefree_five⟩
  constructor
  · apply (v15_total_positive_iff_re_norm_positive (by norm_num) 1).mpr
    norm_num [V15RealQuadraticCoefficientPositive, realQuadratic_norm,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · apply v15_free_value_ideal_integral_of_coefficient_integral
    simpa using ((1 : 𝓞 (RealQuadraticAlgebra 5)).isIntegral_coe)

theorem v15_mfive_two_representative_valid :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (5 : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare (by norm_num) v15_small_squarefree_five⟩
    V15RealQuadraticTotallyPositive (2 : RealQuadraticAlgebra 5) ∧
      v15ValueFractionalIdeal
        (1 : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra 5)))
          (RealQuadraticAlgebra 5)) 2 ≤ 1 := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (5 : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare (by norm_num) v15_small_squarefree_five⟩
  constructor
  · apply (v15_total_positive_iff_re_norm_positive (by norm_num) 2).mpr
    norm_num [V15RealQuadraticCoefficientPositive, realQuadratic_norm,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  · apply v15_free_value_ideal_integral_of_coefficient_integral
    have htwo : (((2 : 𝓞 (RealQuadraticAlgebra 5)) :
        RealQuadraticAlgebra 5)) = 2 := by
      change (algebraMap (𝓞 (RealQuadraticAlgebra 5))
        (RealQuadraticAlgebra 5)) 2 = 2
      exact map_ofNat _ _
    rw [← htwo]
    exact (2 : 𝓞 (RealQuadraticAlgebra 5)).isIntegral_coe

theorem v15_mthirteen_representative_valid :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (13 : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare (by norm_num) v15_small_squarefree_thirteen⟩
    V15RealQuadraticTotallyPositive (1 : RealQuadraticAlgebra 13) ∧
      v15ValueFractionalIdeal
        (1 : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra 13)))
          (RealQuadraticAlgebra 13)) 1 ≤ 1 := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (13 : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare (by norm_num) v15_small_squarefree_thirteen⟩
  constructor
  · apply (v15_total_positive_iff_re_norm_positive (by norm_num) 1).mpr
    norm_num [V15RealQuadraticCoefficientPositive, realQuadratic_norm,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · apply v15_free_value_ideal_integral_of_coefficient_integral
    simpa using ((1 : 𝓞 (RealQuadraticAlgebra 13)).isIntegral_coe)

theorem v15_mtwentyone_representative_valid :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (21 : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare (by norm_num) v15_small_squarefree_twentyone⟩
    V15RealQuadraticTotallyPositive v15mTwentyOneCoefficient ∧
      v15ValueFractionalIdeal
        (1 : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra 21)))
          (RealQuadraticAlgebra 21)) v15mTwentyOneCoefficient ≤ 1 := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (21 : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare (by norm_num) v15_small_squarefree_twentyone⟩
  constructor
  · apply (v15_total_positive_iff_re_norm_positive (by norm_num)
      v15mTwentyOneCoefficient).mpr
    norm_num [V15RealQuadraticCoefficientPositive, realQuadratic_norm,
      v15mTwentyOneCoefficient]
  · apply v15_free_value_ideal_integral_of_coefficient_integral
    rw [← v15_mtwentyone_unit_value]
    exact ((v15mTwentyOneUnit : (𝓞 (RealQuadraticAlgebra 21))ˣ) :
      𝓞 (RealQuadraticAlgebra 21)).isIntegral_coe

end

end TraceEuclidean
