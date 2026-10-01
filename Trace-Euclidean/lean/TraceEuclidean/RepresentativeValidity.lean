import TraceEuclidean.PositivityBridge

/-!
The six free representatives are themselves positive and integral, so the
classification theorem describes six realized classes rather than a list of
formal coefficient names.
-/

namespace TraceEuclidean

open scoped NumberField nonZeroDivisors

noncomputable section

/-- A named free coefficient represents an inhabited ideal-isometry class. -/
theorem free_ideal_self_isometric
    {F : Type*} [Field F] [NumberField F] (δ : F) :
    IdealIsometricToFree
      (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) δ δ := by
  apply ideal_isometric_to_free_of_unit_square
    (I := (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F))
    δ δ (β := 1) (by simp) (by simp) 1
  simp

theorem free_value_ideal_integral_of_coefficient_integral
    {F : Type*} [Field F] [NumberField F]
    (δ : F) (hδ : IsIntegral ℤ δ) :
    valueFractionalIdeal
      (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) δ ≤ 1 := by
  unfold valueFractionalIdeal
  simp only [one_pow, mul_one]
  apply FractionalIdeal.spanSingleton_le_iff_mem.mpr
  exact (FractionalIdeal.mem_one_iff _).mpr ⟨⟨δ, hδ⟩, rfl⟩

theorem mtwo_representative_valid :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (2 : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare (by norm_num) small_squarefree_two⟩
    RealQuadraticTotallyPositive (1 : RealQuadraticAlgebra 2) ∧
      valueFractionalIdeal
        (1 : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra 2)))
          (RealQuadraticAlgebra 2)) 1 ≤ 1 := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (2 : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare (by norm_num) small_squarefree_two⟩
  constructor
  · apply (total_positive_iff_re_norm_positive (by norm_num) 1).mpr
    norm_num [RealQuadraticCoefficientPositive, realQuadratic_norm,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · apply free_value_ideal_integral_of_coefficient_integral
    simpa using ((1 : 𝓞 (RealQuadraticAlgebra 2)).isIntegral_coe)

theorem mthree_representative_valid :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (3 : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare (by norm_num) small_squarefree_three⟩
    RealQuadraticTotallyPositive mThreeCoefficient ∧
      valueFractionalIdeal
        (1 : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra 3)))
          (RealQuadraticAlgebra 3)) mThreeCoefficient ≤ 1 := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (3 : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare (by norm_num) small_squarefree_three⟩
  constructor
  · apply (total_positive_iff_re_norm_positive (by norm_num)
      mThreeCoefficient).mpr
    norm_num [RealQuadraticCoefficientPositive, realQuadratic_norm,
      mThreeCoefficient]
  · apply free_value_ideal_integral_of_coefficient_integral
    rw [← mthree_unit_value]
    exact ((mThreeUnit : (𝓞 (RealQuadraticAlgebra 3))ˣ) :
      𝓞 (RealQuadraticAlgebra 3)).isIntegral_coe

theorem mfive_one_representative_valid :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (5 : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare (by norm_num) small_squarefree_five⟩
    RealQuadraticTotallyPositive (1 : RealQuadraticAlgebra 5) ∧
      valueFractionalIdeal
        (1 : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra 5)))
          (RealQuadraticAlgebra 5)) 1 ≤ 1 := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (5 : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare (by norm_num) small_squarefree_five⟩
  constructor
  · apply (total_positive_iff_re_norm_positive (by norm_num) 1).mpr
    norm_num [RealQuadraticCoefficientPositive, realQuadratic_norm,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · apply free_value_ideal_integral_of_coefficient_integral
    simpa using ((1 : 𝓞 (RealQuadraticAlgebra 5)).isIntegral_coe)

theorem mfive_two_representative_valid :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (5 : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare (by norm_num) small_squarefree_five⟩
    RealQuadraticTotallyPositive (2 : RealQuadraticAlgebra 5) ∧
      valueFractionalIdeal
        (1 : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra 5)))
          (RealQuadraticAlgebra 5)) 2 ≤ 1 := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (5 : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare (by norm_num) small_squarefree_five⟩
  constructor
  · apply (total_positive_iff_re_norm_positive (by norm_num) 2).mpr
    norm_num [RealQuadraticCoefficientPositive, realQuadratic_norm,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  · apply free_value_ideal_integral_of_coefficient_integral
    have htwo : (((2 : 𝓞 (RealQuadraticAlgebra 5)) :
        RealQuadraticAlgebra 5)) = 2 := by
      change (algebraMap (𝓞 (RealQuadraticAlgebra 5))
        (RealQuadraticAlgebra 5)) 2 = 2
      exact map_ofNat _ _
    rw [← htwo]
    exact (2 : 𝓞 (RealQuadraticAlgebra 5)).isIntegral_coe

theorem mthirteen_representative_valid :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (13 : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare (by norm_num) small_squarefree_thirteen⟩
    RealQuadraticTotallyPositive (1 : RealQuadraticAlgebra 13) ∧
      valueFractionalIdeal
        (1 : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra 13)))
          (RealQuadraticAlgebra 13)) 1 ≤ 1 := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (13 : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare (by norm_num) small_squarefree_thirteen⟩
  constructor
  · apply (total_positive_iff_re_norm_positive (by norm_num) 1).mpr
    norm_num [RealQuadraticCoefficientPositive, realQuadratic_norm,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · apply free_value_ideal_integral_of_coefficient_integral
    simpa using ((1 : 𝓞 (RealQuadraticAlgebra 13)).isIntegral_coe)

theorem mtwentyone_representative_valid :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (21 : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare (by norm_num) small_squarefree_twentyone⟩
    RealQuadraticTotallyPositive mTwentyOneCoefficient ∧
      valueFractionalIdeal
        (1 : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra 21)))
          (RealQuadraticAlgebra 21)) mTwentyOneCoefficient ≤ 1 := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (21 : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare (by norm_num) small_squarefree_twentyone⟩
  constructor
  · apply (total_positive_iff_re_norm_positive (by norm_num)
      mTwentyOneCoefficient).mpr
    norm_num [RealQuadraticCoefficientPositive, realQuadratic_norm,
      mTwentyOneCoefficient]
  · apply free_value_ideal_integral_of_coefficient_integral
    rw [← mtwentyone_unit_value]
    exact ((mTwentyOneUnit : (𝓞 (RealQuadraticAlgebra 21))ˣ) :
      𝓞 (RealQuadraticAlgebra 21)).isIntegral_coe

end

end TraceEuclidean
