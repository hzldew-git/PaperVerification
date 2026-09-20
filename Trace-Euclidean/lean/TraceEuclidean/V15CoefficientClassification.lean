import TraceEuclidean.V15ActualPrincipality
import TraceEuclidean.V15Representatives

/-!
The six surviving trace/norm pairs determine the coefficient of a free
rank-one lattice up to the two real-quadratic conjugates. This file states
the result for the actual coefficient obtained from an arbitrary ideal.
-/

namespace TraceEuclidean

open Module
open scoped NumberField nonZeroDivisors

noncomputable section

def V15SixCoefficientCoordinates {m : ℕ}
    (z : RealQuadraticAlgebra m) : Prop :=
  (m = 2 ∧ z.re = 1 ∧ z.im = 0) ∨
  (m = 3 ∧ z.re = 2 ∧ (z.im = 1 ∨ z.im = -1)) ∨
  (m = 5 ∧ (z.re = 1 ∨ z.re = 2) ∧ z.im = 0) ∨
  (m = 13 ∧ z.re = 1 ∧ z.im = 0) ∨
  (m = 21 ∧ z.re = 5 / 2 ∧
    (z.im = 1 / 2 ∨ z.im = -(1 / 2 : ℚ)))

theorem v15_coefficient_coordinates_of_six_rows
    {m a b c n : ℕ}
    (hrow : (m, a, b, c, n) ∈ v15SixSurvivingGrams)
    [Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r)]
    (z : RealQuadraticAlgebra m)
    (htrace : Algebra.trace ℚ (RealQuadraticAlgebra m) z = (a : ℚ))
    (hnorm : Algebra.norm ℚ z = (n : ℚ)) :
    V15SixCoefficientCoordinates z := by
  have htr : 2 * z.re = (a : ℚ) :=
    (realQuadratic_trace z).symm.trans htrace
  have hN : z.re ^ 2 - (m : ℚ) * z.im ^ 2 = (n : ℚ) :=
    (realQuadratic_norm z).symm.trans hnorm
  simp only [v15SixSurvivingGrams, List.mem_cons, List.not_mem_nil,
    or_false, Prod.mk.injEq] at hrow
  rcases hrow with h | h | h | h | h | h
  · rcases h with ⟨rfl, rfl, _, _, rfl⟩
    have hre : z.re = 1 := by norm_num at htr; linarith
    have him : z.im = 0 := by
      norm_num at hN
      nlinarith [sq_nonneg z.im]
    exact Or.inl ⟨rfl, hre, him⟩
  · rcases h with ⟨rfl, rfl, _, _, rfl⟩
    have hre : z.re = 2 := by norm_num at htr; linarith
    have himsq : z.im ^ 2 = 1 := by
      norm_num at hN
      rw [hre] at hN
      nlinarith
    have him : z.im = 1 ∨ z.im = -1 := by
      have hfactor : (z.im - 1) * (z.im + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hfactor with hz | hz
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    exact Or.inr (Or.inl ⟨rfl, hre, him⟩)
  · rcases h with ⟨rfl, rfl, _, _, rfl⟩
    have hre : z.re = 1 := by norm_num at htr; linarith
    have him : z.im = 0 := by
      norm_num at hN
      nlinarith [sq_nonneg z.im]
    exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl hre, him⟩))
  · rcases h with ⟨rfl, rfl, _, _, rfl⟩
    have hre : z.re = 2 := by norm_num at htr; linarith
    have him : z.im = 0 := by
      norm_num at hN
      nlinarith [sq_nonneg z.im]
    exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr hre, him⟩))
  · rcases h with ⟨rfl, rfl, _, _, rfl⟩
    have hre : z.re = 1 := by norm_num at htr; linarith
    have him : z.im = 0 := by
      norm_num at hN
      nlinarith [sq_nonneg z.im]
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hre, him⟩)))
  · rcases h with ⟨rfl, rfl, _, _, rfl⟩
    have hre : z.re = 5 / 2 := by norm_num at htr; linarith
    have himsq : z.im ^ 2 = 1 / 4 := by
      norm_num at hN
      rw [hre] at hN
      nlinarith
    have him : z.im = 1 / 2 ∨ z.im = -(1 / 2 : ℚ) := by
      have hfactor : (z.im - 1 / 2) * (z.im + 1 / 2) = 0 := by nlinarith
      rcases mul_eq_zero.mp hfactor with hz | hz
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hre, him⟩)))

/-- Every actual trace-Euclidean ideal lattice has a free generator whose
quadratic coefficient has one of the five field-specific coordinate shapes
(with two classes over `m = 5`). -/
theorem v15_actual_ideal_coefficient_coordinates
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
        ∃ β : RealQuadraticAlgebra m,
          β ≠ 0 ∧
          I = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 _)) β ∧
          V15SixCoefficientCoordinates (α * β ^ 2) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  intro I hI α hαnorm hint hpositive heucl
  obtain ⟨a, b, c, n, β, hrow, hβ0, hprincipal, htrace, hnorm⟩ :=
    v15_actual_ideal_generator_trace_norm hm hsq I hI α hαnorm
      hint hpositive heucl
  exact ⟨β, hβ0, hprincipal,
    v15_coefficient_coordinates_of_six_rows hrow (α * β ^ 2) htrace hnorm⟩

/-- The coefficient `2 + √3` is an algebraic-integer unit, with conjugate
`2 - √3` as its inverse. -/
def v15mThreeUnit
    [Fact (∀ r : ℚ, r ^ 2 ≠ (3 : ℚ) + 0 * r)] :
    (𝓞 (RealQuadraticAlgebra 3))ˣ := by
  let u : 𝓞 (RealQuadraticAlgebra 3) :=
    caseIIntegerPointToRing (m := 3) (2, 1)
  let v : 𝓞 (RealQuadraticAlgebra 3) :=
    caseIIntegerPointToRing (m := 3) (2, -1)
  have huv : u * v = 1 := by
    apply Subtype.ext
    change caseIIntegerPointValue (m := 3) (2, 1) *
      caseIIntegerPointValue (m := 3) (2, -1) = 1
    apply QuadraticAlgebra.ext <;>
      norm_num [caseIIntegerPointValue, QuadraticAlgebra.re_one,
        QuadraticAlgebra.im_one]
  have hvu : v * u = 1 := by simpa only [mul_comm] using huv
  exact ⟨u, v, huv, hvu⟩

theorem v15_mthree_unit_value
    [Fact (∀ r : ℚ, r ^ 2 ≠ (3 : ℚ) + 0 * r)] :
    (((v15mThreeUnit : (𝓞 (RealQuadraticAlgebra 3))ˣ) :
      𝓞 (RealQuadraticAlgebra 3)) : RealQuadraticAlgebra 3) =
      v15mThreeCoefficient := by
  apply QuadraticAlgebra.ext <;>
    norm_num [v15mThreeUnit, caseIIntegerPointToRing,
      caseIIntegerPointValue, v15mThreeCoefficient]

/-- The coefficient `(5 + √21)/2` is an algebraic-integer unit, with
conjugate `(5 - √21)/2` as its inverse. -/
def v15mTwentyOneUnit
    [Fact (∀ r : ℚ, r ^ 2 ≠ (21 : ℚ) + 0 * r)] :
    (𝓞 (RealQuadraticAlgebra 21))ˣ := by
  let u : 𝓞 (RealQuadraticAlgebra 21) :=
    caseIIIntegerPointToRing (m := 21) (by norm_num) (2, 1)
  let v : 𝓞 (RealQuadraticAlgebra 21) :=
    caseIIIntegerPointToRing (m := 21) (by norm_num) (3, -1)
  have huv : u * v = 1 := by
    apply Subtype.ext
    change caseIIIntegerPointValue (m := 21) (2, 1) *
      caseIIIntegerPointValue (m := 21) (3, -1) = 1
    apply QuadraticAlgebra.ext <;>
      norm_num [caseIIIntegerPointValue, QuadraticAlgebra.re_one,
        QuadraticAlgebra.im_one]
  have hvu : v * u = 1 := by simpa only [mul_comm] using huv
  exact ⟨u, v, huv, hvu⟩

theorem v15_mtwentyone_unit_value
    [Fact (∀ r : ℚ, r ^ 2 ≠ (21 : ℚ) + 0 * r)] :
    (((v15mTwentyOneUnit : (𝓞 (RealQuadraticAlgebra 21))ˣ) :
      𝓞 (RealQuadraticAlgebra 21)) : RealQuadraticAlgebra 21) =
      v15mTwentyOneCoefficient := by
  apply QuadraticAlgebra.ext <;>
    norm_num [v15mTwentyOneUnit, caseIIIntegerPointToRing,
      caseIIIntegerPointValue, v15mTwentyOneCoefficient]

def v15UnitValue {m : ℕ}
    [Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r)]
    (u : (𝓞 (RealQuadraticAlgebra m))ˣ) : RealQuadraticAlgebra m :=
  ((u : 𝓞 (RealQuadraticAlgebra m)) : RealQuadraticAlgebra m)

/-- Membership means equality, up to the square of an actual ring-of-integers
unit, with one of the six named free coefficients. -/
def V15SixFreeCoefficientClass {m : ℕ}
    [Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r)]
    (γ : RealQuadraticAlgebra m) : Prop :=
  ∃ u : (𝓞 (RealQuadraticAlgebra m))ˣ,
    (m = 2 ∧ γ * v15UnitValue u ^ 2 = 1) ∨
    (m = 3 ∧ γ * v15UnitValue u ^ 2 = ⟨2, 1⟩) ∨
    (m = 5 ∧ γ * v15UnitValue u ^ 2 = 1) ∨
    (m = 5 ∧ γ * v15UnitValue u ^ 2 = 2) ∨
    (m = 13 ∧ γ * v15UnitValue u ^ 2 = 1) ∨
    (m = 21 ∧ γ * v15UnitValue u ^ 2 = ⟨5 / 2, 1 / 2⟩)

theorem v15_coordinates_to_free_coefficient_class
    {m : ℕ} [Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r)]
    (γ : RealQuadraticAlgebra m)
    (h : V15SixCoefficientCoordinates γ) :
    V15SixFreeCoefficientClass γ := by
  rcases h with h | h | h | h | h
  · rcases h with ⟨rfl, hre, him⟩
    have hγ : γ = 1 := by
      apply QuadraticAlgebra.ext
      · simpa [QuadraticAlgebra.re_one] using hre
      · simpa [QuadraticAlgebra.im_one] using him
    refine ⟨1, Or.inl ⟨rfl, ?_⟩⟩
    simp [hγ, v15UnitValue]
  · rcases h with ⟨rfl, hre, him⟩
    rcases him with him | him
    · have hγ : γ = v15mThreeCoefficient := by
        apply QuadraticAlgebra.ext
        · simpa [v15mThreeCoefficient] using hre
        · simpa [v15mThreeCoefficient] using him
      refine ⟨1, Or.inr (Or.inl ⟨rfl, ?_⟩)⟩
      simpa [hγ, v15UnitValue, v15mThreeCoefficient]
    · have hγ : γ = (⟨2, -1⟩ : RealQuadraticAlgebra 3) := by
        apply QuadraticAlgebra.ext
        · simpa using hre
        · simpa using him
      refine ⟨v15mThreeUnit, Or.inr (Or.inl ⟨rfl, ?_⟩)⟩
      change γ *
        (((v15mThreeUnit : (𝓞 (RealQuadraticAlgebra 3))ˣ) :
          𝓞 (RealQuadraticAlgebra 3)) : RealQuadraticAlgebra 3) ^ 2 =
        v15mThreeCoefficient
      rw [v15_mthree_unit_value, hγ]
      apply QuadraticAlgebra.ext <;>
        norm_num [v15mThreeCoefficient, pow_two]
  · rcases h with ⟨rfl, hre, him⟩
    rcases hre with hre | hre
    · have hγ : γ = 1 := by
        apply QuadraticAlgebra.ext
        · simpa [QuadraticAlgebra.re_one] using hre
        · simpa [QuadraticAlgebra.im_one] using him
      refine ⟨1, Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))⟩
      simp [hγ, v15UnitValue]
    · have hγ : γ = 2 := by
        apply QuadraticAlgebra.ext
        · simpa [QuadraticAlgebra.re_ofNat] using hre
        · simpa [QuadraticAlgebra.im_ofNat] using him
      refine ⟨1, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩)))⟩
      simp [hγ, v15UnitValue]
  · rcases h with ⟨rfl, hre, him⟩
    have hγ : γ = 1 := by
      apply QuadraticAlgebra.ext
      · simpa [QuadraticAlgebra.re_one] using hre
      · simpa [QuadraticAlgebra.im_one] using him
    refine ⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))))⟩
    simp [hγ, v15UnitValue]
  · rcases h with ⟨rfl, hre, him⟩
    rcases him with him | him
    · have hγ : γ = v15mTwentyOneCoefficient := by
        apply QuadraticAlgebra.ext
        · simpa [v15mTwentyOneCoefficient] using hre
        · simpa [v15mTwentyOneCoefficient] using him
      refine ⟨1, ?_⟩
      right; right; right; right; right
      refine ⟨rfl, ?_⟩
      simp [hγ, v15UnitValue, v15mTwentyOneCoefficient]
    · have hγ : γ = (⟨5 / 2, -(1 / 2 : ℚ)⟩ :
          RealQuadraticAlgebra 21) := by
        apply QuadraticAlgebra.ext
        · simpa using hre
        · simpa using him
      refine ⟨v15mTwentyOneUnit, ?_⟩
      right; right; right; right; right
      refine ⟨rfl, ?_⟩
      change γ *
        (((v15mTwentyOneUnit : (𝓞 (RealQuadraticAlgebra 21))ˣ) :
          𝓞 (RealQuadraticAlgebra 21)) : RealQuadraticAlgebra 21) ^ 2 =
        v15mTwentyOneCoefficient
      rw [v15_mtwentyone_unit_value, hγ]
      apply QuadraticAlgebra.ext <;>
        norm_num [v15mTwentyOneCoefficient, pow_two]

/-- Necessity in Theorem 1.7 for all actual fractional ideals: the lattice
is free and, after scaling by its generator and a ring-of-integers unit, its
coefficient is exactly one of the six stated coefficients. -/
theorem v15_actual_ideal_six_free_coefficients
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
        ∃ β : RealQuadraticAlgebra m,
          β ≠ 0 ∧
          I = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 _)) β ∧
          V15SixFreeCoefficientClass (α * β ^ 2) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  intro I hI α hαnorm hint hpositive heucl
  obtain ⟨β, hβ0, hprincipal, hshape⟩ :=
    v15_actual_ideal_coefficient_coordinates hm hsq I hI α
      hαnorm hint hpositive heucl
  exact ⟨β, hβ0, hprincipal,
    v15_coordinates_to_free_coefficient_class (α * β ^ 2) hshape⟩

/-- Multiplication by a ring-of-integers unit, followed by multiplication
by an ideal generator, is an explicit module equivalence. -/
def v15_unit_scaled_principal_equiv
    {F : Type*} [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    {β : F} (hβ0 : β ≠ 0)
    (hprincipal : I = FractionalIdeal.spanSingleton
      (nonZeroDivisors (𝓞 F)) β)
    (u : (𝓞 F)ˣ) :
    (𝓞 F) ≃ₗ[𝓞 F] I :=
  (DistribMulAction.toLinearEquiv (𝓞 F) (𝓞 F) u).trans
    (v15_principal_ideal_equiv I hβ0 hprincipal)

theorem v15_unit_scaled_principal_quadratic_isometry
    {F : Type*} [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    {β : F} (hβ0 : β ≠ 0)
    (hprincipal : I = FractionalIdeal.spanSingleton
      (nonZeroDivisors (𝓞 F)) β)
    (α : F) (u : (𝓞 F)ˣ) (x : 𝓞 F) :
    α * (((v15_unit_scaled_principal_equiv I hβ0 hprincipal u x : I) : F) ^ 2) =
      (α * β ^ 2 *
        (((u : 𝓞 F) : F) ^ 2)) * (x : F) ^ 2 := by
  unfold v15_unit_scaled_principal_equiv
  rw [LinearEquiv.trans_apply, v15_principal_ideal_equiv_apply]
  change α * (((((u : 𝓞 F) : F) * (x : F)) * β) ^ 2) = _
  ring

/-- Actual `𝓞_F`-linear quadratic-lattice isometry to a free coefficient. -/
def V15IdealIsometricToFree
    {F : Type*} [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (α δ : F) : Prop :=
  ∃ e : (𝓞 F) ≃ₗ[𝓞 F] I,
    ∀ x : 𝓞 F,
      α * (((e x : I) : F) ^ 2) = δ * (x : F) ^ 2

theorem v15_ideal_isometric_to_free_of_unit_square
    {F : Type*} [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (α δ : F) {β : F} (hβ0 : β ≠ 0)
    (hprincipal : I = FractionalIdeal.spanSingleton
      (nonZeroDivisors (𝓞 F)) β)
    (u : (𝓞 F)ˣ)
    (hcoeff : α * β ^ 2 * (((u : 𝓞 F) : F) ^ 2) = δ) :
    V15IdealIsometricToFree I α δ := by
  refine ⟨v15_unit_scaled_principal_equiv I hβ0 hprincipal u, ?_⟩
  intro x
  rw [v15_unit_scaled_principal_quadratic_isometry]
  rw [hcoeff]

/-- The six names in Theorem 1.7, interpreted as honest `𝓞_F`-linear
isometry classes of arbitrary fractional-ideal lattices. -/
def V15SixFreeIsometryClass
    {m : ℕ} [Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r)]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra m)))
      (RealQuadraticAlgebra m))
    (α : RealQuadraticAlgebra m) : Prop :=
  (m = 2 ∧ V15IdealIsometricToFree I α 1) ∨
  (m = 3 ∧ V15IdealIsometricToFree I α ⟨2, 1⟩) ∨
  (m = 5 ∧ V15IdealIsometricToFree I α 1) ∨
  (m = 5 ∧ V15IdealIsometricToFree I α 2) ∨
  (m = 13 ∧ V15IdealIsometricToFree I α 1) ∨
  (m = 21 ∧ V15IdealIsometricToFree I α ⟨5 / 2, 1 / 2⟩)

/-- Necessity: every positive integral trace-Euclidean rank-one fractional
ideal lattice lies in one of the six actual module-isometry classes. -/
theorem v15_actual_ideal_six_isometry_classes
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
        V15SixFreeIsometryClass I α := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  intro I hI α hαnorm hint hpositive heucl
  obtain ⟨β, hβ0, hprincipal, u, hclass⟩ :=
    v15_actual_ideal_six_free_coefficients hm hsq I hI α
      hαnorm hint hpositive heucl
  rcases hclass with h | h | h | h | h | h
  · exact Or.inl ⟨h.1,
      v15_ideal_isometric_to_free_of_unit_square I α 1 hβ0 hprincipal u h.2⟩
  · exact Or.inr (Or.inl ⟨h.1,
      v15_ideal_isometric_to_free_of_unit_square I α ⟨2, 1⟩
        hβ0 hprincipal u h.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h.1,
      v15_ideal_isometric_to_free_of_unit_square I α 1
        hβ0 hprincipal u h.2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1,
      v15_ideal_isometric_to_free_of_unit_square I α 2
        hβ0 hprincipal u h.2⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1,
      v15_ideal_isometric_to_free_of_unit_square I α 1
        hβ0 hprincipal u h.2⟩))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
    exact ⟨h.1, v15_ideal_isometric_to_free_of_unit_square I α
      ⟨5 / 2, 1 / 2⟩ hβ0 hprincipal u h.2⟩

/-- Trace Euclideanity transfers from a free representative through an
actual module isometry. The map is evaluated on the fraction field by its
value at one, so this covers every field point in the Euclidean condition. -/
theorem v15_ideal_trace_euclidean_of_free_isometry
    {F : Type*} [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (α δ : F)
    (hIso : V15IdealIsometricToFree I α δ)
    (hFree : V15FreeTraceEuclidean δ) :
    V15IdealTraceEuclidean I α := by
  obtain ⟨e, he⟩ := hIso
  let β : F := ((e 1 : I) : F)
  have hβ0 : β ≠ 0 := by
    intro hzero
    have hezero : e 1 = 0 := Subtype.ext hzero
    have hone : (1 : 𝓞 F) = 0 := e.injective (by simpa using hezero)
    exact one_ne_zero hone
  have hmap (y : 𝓞 F) : ((e y : I) : F) = (y : F) * β := by
    have hy : e y = y • e 1 := by
      calc
        e y = e (y • (1 : 𝓞 F)) := by simp [smul_eq_mul]
        _ = y • e 1 := map_smul e y 1
    rw [hy]
    rfl
  have hcoeff : α * β ^ 2 = δ := by
    simpa [β] using he 1
  intro x
  obtain ⟨y, hy⟩ := hFree (x / β)
  refine ⟨e y, ?_⟩
  have hx : x - ((e y : I) : F) = β * (x / β - (y : F)) := by
    rw [hmap]
    field_simp [hβ0]
  rw [hx]
  have hq : α * (β * (x / β - (y : F))) ^ 2 =
      δ * (x / β - (y : F)) ^ 2 := by
    rw [← hcoeff]
    ring
  rw [hq]
  exact hy

/-- Sufficiency: every one of the six actual isometry classes is trace
Euclidean. The six free representatives have separate constructive covering
proofs; this theorem transfers each proof to arbitrary isometric ideals. -/
theorem v15_six_isometry_classes_trace_euclidean
    {m : ℕ} [Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r)]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra m)))
      (RealQuadraticAlgebra m))
    (α : RealQuadraticAlgebra m)
    (hclass : V15SixFreeIsometryClass I α) :
    V15IdealTraceEuclidean I α := by
  rcases hclass with h | h | h | h | h | h
  · rcases h with ⟨rfl, hIso⟩
    exact v15_ideal_trace_euclidean_of_free_isometry I α 1 hIso
      v15_mtwo_representative_euclidean
  · rcases h with ⟨rfl, hIso⟩
    exact v15_ideal_trace_euclidean_of_free_isometry I α
      v15mThreeCoefficient hIso v15_mthree_representative_euclidean
  · rcases h with ⟨rfl, hIso⟩
    exact v15_ideal_trace_euclidean_of_free_isometry I α 1 hIso
      v15_mfive_one_representative_euclidean
  · rcases h with ⟨rfl, hIso⟩
    exact v15_ideal_trace_euclidean_of_free_isometry I α 2 hIso
      v15_mfive_two_representative_euclidean
  · rcases h with ⟨rfl, hIso⟩
    exact v15_ideal_trace_euclidean_of_free_isometry I α 1 hIso
      v15_mthirteen_representative_euclidean
  · rcases h with ⟨rfl, hIso⟩
    exact v15_ideal_trace_euclidean_of_free_isometry I α
      v15mTwentyOneCoefficient hIso
      v15_mtwentyone_representative_euclidean

/-- Theorem 1.7: the exact six-class if-and-only-if classification for
positive integral rank-one fractional-ideal lattices over real quadratic
fields. The hypotheses include all nonzero fractional ideals. -/
theorem v15_rank_one_real_quadratic_classification
    {m : ℕ} (hm : 1 < m) (hsq : IsSquarefreeNat m) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare hm hsq⟩
    ∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra m)))
        (RealQuadraticAlgebra m)) (hI : I ≠ 0)
      (α : RealQuadraticAlgebra m),
      0 < Algebra.norm ℚ α →
      v15ValueFractionalIdeal I α ≤ 1 →
      V15IdealTracePositive I α →
      (V15IdealTraceEuclidean I α ↔ V15SixFreeIsometryClass I α) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  intro I hI α hαnorm hint hpositive
  constructor
  · exact v15_actual_ideal_six_isometry_classes hm hsq I hI α
      hαnorm hint hpositive
  · exact v15_six_isometry_classes_trace_euclidean I α

end

end TraceEuclidean
