import TraceEuclidean.V15PropositionSixOne
import TraceEuclidean.QuadraticIntegralBasis

/-!
The two integer-scalar specializations at the end of Proposition 6.1.
The integral-basis coordinate models and their exact rational covering radii
are reused, then transported to the algebraic-integer lattice.
-/

namespace TraceEuclidean

open Module
open scoped NumberField

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- Trace cost of the square form with a positive integer scalar on `𝓞 F`. -/
def v15ScalarTraceCost (a : ℕ) (x : F) (y : 𝓞 F) : ℚ :=
  Algebra.trace ℚ F ((a : F) * (x - (y : F)) ^ 2)

private theorem scalar_trace_cost_eq (a : ℕ) (x : F) (y : 𝓞 F) :
    v15ScalarTraceCost a x y =
      (a : ℚ) * Algebra.trace ℚ F ((x - (y : F)) ^ 2) := by
  change Algebra.trace ℚ F ((a : F) * (x - (y : F)) ^ 2) = _
  have hcast : (a : F) = algebraMap ℚ F (a : ℚ) := by simp
  rw [hcast, ← Algebra.smul_def (a : ℚ), map_smul]
  simp only [smul_eq_mul]

private theorem rational_radius_scale {X Y : Type*}
    {cost : X → Y → ℚ} {r : ℚ}
    (h : SquaredCoveringRadiusSpecOver cost r)
    (a : ℚ) (ha : 0 < a) :
    SquaredCoveringRadiusSpecOver (fun x y ↦ a * cost x y) (a * r) := by
  constructor
  · intro x
    obtain ⟨y, hy⟩ := h.upper x
    exact ⟨y, mul_le_mul_of_nonneg_left hy ha.le⟩
  · intro s hs
    have hs' : s / a < r := (div_lt_iff₀ ha).2 (by nlinarith)
    obtain ⟨x, hx⟩ := h.sharp (s / a) hs'
    refine ⟨x, fun y ↦ ?_⟩
    have hy := hx y
    have := mul_lt_mul_of_pos_left hy ha
    have hid : s / a * a = s := by field_simp [ne_of_gt ha]
    nlinarith

private theorem scalar_radius_of_coordinate_model {m : ℕ}
    (M : RealQuadraticCoordinateModel F m) (a : ℕ) (ha : 0 < a)
    {r : ℚ}
    (h : SquaredCoveringRadiusSpecOver (realQuadraticCostRat m) r) :
    SquaredCoveringRadiusSpecOver (v15ScalarTraceCost (F := F) a)
      ((a : ℚ) * r) := by
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  have hscaled := rational_radius_scale h a haQ
  constructor
  · intro x
    obtain ⟨z, hz⟩ := hscaled.upper (M.coordinates x)
    let y : 𝓞 F := M.integerCoordinates.symm z
    refine ⟨y, ?_⟩
    rw [scalar_trace_cost_eq, M.trace_formula]
    simpa only [y, AddEquiv.apply_symm_apply] using hz
  · intro s hs
    obtain ⟨p, hp⟩ := hscaled.sharp s hs
    refine ⟨M.coordinates.symm p, fun y ↦ ?_⟩
    rw [scalar_trace_cost_eq, M.trace_formula]
    simpa only [LinearEquiv.apply_symm_apply] using hp (M.integerCoordinates y)

/-- Both displayed integer-scalar formulas in Proposition 6.1, for the
actual quadratic integer ring and every positive integer coefficient. -/
theorem v15_proposition_six_one_scalar_cases {m : ℕ}
    (hm : 1 < m) (hsq : IsSquarefreeNat m)
    (a : ℕ) (ha : 0 < a) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare hm hsq⟩
    (m % 4 = 2 ∨ m % 4 = 3 →
      SquaredCoveringRadiusSpecOver
        (v15ScalarTraceCost (F := RealQuadraticAlgebra m) a)
        ((a : ℚ) * ((m : ℚ) + 1) / 2)) ∧
    (m % 4 = 1 →
      SquaredCoveringRadiusSpecOver
        (v15ScalarTraceCost (F := RealQuadraticAlgebra m) a)
        ((a : ℚ) * ((m : ℚ) + 1) ^ 2 / (8 * m))) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  constructor
  · intro hmod
    have hbase : SquaredCoveringRadiusSpecOver
        (realQuadraticCostRat m) (((m : ℚ) + 1) / 2) := by
      have hnot : m % 4 ≠ 1 := by omega
      simpa [realQuadraticCostRat, hnot, caseIRadiusSqOver] using
        (caseI_exact_radius_over (K := ℚ) (m := (m : ℚ)) (by positivity))
    have hspec := scalar_radius_of_coordinate_model
      (realQuadraticCoordinateModel_caseI hsq hmod) a ha hbase
    convert hspec using 1; ring
  · intro hmod
    have hm3 : 3 ≤ m := by omega
    have hbase : SquaredCoveringRadiusSpecOver
        (realQuadraticCostRat m) ((((m : ℚ) + 1) ^ 2) / (8 * m)) := by
      simpa [realQuadraticCostRat, hmod, caseIIRadiusSqOver] using
        (caseII_exact_radius_over (K := ℚ) (m := (m : ℚ))
          (by exact_mod_cast hm3))
    have hspec := scalar_radius_of_coordinate_model
      (realQuadraticCoordinateModel_caseII hsq hmod) a ha hbase
    convert hspec using 1; ring

/-- All clauses of Proposition 6.1 in one exported statement: the reduced
basis and exact radius for every qualifying fractional ideal, and both
integer-scalar formulas on the full ring of integers. -/
theorem v15_proposition_six_one_full {m : ℕ}
    (hm : 1 < m) (hsq : IsSquarefreeNat m) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare hm hsq⟩
    (∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra m)))
          (RealQuadraticAlgebra m)) (hI : I ≠ 0)
        (α : RealQuadraticAlgebra m),
        V15RealQuadraticTotallyPositive α →
        v15ValueFractionalIdeal I α ≤ 1 →
        ∃ (B : Basis (Fin 2) ℤ I.coeToSubmodule) (a b c : ℕ),
          v15IdealTraceGramOf I hI B α = ((a : ℚ), (b : ℚ), (c : ℚ)) ∧
          V15ReducedGram a b c ∧
          (a : ℚ) * c - (b : ℚ) ^ 2 =
            (NumberField.discr (RealQuadraticAlgebra m) : ℚ) *
              Algebra.norm ℚ α * (FractionalIdeal.absNorm I) ^ 2 ∧
          SquaredCoveringRadiusSpecOver (v15IdealTraceCost I α)
            (v15GramRadius a b c) ∧
          (V15IdealTraceEuclidean I α ↔ V15BinaryTraceEuclidean a b c)) ∧
    (∀ a : ℕ, 0 < a →
      (m % 4 = 2 ∨ m % 4 = 3 →
        SquaredCoveringRadiusSpecOver
          (v15ScalarTraceCost (F := RealQuadraticAlgebra m) a)
          ((a : ℚ) * ((m : ℚ) + 1) / 2)) ∧
      (m % 4 = 1 →
        SquaredCoveringRadiusSpecOver
          (v15ScalarTraceCost (F := RealQuadraticAlgebra m) a)
          ((a : ℚ) * ((m : ℚ) + 1) ^ 2 / (8 * m)))) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  constructor
  · exact v15_proposition_six_one_ideal hm hsq
  · intro a ha
    exact v15_proposition_six_one_scalar_cases hm hsq a ha

end

end TraceEuclidean
