import TraceEuclidean.RankOneIdealBridge
import TraceEuclidean.VariableSieve
import TraceEuclidean.VariableDeterminant
import TraceEuclidean.PositivityBridge

/-!
Proposition 6.1 for every nonzero quadratic fractional ideal. The generic
binary covering theorem is transferred through an actual ideal basis, and the
existing Gauss and determinant theorems supply the remaining assertions.
-/

namespace TraceEuclidean

open Module
open scoped NumberField nonZeroDivisors

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- The rational trace cost on an actual fractional-ideal lattice. -/
def idealTraceCost
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (α : F)
    (x : F) (y : I.coeToSubmodule) : ℚ :=
  Algebra.trace ℚ F (α * (x - (y : F)) ^ 2)

private def pairToFin {R : Type*} (x : R × R) : Fin 2 → R :=
  Fin.cases x.1 (fun _ ↦ x.2)

@[simp] private theorem pairToFin_zero {R : Type*} (x : R × R) :
    pairToFin x 0 = x.1 := rfl

@[simp] private theorem pairToFin_one {R : Type*} (x : R × R) :
    pairToFin x 1 = x.2 := rfl

/-- Any specified reduced integral trace Gram basis of any nonzero quadratic
fractional ideal gives the exact squared trace covering radius on the field. -/
theorem ideal_exact_radius_of
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hI : I ≠ 0)
    (B : Basis (Fin 2) ℤ I.coeToSubmodule) (α : F)
    {a b c : ℕ}
    (hGram : idealTraceGramOf I hI B α =
      ((a : ℚ), (b : ℚ), (c : ℚ)))
    (hred : ReducedGram a b c) :
    SquaredCoveringRadiusSpecOver (idealTraceCost I α)
      (gramRadius a b c) := by
  let C := idealRationalCoordinatesOf I hI B
  let Z := idealIntegerCoordinatesOf I B
  have hspec := reduced_gram_exact_radius_rat hred
  constructor
  · intro x
    obtain ⟨z, hz⟩ := hspec.upper (C x 0, C x 1)
    let y : I.coeToSubmodule := Z.symm (pairToFin z)
    refine ⟨y, ?_⟩
    have hcost := ideal_trace_cost_of_eq_binary_cost I hI B α x y hGram
    change idealTraceCost I α x y = _ at hcost
    rw [hcost]
    have h0 : Z y 0 = z.1 := by simp [y, Z]
    have h1 : Z y 1 = z.2 := by simp [y, Z]
    simpa only [h0, h1, C, Z] using hz
  · intro r hr
    obtain ⟨p, hp⟩ := hspec.sharp r hr
    let x : F := C.symm (pairToFin p)
    refine ⟨x, fun y ↦ ?_⟩
    have hcost := ideal_trace_cost_of_eq_binary_cost I hI B α x y hGram
    change idealTraceCost I α x y = _ at hcost
    rw [hcost]
    have h0 : C x 0 = p.1 := by simp [x, C]
    have h1 : C x 1 = p.2 := by simp [x, C]
    simpa only [h0, h1, C, Z] using hp (Z y 0, Z y 1)

/-- Proposition 6.1 in the concrete real-quadratic field model: a Gauss basis,
its ideal-norm determinant, and the exact trace covering radius all exist
for every integral, totally positive, nonzero fractional-ideal lattice. -/
theorem proposition_six_one_ideal
    {m : ℕ} (hm : 1 < m) (hsq : IsSquarefreeNat m) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare hm hsq⟩
    ∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 (RealQuadraticAlgebra m)))
        (RealQuadraticAlgebra m)) (hI : I ≠ 0)
      (α : RealQuadraticAlgebra m),
      RealQuadraticTotallyPositive α →
      valueFractionalIdeal I α ≤ 1 →
      ∃ (B : Basis (Fin 2) ℤ I.coeToSubmodule) (a b c : ℕ),
        idealTraceGramOf I hI B α =
          ((a : ℚ), (b : ℚ), (c : ℚ)) ∧
        ReducedGram a b c ∧
        (a : ℚ) * c - (b : ℚ) ^ 2 =
          (NumberField.discr (RealQuadraticAlgebra m) : ℚ) *
            Algebra.norm ℚ α * (FractionalIdeal.absNorm I) ^ 2 ∧
        SquaredCoveringRadiusSpecOver (idealTraceCost I α)
          (gramRadius a b c) ∧
        (IdealTraceEuclidean I α ↔ BinaryTraceEuclidean a b c) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  intro I hI α htotal hint
  have hcoeff : RealQuadraticCoefficientPositive α :=
    (total_positive_iff_re_norm_positive hm α).mp htotal
  have hpositive : IdealTracePositive I α :=
    ideal_trace_positive_of_coefficient_positive hm I α hcoeff
  obtain ⟨B, a, b, c, hGram, hred⟩ :=
    actual_ideal_exists_reduced_basis hm hsq I hI α hint hcoeff.2 hpositive
  exact ⟨B, a, b, c, hGram, hred,
    actual_ideal_trace_gram_determinant_of I hI
      (QuadraticAlgebra.finrank_eq_two (m : ℚ) 0) B α hGram,
    ideal_exact_radius_of I hI B α hGram hred,
    ideal_trace_euclidean_iff_binary_of I hI B α hGram⟩

end

end TraceEuclidean
