import TraceEuclidean.QuadraticIntegralBasis
import TraceEuclidean.BinaryCriterion

/-!
Concrete free representatives for the six rows of Theorem 1.7. The three
nontrivial coefficient cases are checked against the integral-coordinate
models of the actual rings of integers, rather than only against abstract
binary forms.
-/

namespace TraceEuclidean

open scoped NumberField

noncomputable section

set_option maxHeartbeats 1000000

theorem small_squarefree_three : IsSquarefreeNat 3 := by
  intro k hk
  have hkSq : k * k ≤ 3 := Nat.le_of_dvd (by norm_num) hk
  have hkBound : k ≤ 1 := by nlinarith
  interval_cases k <;> norm_num at *

theorem small_squarefree_two : IsSquarefreeNat 2 := by
  intro k hk
  have hkSq : k * k ≤ 2 := Nat.le_of_dvd (by norm_num) hk
  have hkBound : k ≤ 1 := by nlinarith
  interval_cases k <;> norm_num at *

theorem small_squarefree_five : IsSquarefreeNat 5 := by
  intro k hk
  have hkSq : k * k ≤ 5 := Nat.le_of_dvd (by norm_num) hk
  have hkBound : k ≤ 2 := by nlinarith
  interval_cases k <;> norm_num at *

theorem small_squarefree_thirteen : IsSquarefreeNat 13 := by
  intro k hk
  have hkSq : k * k ≤ 13 := Nat.le_of_dvd (by norm_num) hk
  have hkBound : k ≤ 3 := by nlinarith
  interval_cases k <;> norm_num at *

theorem small_squarefree_twentyone : IsSquarefreeNat 21 := by
  intro k hk
  have hkSq : k * k ≤ 21 := Nat.le_of_dvd (by norm_num) hk
  have hkBound : k ≤ 4 := by nlinarith
  interval_cases k <;> norm_num at *

def FreeTraceEuclidean {F : Type*} [Field F] [NumberField F] (α : F) : Prop :=
  ∀ x : F, ∃ y : 𝓞 F,
    Algebra.trace ℚ F (α * (x - (y : F)) ^ 2) < 2

private theorem free_one_of_field_trace
    {F : Type*} [Field F] [NumberField F]
    (h : IsFieldTraceEuclidean (F := F) 2) :
    FreeTraceEuclidean (1 : F) := by
  intro x
  obtain ⟨y, hy⟩ := h x
  refine ⟨y, ?_⟩
  simp only [one_mul]
  exact_mod_cast hy

theorem mtwo_representative_euclidean :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (2 : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare (by norm_num) small_squarefree_two⟩
    FreeTraceEuclidean (1 : RealQuadraticAlgebra 2) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (2 : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare (by norm_num) small_squarefree_two⟩
  apply free_one_of_field_trace
  apply (realQuadratic_two_trace_euclidean_iff
    (m := 2) (by norm_num) small_squarefree_two).2
  exact Or.inl rfl

theorem mfive_one_representative_euclidean :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (5 : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare (by norm_num) small_squarefree_five⟩
    FreeTraceEuclidean (1 : RealQuadraticAlgebra 5) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (5 : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare (by norm_num) small_squarefree_five⟩
  apply free_one_of_field_trace
  apply (realQuadratic_two_trace_euclidean_iff
    (m := 5) (by norm_num) small_squarefree_five).2
  exact Or.inr (Or.inl rfl)

theorem mthirteen_representative_euclidean :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (13 : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare (by norm_num) small_squarefree_thirteen⟩
    FreeTraceEuclidean (1 : RealQuadraticAlgebra 13) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (13 : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare (by norm_num) small_squarefree_thirteen⟩
  apply free_one_of_field_trace
  apply (realQuadratic_two_trace_euclidean_iff
    (m := 13) (by norm_num) small_squarefree_thirteen).2
  exact Or.inr (Or.inr rfl)

def mThreeCoefficient : RealQuadraticAlgebra 3 := ⟨2, 1⟩
def mTwentyOneCoefficient : RealQuadraticAlgebra 21 := ⟨5 / 2, 1 / 2⟩

private theorem mthree_trace_formula
    [Fact (∀ r : ℚ, r ^ 2 ≠ (3 : ℚ) + 0 * r)]
    (x : RealQuadraticAlgebra 3) (z : IntegralPoint) :
    Algebra.trace ℚ (RealQuadraticAlgebra 3)
      (mThreeCoefficient *
        (x - caseIIntegerPointValue (m := 3) z) ^ 2) =
      gramCostRat 4 2 4 (x.re + x.im, x.im)
        (z.1 + z.2, z.2) := by
  calc
    _ = 2 * (mThreeCoefficient *
        (x - caseIIntegerPointValue (m := 3) z) ^ 2).re :=
      realQuadratic_trace _
    _ = _ := by
      simp [gramCostRat, mThreeCoefficient,
        caseIIntegerPointValue, pow_two]
      ring

private theorem mfive_two_trace_formula
    [Fact (∀ r : ℚ, r ^ 2 ≠ (5 : ℚ) + 0 * r)]
    (x : RealQuadraticAlgebra 5) (z : IntegralPoint) :
    Algebra.trace ℚ (RealQuadraticAlgebra 5)
      ((2 : RealQuadraticAlgebra 5) *
        (x - caseIIIntegerPointValue (m := 5) z) ^ 2) =
      gramCostRat 4 2 6
        (caseIICoordinates (m := 5) x)
        z := by
  calc
    _ = 2 * ((2 : RealQuadraticAlgebra 5) *
        (x - caseIIIntegerPointValue (m := 5) z) ^ 2).re :=
      realQuadratic_trace _
    _ = _ := by
      simp [gramCostRat, QuadraticAlgebra.re_ofNat,
        QuadraticAlgebra.im_ofNat, caseIICoordinates,
        caseIIIntegerPointValue, pow_two]
      ring

private theorem mtwentyone_trace_formula
    [Fact (∀ r : ℚ, r ^ 2 ≠ (21 : ℚ) + 0 * r)]
    (x : RealQuadraticAlgebra 21) (z : IntegralPoint) :
    Algebra.trace ℚ (RealQuadraticAlgebra 21)
      (mTwentyOneCoefficient *
        (x - caseIIIntegerPointValue (m := 21) z) ^ 2) =
      gramCostRat 5 2 5
        (-2 * x.im, x.re + 5 * x.im)
        (-z.2, z.1 + 3 * z.2) := by
  calc
    _ = 2 * (mTwentyOneCoefficient *
        (x - caseIIIntegerPointValue (m := 21) z) ^ 2).re :=
      realQuadratic_trace _
    _ = _ := by
      simp [gramCostRat, mTwentyOneCoefficient,
        caseIIIntegerPointValue, pow_two]
      ring

theorem mthree_representative_euclidean :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (3 : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare (by norm_num) small_squarefree_three⟩
    FreeTraceEuclidean mThreeCoefficient := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (3 : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare (by norm_num) small_squarefree_three⟩
  have hbinary := six_binary_forms_trace_euclidean.2.1
  intro x
  let p : PlanePoint ℚ := (x.re + x.im, x.im)
  obtain ⟨z, hz⟩ := hbinary p
  let w : IntegralPoint := (z.1 - z.2, z.2)
  let y : 𝓞 (RealQuadraticAlgebra 3) := caseIIntegerPointToRing (m := 3) w
  refine ⟨y, ?_⟩
  change Algebra.trace ℚ (RealQuadraticAlgebra 3)
    (mThreeCoefficient *
      (x - caseIIntegerPointValue (m := 3) w) ^ 2) < 2
  calc
    _ = gramCostRat 4 2 4 (x.re + x.im, x.im)
          (w.1 + w.2, w.2) := mthree_trace_formula x w
    _ < 2 := by simpa [p, w] using hz

theorem mfive_two_representative_euclidean :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (5 : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare (by norm_num) small_squarefree_five⟩
    FreeTraceEuclidean (2 : RealQuadraticAlgebra 5) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (5 : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare (by norm_num) small_squarefree_five⟩
  have hbinary := six_binary_forms_trace_euclidean.2.2.2.1
  intro x
  obtain ⟨z, hz⟩ := hbinary (caseIICoordinates (m := 5) x)
  let y : 𝓞 (RealQuadraticAlgebra 5) :=
    caseIIIntegerPointToRing (m := 5) (by norm_num) z
  refine ⟨y, ?_⟩
  change Algebra.trace ℚ (RealQuadraticAlgebra 5)
    ((2 : RealQuadraticAlgebra 5) *
      (x - caseIIIntegerPointValue (m := 5) z) ^ 2) < 2
  calc
    _ = gramCostRat 4 2 6 (caseIICoordinates (m := 5) x) z :=
      mfive_two_trace_formula x z
    _ < 2 := hz

theorem mtwentyone_representative_euclidean :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (21 : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare (by norm_num) small_squarefree_twentyone⟩
    FreeTraceEuclidean mTwentyOneCoefficient := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (21 : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare (by norm_num) small_squarefree_twentyone⟩
  have hbinary := six_binary_forms_trace_euclidean.2.2.2.2.2
  intro x
  let p : PlanePoint ℚ := (-2 * x.im, x.re + 5 * x.im)
  obtain ⟨z, hz⟩ := hbinary p
  let w : IntegralPoint := (z.2 + 3 * z.1, -z.1)
  let y : 𝓞 (RealQuadraticAlgebra 21) :=
    caseIIIntegerPointToRing (m := 21) (by norm_num) w
  refine ⟨y, ?_⟩
  change Algebra.trace ℚ (RealQuadraticAlgebra 21)
    (mTwentyOneCoefficient *
      (x - caseIIIntegerPointValue (m := 21) w) ^ 2) < 2
  calc
    _ = gramCostRat 5 2 5 (-2 * x.im, x.re + 5 * x.im)
          (-w.2, w.1 + 3 * w.2) := mtwentyone_trace_formula x w
    _ < 2 := by simpa [p, w] using hz

end

end TraceEuclidean
