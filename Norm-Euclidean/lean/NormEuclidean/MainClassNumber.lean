import NormEuclidean.ClassNumberTheorem
import NormEuclidean.UnaryStableClassNumber

/-!
# The full positive-rank class-number statement

The conclusion includes the ordinary lattice class number, the stable field
class-number equality, and all three rank branches. The binary field is the
actual negative Gram determinant extension in the separable closure.
-/

noncomputable section

namespace NormEuclidean.MainClassNumber

open scoped NumberField IntermediateField

universe v
variable {K : Type} [Field K] [NumberField K]
  {V : Type v} [Invertible (2 : K)] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- The numerical ordinary class number of the original Euclidean lattice is one. -/
theorem ordinary_class_number_one (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hpos : 1 ≤ Module.finrank K V) : OrdinaryGenusMass.classNumber L = 1 := by
  letI : Subsingleton (GenusClassSet Q L) :=
    ClassNumberTheorem.class_number_one L hA hE hpos
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

/-- Maximality, ordinary and stable class numbers, and all positive-rank field criteria. -/
theorem class_number_theorem (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hpos : 1 ≤ Module.finrank K V) :
    (∀ M : Submodule (integerSubring K) V, L.carrier ≤ M →
      (∀ x ∈ M, Q x ∈ integerSubring K) → L.carrier = M) ∧
    OrdinaryGenusMass.classNumber L = 1 ∧
    NumberField.classNumber K = OrdinaryGenusMass.classNumber L.hyperbolic ∧
    (3 ≤ Module.finrank K V → NumberField.classNumber K = 1) ∧
    (Module.finrank K V = 2 → NumberField.classNumber K ≤ 2 ∧
      ∃ theta : Kˣ, ∃ f : BinaryNormForm.Frame Q theta, ¬ IsSquare theta ∧
        ∃ r : SeparableClosure K,
          r ^ 2 = algebraMap K (SeparableClosure K)
              (-(LinearMap.toMatrix₂ f.basis f.basis Q.associated).det) ∧
            HilbertClassFieldArithmetic.field K ≤ K⟮r⟯ ∧
              (NumberField.classNumber K = 2 ↔ HilbertClassFieldArithmetic.field K = K⟮r⟯)) ∧
    (Module.finrank K V = 1 → NumberField.classNumber K ≤ 2 ∧
      (NumberField.classNumber K = 2 ↔ ¬Module.Free (integerSubring K) L.carrier)) := by
  obtain ⟨hmax, _, hlarge, hbinary⟩ :=
    ClassNumberTheorem.class_number_theorem L hA hE hpos
  refine ⟨hmax, ordinary_class_number_one L hA hE hpos,
    (UnaryStableClassNumber.equality_of_positive_rank L hA hE hpos).symm,
    hlarge, hbinary, ?_⟩
  intro hone
  exact ⟨UnaryFieldClassNumber.classNumber_le_two L hA hE hone,
    UnaryFieldClassNumber.classNumber_eq_two_iff_not_free L hA hE hone⟩

end NormEuclidean.MainClassNumber
