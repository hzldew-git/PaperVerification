import NormEuclidean.BinaryHilbertGenusClosure
import NormEuclidean.UnaryClassNumber
import NormEuclidean.Maximality

/-!
# The positive-rank norm-Euclidean class-number theorem

Rank one uses the proved line theorem, rank two uses the actual Hilbert
Artin and norm correction chain, and rank at least three uses the proved
principal-ring and hyperbolic strong-approximation theorem. The binary
field identification is expressed in the common separable closure with
the actual negative associated Gram determinant.
-/

noncomputable section

namespace NormEuclidean.ClassNumberTheorem

open scoped NumberField IntermediateField

universe v
variable {K : Type} [Field K] [NumberField K]
  {V : Type v} [Invertible (2 : K)] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- The original positive-rank anisotropic norm-Euclidean lattice has ordinary class number one. -/
theorem class_number_one (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hpos : 1 ≤ Module.finrank K V) : HasLatticeClassNumberOne Q L := by
  by_cases hone : Module.finrank K V = 1
  · exact UnaryClassNumber.classNumberOne L
      (quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hA) hone
  by_cases htwo : Module.finrank K V = 2
  · exact BinaryHilbertGenusClosure.class_number_one L hA hE htwo
  exact ClassNumberClosure.lattice_classNumberOne_of_rank_ge_three L (by omega) hA hE

/-- Maximality is among every integral overmodule, and the ordinary genus has one class. -/
theorem maximal_and_class_number_one (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hpos : 1 ≤ Module.finrank K V) :
    (∀ M : Submodule (integerSubring K) V, L.carrier ≤ M →
      (∀ x ∈ M, Q x ∈ integerSubring K) → L.carrier = M) ∧
        HasLatticeClassNumberOne Q L :=
  ⟨numberField_normEuclidean_maximal Q L hA hE,
    class_number_one L hA hE hpos⟩

/-- The complete positive-rank conclusion, including both field-class-number branches. -/
theorem class_number_theorem (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hpos : 1 ≤ Module.finrank K V) :
    (∀ M : Submodule (integerSubring K) V, L.carrier ≤ M →
      (∀ x ∈ M, Q x ∈ integerSubring K) → L.carrier = M) ∧
    HasLatticeClassNumberOne Q L ∧
    (3 ≤ Module.finrank K V → NumberField.classNumber K = 1) ∧
    (Module.finrank K V = 2 → NumberField.classNumber K ≤ 2 ∧
      ∃ theta : Kˣ, ∃ f : BinaryNormForm.Frame Q theta, ¬ IsSquare theta ∧
        ∃ r : SeparableClosure K,
          r ^ 2 = algebraMap K (SeparableClosure K)
              (-(LinearMap.toMatrix₂ f.basis f.basis Q.associated).det) ∧
            HilbertClassFieldArithmetic.field K ≤ K⟮r⟯ ∧
              (NumberField.classNumber K = 2 ↔ HilbertClassFieldArithmetic.field K = K⟮r⟯)) := by
  refine ⟨numberField_normEuclidean_maximal Q L hA hE,
    class_number_one L hA hE hpos,
    fun hdim ↦ classNumber_eq_one_of_rank_ge_three L hdim hA hE, ?_⟩
  intro hdim
  exact (BinaryHilbertClassFieldComparison.exists_model_and_class_number L hA hE hdim).2

end NormEuclidean.ClassNumberTheorem
