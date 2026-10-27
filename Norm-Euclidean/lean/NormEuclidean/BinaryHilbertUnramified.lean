import NormEuclidean.BinaryHilbertClassFieldComparison
import NormEuclidean.QuadraticUnramifiedArithmetic

/-!
# Unramifiedness of the actual binary discriminant model

In the class-number-two branch, the quadratic algebra used by the completed
norm and spinor constructions is identified over the base with the actual
ordinary Hilbert class field. Integer rings and infinite places are
transported by that algebra equivalence; unramifiedness is a consequence.
-/

noncomputable section

namespace NormEuclidean.BinaryHilbertUnramified

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm
open scoped NumberField IntermediateField

universe v
variable {K : Type} [Field K] [NumberField K]
  {V : Type v} [Invertible (2 : K)] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- The concrete discriminant algebra is the actual ordinary Hilbert class field over `K`. -/
def equiv (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) (hclass : NumberField.classNumber K = 2) :
    letI := quadraticExtensionField theta htheta
    QuadraticAlgebra K (theta : K) 0 ≃ₐ[K] HilbertClassFieldArithmetic.field K := by
  letI := quadraticExtensionField theta htheta
  let hex := IsAlgClosed.exists_pow_nat_eq
    (algebraMap K (SeparableClosure K) (theta : K)) (by decide : 0 < 2)
  let r := Classical.choose hex
  have hr := Classical.choose_spec hex
  exact (QuadraticRootFields.equivAdjoin theta htheta r hr).trans
    (IntermediateField.equivOfEq
      (BinaryHilbertClassFieldComparison.eq_of_class_number_two
        L hA hE hdim theta htheta f r hr hclass).symm)

/-- The identification retains the determinant field norm used by the existing norm chain. -/
theorem norm_equiv (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) (hclass : NumberField.classNumber K = 2) :
    letI := quadraticExtensionField theta htheta
    ∀ z : QuadraticAlgebra K (theta : K) 0,
      Algebra.norm K (equiv L hA hE hdim theta htheta f hclass z) = Algebra.norm K z := by
  letI := quadraticExtensionField theta htheta
  exact Algebra.norm_eq_of_algEquiv (equiv L hA hE hdim theta htheta f hclass)

/-- Both actual ramification predicates hold for the concrete discriminant algebra. -/
theorem everywhere_unramified (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) (hclass : NumberField.classNumber K = 2) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    ClassFieldTheory.IsEverywhereUnramified K (QuadraticAlgebra K (theta : K) 0) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  exact (ClassFieldTheory.isEverywhereUnramified_iff_of_algEquiv K
    (QuadraticAlgebra K (theta : K) 0) (HilbertClassFieldArithmetic.field K)
    (equiv L hA hE hdim theta htheta f hclass)).mpr
      (HilbertClassFieldArithmetic.specification K).1

/-- Every base finite prime is unramified in the actual quadratic integer extension. -/
theorem finite_unramified (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) (hclass : NumberField.classNumber K = 2) :
    QuadraticUnramifiedArithmetic.FiniteUnramified theta htheta :=
  (everywhere_unramified L hA hE hdim theta htheta f hclass).1

/-- No real place becomes complex in the actual quadratic extension. -/
theorem infinite_unramified (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) (hclass : NumberField.classNumber K = 2) :
    QuadraticUnramifiedArithmetic.InfiniteUnramified theta htheta :=
  (everywhere_unramified L hA hE hdim theta htheta f hclass).2.isUnramified

/-- The actual binary parameter is square in every infinite completion, including real ones. -/
theorem infinite_square (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) (hclass : NumberField.classNumber K = 2)
    (w : NumberField.InfinitePlace K) :
    IsSquare (Units.map (algebraMap K w.Completion).toMonoidHom theta) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  apply InfiniteUnramifiedSquareClasses.quadratic_isSquare theta htheta
  exact fun _ z ↦ infinite_unramified L hA hE hdim theta htheta f hclass z.1

end NormEuclidean.BinaryHilbertUnramified
