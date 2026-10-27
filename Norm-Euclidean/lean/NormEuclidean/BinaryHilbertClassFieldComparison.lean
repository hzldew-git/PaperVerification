import NormEuclidean.HilbertClassFieldArithmetic
import NormEuclidean.BinaryHilbertComparisonEntry
import NormEuclidean.BinaryClassNumberClosure
import NormEuclidean.BinaryDiscriminantField

/-!
# Binary norm-Euclidean lattices and the actual ordinary Hilbert class field

The field and its arithmetic are constructed independently of the binary
Euclidean hypothesis. The two former Cox arithmetic inputs are supplied
by actual ideal Artin reciprocity and its Frobenius normalization.
-/

noncomputable section

namespace NormEuclidean.BinaryHilbertClassFieldComparison

open IsDedekindDomain ExtensionIdeleNorm
open scoped NumberField IntermediateField NormEuclidean.CompletedExtensionProduct

universe v
variable {K : Type} [Field K] [NumberField K]
  {V : Type v} [Invertible (2 : K)] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- Containment and the class-number-two equality criterion for the constructed Hilbert field. -/
theorem le_and_eq_iff_class_number_two (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) (r : SeparableClosure K)
    (hr : r ^ 2 = algebraMap K (SeparableClosure K) (theta : K)) :
    HilbertClassFieldArithmetic.field K ≤ K⟮r⟯ ∧
      (NumberField.classNumber K = 2 ↔ HilbertClassFieldArithmetic.field K = K⟮r⟯) := by
  apply BinaryHilbertComparisonEntry.le_and_eq_iff_class_number_two
    L hA hE hdim theta htheta f r hr (HilbertClassFieldArithmetic.field K)
    (HilbertClassFieldArithmetic.degree_eq_class_number K)
  exact Filter.Eventually.of_forall fun p hp w ↦
    HilbertClassFieldArithmetic.degree_one_of_principal K p hp w

/-- When the ordinary field class number is two, the discriminant extension is its Hilbert field. -/
theorem eq_of_class_number_two (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) (r : SeparableClosure K)
    (hr : r ^ 2 = algebraMap K (SeparableClosure K) (theta : K))
    (htwo : NumberField.classNumber K = 2) :
    HilbertClassFieldArithmetic.field K = K⟮r⟯ :=
  (le_and_eq_iff_class_number_two L hA hE hdim theta htheta f r hr).2.mp htwo

/-- The complete binary conclusion uses only the original Euclidean and anisotropy hypotheses. -/
theorem class_number_and_hilbert_field (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) (r : SeparableClosure K)
    (hr : r ^ 2 = algebraMap K (SeparableClosure K) (theta : K)) :
    HasLatticeClassNumberOne Q L ∧ NumberField.classNumber K ≤ 2 ∧
      HilbertClassFieldArithmetic.field K ≤ K⟮r⟯ ∧
        (NumberField.classNumber K = 2 ↔ HilbertClassFieldArithmetic.field K = K⟮r⟯) :=
  ⟨BinaryClassNumberClosure.classNumberOne L hA hE hdim,
    BinaryFieldArithmetic.classNumber_le_two L hA hE hdim,
    le_and_eq_iff_class_number_two L hA hE hdim theta htheta f r hr⟩

/-- The original hypotheses also construct the binary determinant model and its comparison. -/
theorem exists_model_and_class_number (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) :
    HasLatticeClassNumberOne Q L ∧ NumberField.classNumber K ≤ 2 ∧
      ∃ theta : Kˣ, ∃ f : BinaryNormForm.Frame Q theta, ¬ IsSquare theta ∧
        ∃ r : SeparableClosure K,
          r ^ 2 = algebraMap K (SeparableClosure K)
              (-(LinearMap.toMatrix₂ f.basis f.basis Q.associated).det) ∧
            HilbertClassFieldArithmetic.field K ≤ K⟮r⟯ ∧
              (NumberField.classNumber K = 2 ↔ HilbertClassFieldArithmetic.field K = K⟮r⟯) := by
  letI := L.finiteDimensional
  obtain ⟨theta, htheta, ⟨f⟩⟩ := BinaryNormForm.exists_frame hA hdim
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap K (SeparableClosure K) (theta : K)) (by decide : 0 < 2)
  refine ⟨BinaryClassNumberClosure.classNumberOne L hA hE hdim,
    BinaryFieldArithmetic.classNumber_le_two L hA hE hdim, theta, f, htheta, r, ?_,
    le_and_eq_iff_class_number_two L hA hE hdim theta htheta f r hr⟩
  exact hr.trans (congrArg (algebraMap K (SeparableClosure K))
    (BinaryDiscriminantField.parameter_eq_neg_det f))

end NormEuclidean.BinaryHilbertClassFieldComparison
