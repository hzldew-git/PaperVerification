import NormEuclidean.DyadicUnramifiedSquareClasses
import NormEuclidean.InfiniteUnramifiedSquareClasses
import NormEuclidean.BinaryUnramifiedClassNumber

/-!
# Ordinary class correction from actual everywhere unramified extensions

Finite unramifiedness is mathlib's integer-ring predicate; infinite
unramifiedness is its actual infinite-place predicate. All three completed
square-class conditions and the unit-idele norm inclusion are consequences.
The field class-number bound and unramifiedness themselves are retained
arithmetic inputs, not asserted consequences of the Euclidean hypothesis.
-/

noncomputable section

namespace NormEuclidean.QuadraticUnramifiedArithmetic

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm Bong.Dyadic
open scoped NumberField

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- Every finite prime is unramified in the actual quadratic integer extension. -/
def FiniteUnramified (theta : Kˣ) (htheta : ¬ IsSquare theta) : Prop :=
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  ∀ p : HeightOneSpectrum (𝓞 K),
    Algebra.IsUnramifiedIn (𝓞 (QuadraticAlgebra K (theta : K) 0)) p.asIdeal

/-- No real place becomes complex in the actual quadratic extension. -/
def InfiniteUnramified (theta : Kˣ) (htheta : ¬ IsSquare theta) : Prop :=
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  ∀ w : NumberField.InfinitePlace (QuadraticAlgebra K (theta : K) 0), w.IsUnramified K

/-- The global integer-ring predicate applies to each actual finite completion factor. -/
theorem finite_at (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (hfinite : FiniteUnramified theta htheta) (p : HeightOneSpectrum (𝓞 K)) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    ∀ w : FinitePlacesAbove (E := QuadraticAlgebra K (theta : K) 0) p,
      Algebra.IsUnramifiedAt (𝓞 K) w.1.asIdeal := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  intro w
  exact hfinite p w.1.asIdeal w.1.isPrime
    ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩

/-- Actual unramifiedness supplies the entire ordinary unit-idele norm inclusion. -/
theorem unitIdeles_le_norm (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (hfinite : FiniteUnramified theta htheta)
    (hinfty : InfiniteUnramified theta htheta) :
    FullIdeleClassKernel.unitIdeles ≤ (quadraticExtensionIdeleNorm theta htheta).range := by
  apply BinaryUnramifiedClassNumber.unitIdeles_le_norm theta htheta
  · intro p _
    exact FiniteUnramifiedSquareClasses.quadratic_even_order theta htheta p
      (finite_at theta htheta hfinite p)
  · intro p hp
    exact DyadicUnramifiedSquareClasses.quadratic_defect_ge_twoE theta htheta p hp
      (finite_at theta htheta hfinite p)
  · apply InfiniteUnramifiedSquareClasses.quadratic_isSquare theta htheta
    exact fun _ w ↦ hinfty w.1

/-- The ordinary class kernel is obtained from the actual unramified quadratic norm range. -/
theorem principal_norm_eq_kernel (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (hclass : NumberField.classNumber K = 2)
    (hfinite : FiniteUnramified theta htheta)
    (hinfty : InfiniteUnramified theta htheta) :
    idelePrincipalEmbedding.range ⊔ (quadraticExtensionIdeleNorm theta htheta).range =
      (FullIdeleClassKernel.classHom (K := K)).ker :=
  FullIdeleClassKernel.principal_norm_eq_kernel theta htheta hclass
    (unitIdeles_le_norm theta htheta hfinite hinfty)

variable {V : Type*} [Invertible (2 : K)] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- The exceptional binary branch needs no remaining local square-class hypotheses. -/
theorem classNumberOne_of_unramified (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) (hclass : NumberField.classNumber K = 2)
    (hfinite : FiniteUnramified theta htheta)
    (hinfty : InfiniteUnramified theta htheta) : HasLatticeClassNumberOne Q L :=
  BinaryClassNumberCorrection.classNumberOne_of_norm_units Q L hA hE hdim theta htheta f hclass
    (unitIdeles_le_norm theta htheta hfinite hinfty)

/-- The unramified arithmetic is required only when the field class number is two. -/
theorem classNumberOne_of_classNumber_le_two (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) (hbound : NumberField.classNumber K ≤ 2)
    (hfinite : NumberField.classNumber K = 2 → FiniteUnramified theta htheta)
    (hinfty : NumberField.classNumber K = 2 → InfiniteUnramified theta htheta) :
    HasLatticeClassNumberOne Q L := by
  apply BinaryUnramifiedClassNumber.classNumberOne_of_classNumber_le_two L hA hE hdim
    theta htheta f hbound
  · intro htwo p _
    exact FiniteUnramifiedSquareClasses.quadratic_even_order theta htheta p
      (finite_at theta htheta (hfinite htwo) p)
  · intro htwo p hp
    exact DyadicUnramifiedSquareClasses.quadratic_defect_ge_twoE theta htheta p hp
      (finite_at theta htheta (hfinite htwo) p)
  · intro htwo
    apply InfiniteUnramifiedSquareClasses.quadratic_isSquare theta htheta
    exact fun _ w ↦ hinfty htwo w.1

end NormEuclidean.QuadraticUnramifiedArithmetic
