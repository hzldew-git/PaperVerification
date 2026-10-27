import NormEuclidean.HilbertIdeleArtin
import NormEuclidean.BinaryHilbertNormCorrection

/-!
# The actual Hilbert Artin kernel and the binary discriminant idele norm

The exceptional binary norm quotient is identified with the Galois group
of the constructed ordinary Hilbert class field. This is the actual
arithmetic Artin map on the existing full idele group.
-/

noncomputable section

namespace NormEuclidean.BinaryHilbertArtinNorm

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm
open scoped NumberField

universe v
variable {K : Type} [Field K] [NumberField K]
  {V : Type v} [Invertible (2 : K)] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- The actual Hilbert Artin kernel is principal times the discriminant extension norm range. -/
theorem ker_eq_principal_norm (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) (hclass : NumberField.classNumber K = 2) :
    (HilbertIdeleArtin.artin K).ker =
      idelePrincipalEmbedding.range ⊔ (quadraticExtensionIdeleNorm theta htheta).range :=
  (HilbertIdeleArtin.ker_eq K).trans
    (BinaryHilbertNormCorrection.principal_norm_eq_kernel L hA hE hdim theta htheta f hclass).symm

/-- Every actual discriminant extension idele norm acts trivially on the Hilbert field. -/
theorem norm (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) (hclass : NumberField.classNumber K = 2)
    (i : NumberFieldIdele K) (hi : i ∈ (quadraticExtensionIdeleNorm theta htheta).range) :
    HilbertIdeleArtin.artin K i = 1 := by
  change i ∈ (HilbertIdeleArtin.artin K).ker
  rw [ker_eq_principal_norm L hA hE hdim theta htheta f hclass]
  exact (show (quadraticExtensionIdeleNorm theta htheta).range ≤
    idelePrincipalEmbedding.range ⊔ (quadraticExtensionIdeleNorm theta htheta).range
      from le_sup_right) hi

/-- A trivial arithmetic Artin automorphism is exactly an actual principal-times-norm idele. -/
theorem artin_eq_one_iff (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) (hclass : NumberField.classNumber K = 2)
    (i : NumberFieldIdele K) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    HilbertIdeleArtin.artin K i = 1 ↔
      ∃ c : Kˣ, ∃ j : NumberFieldIdele (QuadraticAlgebra K (theta : K) 0),
        i = idelePrincipalEmbedding c * extensionIdeleNorm j := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  change i ∈ (HilbertIdeleArtin.artin K).ker ↔ _
  rw [ker_eq_principal_norm L hA hE hdim theta htheta f hclass]
  constructor
  · intro hi
    obtain ⟨_, ⟨c, rfl⟩, _, ⟨j, rfl⟩, h⟩ := Subgroup.mem_sup.mp hi
    exact ⟨c, j, h.symm⟩
  · rintro ⟨c, j, rfl⟩
    exact Subgroup.mul_mem_sup ⟨c, rfl⟩ ⟨j, rfl⟩

/-- Arithmetic reciprocity identifies the actual binary norm quotient with the Hilbert group. -/
def quotientEquiv (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) (hclass : NumberField.classNumber K = 2) :
    NumberFieldIdele K ⧸
      (idelePrincipalEmbedding.range ⊔ (quadraticExtensionIdeleNorm theta htheta).range) ≃*
        ((HilbertClassFieldArithmetic.field K) ≃ₐ[K] (HilbertClassFieldArithmetic.field K)) :=
  (QuotientGroup.quotientMulEquivOfEq
    (ker_eq_principal_norm L hA hE hdim theta htheta f hclass).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (HilbertIdeleArtin.artin K) (HilbertIdeleArtin.surjective K))

/-- The quotient comparison evaluates to the actual arithmetic Artin automorphism. -/
theorem quotientEquiv_mk (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) (hclass : NumberField.classNumber K = 2)
    (i : NumberFieldIdele K) :
    quotientEquiv L hA hE hdim theta htheta f hclass (QuotientGroup.mk i) =
      HilbertIdeleArtin.artin K i := rfl

end NormEuclidean.BinaryHilbertArtinNorm
