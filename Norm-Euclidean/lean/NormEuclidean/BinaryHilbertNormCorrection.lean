import NormEuclidean.BinaryHilbertUnramified

/-!
# Binary ordinary idele norm correction from the Hilbert class field

The two unramifiedness inputs of the earlier correction theorem are now
consequences of the original Euclidean data and class number two. The
reverse implications retain the exact boundary of this exceptional branch.
-/

noncomputable section

namespace NormEuclidean.BinaryHilbertNormCorrection

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm FullIdeleClassKernel
open scoped NumberField

universe v
variable {K : Type} [Field K] [NumberField K]
  {V : Type v} [Invertible (2 : K)] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- The actual Hilbert field supplies every ordinary unit idele norm preimage. -/
theorem unitIdeles_le_norm (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) (hclass : NumberField.classNumber K = 2) :
    unitIdeles ≤ (quadraticExtensionIdeleNorm theta htheta).range :=
  QuadraticUnramifiedArithmetic.unitIdeles_le_norm theta htheta
    (BinaryHilbertUnramified.finite_unramified L hA hE hdim theta htheta f hclass)
    (BinaryHilbertUnramified.infinite_unramified L hA hE hdim theta htheta f hclass)

/-- The principal-times-norm subgroup is the ordinary ideal class kernel, with no local input. -/
theorem principal_norm_eq_kernel (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) (hclass : NumberField.classNumber K = 2) :
    idelePrincipalEmbedding.range ⊔ (quadraticExtensionIdeleNorm theta htheta).range =
      (FullIdeleClassKernel.classHom (K := K)).ker :=
  FullIdeleClassKernel.principal_norm_eq_kernel theta htheta hclass
    (unitIdeles_le_norm L hA hE hdim theta htheta f hclass)

/-- Unit norm surjectivity in this binary Euclidean setting forces field class number two. -/
theorem class_number_two_of_unit_norms (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta)
    (hunit : unitIdeles ≤ (quadraticExtensionIdeleNorm theta htheta).range) :
    NumberField.classNumber K = 2 := by
  apply (BinaryFieldArithmetic.classNumber_eq_two_iff_principal_norm_eq_kernel
    L hA hE hdim theta htheta f).mpr
  apply le_antisymm
    (BinaryFieldArithmetic.principal_norm_le_class_kernel L hA hE (by omega) theta htheta f)
  rw [FullIdeleClassKernel.ker_eq]
  exact sup_le_sup_left hunit _

/-- Ordinary unit norm surjectivity holds exactly in the exceptional class-number-two branch. -/
theorem unit_norms_iff_class_number_two (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) :
    unitIdeles ≤ (quadraticExtensionIdeleNorm theta htheta).range ↔
      NumberField.classNumber K = 2 :=
  ⟨class_number_two_of_unit_norms L hA hE hdim theta htheta f,
    unitIdeles_le_norm L hA hE hdim theta htheta f⟩

/-- Actual everywhere-unramifiedness has the same exact exceptional-branch boundary. -/
theorem unramified_iff_class_number_two (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) :
    (QuadraticUnramifiedArithmetic.FiniteUnramified theta htheta ∧
      QuadraticUnramifiedArithmetic.InfiniteUnramified theta htheta) ↔
        NumberField.classNumber K = 2 := by
  constructor
  · rintro ⟨hfinite, hinfinite⟩
    exact class_number_two_of_unit_norms L hA hE hdim theta htheta f
      (QuadraticUnramifiedArithmetic.unitIdeles_le_norm theta htheta hfinite hinfinite)
  · intro hclass
    exact ⟨BinaryHilbertUnramified.finite_unramified L hA hE hdim theta htheta f hclass,
      BinaryHilbertUnramified.infinite_unramified L hA hE hdim theta htheta f hclass⟩

/-- At class number one some ordinary unit idele is not a discriminant extension norm. -/
theorem exists_unit_not_norm_of_class_number_one (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) (hclass : NumberField.classNumber K = 1) :
    ∃ i : unitIdeles (K := K), i.1 ∉ (quadraticExtensionIdeleNorm theta htheta).range := by
  classical
  by_contra h
  have hunit : unitIdeles ≤ (quadraticExtensionIdeleNorm theta htheta).range := by
    intro i hi
    by_contra hn
    exact h ⟨⟨i, hi⟩, hn⟩
  have htwo := class_number_two_of_unit_norms L hA hE hdim theta htheta f hunit
  omega

/-- Every actual norm has a principal-times-ordinary-unit decomposition with no local premise. -/
theorem exists_norm_decomposition (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) (hclass : NumberField.classNumber K = 2)
    (i : NumberFieldIdele K) (hi : i ∈ (quadraticExtensionIdeleNorm theta htheta).range) :
    ∃ c : Kˣ, ∃ u : unitIdeles (K := K), i = idelePrincipalEmbedding c * u.1 :=
  QuadraticIdeleClassCorrection.exists_norm_decomposition theta htheta hclass
    (unitIdeles_le_norm L hA hE hdim theta htheta f hclass) i hi

end NormEuclidean.BinaryHilbertNormCorrection
