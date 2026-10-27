import NormEuclidean.NormIdelePrincipality
import NormEuclidean.BinaryAdelicNorm
import NormEuclidean.FullIdeleClassKernel

/-!
# The binary field class-number bound from norm-Euclidean descent

Actual quadratic idele norms have trivial ordinary ideal class. The proved
global quadratic norm index then gives divisibility of the ordinary field
class number by two. In the exceptional branch the principal-times-norm
subgroup equals the ordinary class kernel. This is an actual subgroup
comparison, not an identification with a constructed Hilbert class field.
-/

noncomputable section

namespace NormEuclidean.BinaryFieldArithmetic

open IsDedekindDomain CompletedIntegralLattice ExtensionIdeleNorm QuadraticExtensionNorm
open scoped NumberField

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

set_option backward.isDefEq.respectTransparency false in
/-- The original Euclidean hypothesis puts actual quadratic idele norms in the ordinary kernel. -/
theorem norm_range_le_class_kernel (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : 2 ≤ Module.finrank K V) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) :
    (quadraticExtensionIdeleNorm theta htheta).range ≤
      (FullIdeleClassKernel.classHom (K := K)).ker := by
  intro i hi
  have hn := (NormFiberAssembly.mem_full_norm_range_iff theta htheta i).mp hi
  exact NormIdelePrincipality.classHom_eq_one L hA hE hdim f
    (FullIdeleClassKernel.finiteProjection i) hn.1

/-- The same containment includes every actual principal idele. -/
theorem principal_norm_le_class_kernel (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : 2 ≤ Module.finrank K V) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) :
    idelePrincipalEmbedding.range ⊔ (quadraticExtensionIdeleNorm theta htheta).range ≤
      (FullIdeleClassKernel.classHom (K := K)).ker := by
  apply sup_le
  · rintro _ ⟨c, rfl⟩
    exact FullIdeleClassKernel.classHom_principal c
  · exact norm_range_le_class_kernel L hA hE hdim theta htheta f

/-- The actual ordinary field class number divides two, with no arithmetic input. -/
theorem classNumber_dvd_two (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) : NumberField.classNumber K ∣ 2 := by
  letI := L.finiteDimensional
  obtain ⟨theta, htheta, ⟨f⟩⟩ := BinaryNormForm.exists_frame hA hdim
  have h := Subgroup.index_dvd_of_le
    (principal_norm_le_class_kernel L hA hE (by omega) theta htheta f)
  have hnorm :
      (idelePrincipalEmbedding.range ⊔ (quadraticExtensionIdeleNorm theta htheta).range).index =
        2 := QuadraticGlobalNormIndex.index_two theta htheta
  rwa [FullIdeleClassKernel.kernel_index, hnorm] at h

/-- The manuscript's binary field class-number bound follows from the original hypotheses. -/
theorem classNumber_le_two (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) : NumberField.classNumber K ≤ 2 :=
  Nat.le_of_dvd (by decide) (classNumber_dvd_two L hA hE hdim)

/-- The only possible ordinary field class numbers are one and two. -/
theorem classNumber_eq_one_or_two (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) :
    NumberField.classNumber K = 1 ∨ NumberField.classNumber K = 2 := by
  have hp := NumberField.classNumber_pos K
  have hb := classNumber_le_two L hA hE hdim
  omega

/-- The exceptional branch has exactly the ordinary principal-times-norm class kernel. -/
theorem classNumber_eq_two_iff_principal_norm_eq_kernel (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) :
    NumberField.classNumber K = 2 ↔
      idelePrincipalEmbedding.range ⊔ (quadraticExtensionIdeleNorm theta htheta).range =
        (FullIdeleClassKernel.classHom (K := K)).ker := by
  have hnorm :
      (idelePrincipalEmbedding.range ⊔ (quadraticExtensionIdeleNorm theta htheta).range).index =
        2 := QuadraticGlobalNormIndex.index_two theta htheta
  constructor
  · intro htwo
    apply FullIdeleClassKernel.eq_of_le_of_index_eq
      (principal_norm_le_class_kernel L hA hE (by omega) theta htheta f)
    · rw [hnorm, FullIdeleClassKernel.kernel_index, htwo]
    · rw [FullIdeleClassKernel.kernel_index, htwo]
      decide
  · intro heq
    have h := congrArg Subgroup.index heq
    rw [hnorm, FullIdeleClassKernel.kernel_index] at h
    exact h.symm

end NormEuclidean.BinaryFieldArithmetic
