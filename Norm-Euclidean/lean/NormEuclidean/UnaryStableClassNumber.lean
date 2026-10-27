import NormEuclidean.TernaryStrongApproximation
import NormEuclidean.StableClassNumber
import NormEuclidean.UnaryFieldClassNumber

/-!
# The unary stable class-number equality from the original norm-Euclidean hypothesis

The actual ternary kernel approximation is proved by opposite unipotents and
finite-place scalar approximation. No freeness, class-number, or strong
approximation premise is supplied by the caller.
-/

noncomputable section

namespace NormEuclidean.UnaryStableClassNumber

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

/-- The original unary norm-Euclidean lattice has stable class number equal to the field's. -/
theorem equality (L : Lattice (integerSubring K) Q) (hA : Q.Anisotropic)
    (hE : HasNumberFieldApproximation Q L.carrier) (hdim : Module.finrank K V = 1) :
    OrdinaryGenusMass.classNumber L.hyperbolic = NumberField.classNumber K := by
  letI := L.finiteDimensional
  exact StableClassNumber.equality_of_kernel_approximation L hA hE (by omega)
    (TernaryStrongApproximation.spinorKernelStrongApproximation Q
      (quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hA) hdim L)

/-- Stable class number one is exactly freeness of the original integral line module. -/
theorem eq_one_iff_free (L : Lattice (integerSubring K) Q) (hA : Q.Anisotropic)
    (hE : HasNumberFieldApproximation Q L.carrier) (hdim : Module.finrank K V = 1) :
    OrdinaryGenusMass.classNumber L.hyperbolic = 1 ↔
      Module.Free (integerSubring K) L.carrier := by
  rw [equality L hA hE hdim]
  exact UnaryFieldClassNumber.classNumber_eq_one_iff_free L hA hE hdim

/-- Stable class number two is exactly the nonfree unary branch. -/
theorem eq_two_iff_not_free (L : Lattice (integerSubring K) Q) (hA : Q.Anisotropic)
    (hE : HasNumberFieldApproximation Q L.carrier) (hdim : Module.finrank K V = 1) :
    OrdinaryGenusMass.classNumber L.hyperbolic = 2 ↔
      ¬Module.Free (integerSubring K) L.carrier := by
  rw [equality L hA hE hdim]
  exact UnaryFieldClassNumber.classNumber_eq_two_iff_not_free L hA hE hdim

/-- The two possible stable class numbers, with the actual integral module retained. -/
theorem eq_one_or_two (L : Lattice (integerSubring K) Q) (hA : Q.Anisotropic)
    (hE : HasNumberFieldApproximation Q L.carrier) (hdim : Module.finrank K V = 1) :
    OrdinaryGenusMass.classNumber L.hyperbolic = 1 ∨
      OrdinaryGenusMass.classNumber L.hyperbolic = 2 := by
  rw [equality L hA hE hdim]
  have hp := NumberField.classNumber_pos K
  have hb := UnaryFieldClassNumber.classNumber_le_two L hA hE hdim
  omega

/-- The stable equality now holds in every positive original rank, including rank one. -/
theorem equality_of_positive_rank (L : Lattice (integerSubring K) Q) (hA : Q.Anisotropic)
    (hE : HasNumberFieldApproximation Q L.carrier) (hpos : 1 ≤ Module.finrank K V) :
    OrdinaryGenusMass.classNumber L.hyperbolic = NumberField.classNumber K := by
  by_cases hdim : Module.finrank K V = 1
  · exact equality L hA hE hdim
  · exact StableClassNumber.equality_of_rank_ge_two L hA hE (by omega)

end NormEuclidean.UnaryStableClassNumber
