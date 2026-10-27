import NormEuclidean.StableClassNumberUpperBound
import NormEuclidean.StableClassNumberLowerBound
import NormEuclidean.ChapterX.HyperbolicStrongApproximation

/-!
# Stable class-number equality in original rank at least two

The new ideal-label injection supplies the upper bound, and actual ideal
hyperbolic genus members supply the lower bound. The existing uniform kernel
approximation closes the equality when the original rank is at least two.
The unary case is reduced to the specific ternary kernel approximation.
-/

noncomputable section

namespace NormEuclidean.StableClassNumber

open AdelicSpinorKernel
open scoped nonZeroDivisors

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

/-- Kernel approximation, rather than a supplied class-number bound, finishes stable equality. -/
theorem equality_of_kernel_approximation [FiniteDimensional K V]
    (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hpos : 1 ≤ Module.finrank K V)
    (happrox : HasSpinorKernelStrongApproximation (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q
        (quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hA))) :
    OrdinaryGenusMass.classNumber L.hyperbolic = NumberField.classNumber K := by
  exact le_antisymm
    (StableClassNumberUpperBound.classNumber_le Q
      (quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hA) L happrox)
    (StableClassNumberLowerBound.field_classNumber_le_stable L hA hE hpos)

/-- The stable ordinary class number equals the field class number in original rank at least two. -/
theorem equality_of_rank_ge_two (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : 2 ≤ Module.finrank K V) :
    OrdinaryGenusMass.classNumber L.hyperbolic = NumberField.classNumber K := by
  letI := L.finiteDimensional
  exact equality_of_kernel_approximation L hA hE (by omega)
    (HyperbolicStrongApproximation.spinorKernelStrongApproximation Q
      (quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hA) hdim)

/-- The stabilized ordinary genus has exactly one or two classes in original rank at least two. -/
theorem classNumber_eq_one_or_two (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : 2 ≤ Module.finrank K V) :
    OrdinaryGenusMass.classNumber L.hyperbolic = 1 ∨
      OrdinaryGenusMass.classNumber L.hyperbolic = 2 := by
  rw [equality_of_rank_ge_two L hA hE hdim]
  have hpos := NumberField.classNumber_pos K
  have hbound := StableClassNumberLowerBound.field_classNumber_le_two L hA hE (by omega)
  omega

/-- Any actual nonprincipal ideal forces exactly two stable classes
in original rank at least two. -/
theorem classNumber_eq_two_of_nonprincipal (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : 2 ≤ Module.finrank K V)
    (I : FractionalIdeal (integerSubring K)⁰ K) (hI : I ≠ 0)
    (hprincipal : ¬(I : Submodule (integerSubring K) K).IsPrincipal) :
    OrdinaryGenusMass.classNumber L.hyperbolic = 2 := by
  have hlow := StableClassNumberLowerBound.two_le_of_nonprincipal L hA hE I hI hprincipal
  have hbound := StableClassNumberLowerBound.field_classNumber_le_two L hA hE (by omega)
  have heq := equality_of_rank_ge_two L hA hE hdim
  omega

end NormEuclidean.StableClassNumber
