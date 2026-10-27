import NormEuclidean.ChapterX.HyperbolicStrongApproximation
import NormEuclidean.ClassNumberTransfer

/-!
# Hyperbolic class number one and cancellation without hH

Over a principal integer ring the extended ordinary genus has one class
when the original regular rank is at least two. For anisotropic
norm-Euclidean lattices of rank at least three, the existing arithmetic
theorem proves principality; no hH or strong-approximation input remains.
-/

noncomputable section

namespace NormEuclidean.ClassNumberClosure

open AdelicSpinorCorrection AdelicSpinorKernel

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

/-- The enlarged ordinary class number is one under an explicit principal-ring hypothesis. -/
theorem hyperbolic_classNumberOne [FiniteDimensional K V]
    [IsPrincipalIdealRing (integerSubring K)] (L : Lattice (integerSubring K) Q)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : 2 ≤ Module.finrank K V) :
    HasLatticeClassNumberOne (Hyperbolic.form Q) L.hyperbolic :=
  hyperbolic_hasLatticeClassNumberOne_of_kernelApproximation Q hQ L
    (kernelApproximationAt_of_uniform (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ)
      (HyperbolicStrongApproximation.spinorKernelStrongApproximation Q hQ hdim) L.hyperbolic)

/-- Under the original rank-three norm-Euclidean hypotheses, the enlarged ordinary genus is one. -/
theorem hyperbolic_classNumberOne_of_rank_ge_three
    (L : Lattice (integerSubring K) Q) (hdim : 3 ≤ Module.finrank K V)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier) :
    HasLatticeClassNumberOne (Hyperbolic.form Q) L.hyperbolic := by
  letI := L.finiteDimensional
  letI := isPrincipalIdealRing_of_rank_ge_three L hdim hA hE
  exact hyperbolic_classNumberOne L
    (quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hA) (by omega)

/-- Rank at least three removes hH and the separate adelic approximation input. -/
theorem lattice_classNumberOne_of_rank_ge_three
    (L : Lattice (integerSubring K) Q) (hdim : 3 ≤ Module.finrank K V)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier) :
    HasLatticeClassNumberOne Q L :=
  hasLatticeClassNumberOne_of_hyperbolic L hA hE
    (hyperbolic_classNumberOne_of_rank_ge_three L hdim hA hE)

/-- Both field and lattice class number one now follow from the original rank-three hypotheses. -/
theorem field_and_lattice_classNumberOne_of_rank_ge_three
    (L : Lattice (integerSubring K) Q) (hdim : 3 ≤ Module.finrank K V)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier) :
    NumberField.classNumber K = 1 ∧ HasLatticeClassNumberOne Q L :=
  ⟨classNumber_eq_one_of_rank_ge_three L hdim hA hE,
    lattice_classNumberOne_of_rank_ge_three L hdim hA hE⟩

end NormEuclidean.ClassNumberClosure
