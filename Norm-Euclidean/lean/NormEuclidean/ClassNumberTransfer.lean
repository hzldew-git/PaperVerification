import NormEuclidean.GenusClassNumber
import NormEuclidean.NumberFieldCancellation
import NormEuclidean.UnconditionalClassNumber
import NormEuclidean.GlobalLatticeRecovery
import NormEuclidean.QuadraticBaseChangeNondegenerate
import NormEuclidean.AdelicSpinorCorrection

/-!
# Transfer of class number one through hyperbolic cancellation

Once every lattice in the ordinary genus of `L ⊥ H` is globally isometric to
`L ⊥ H`, the established norm-Euclidean cancellation theorem shows that every
lattice in the ordinary genus of `L` is globally isometric to `L`.  This file
formalizes that implication.  The cited global theorem proving class number one
for the enlarged indefinite lattice remains a separate input.
-/

namespace NormEuclidean

open scoped NumberField

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V}

/-- Class number one for the enlarged ordinary genus descends to the original
norm-Euclidean anisotropic lattice by hyperbolic cancellation. -/
theorem hasLatticeClassNumberOne_of_hyperbolic
    (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hH : HasLatticeClassNumberOne (Hyperbolic.form Q) L.hyperbolic) :
    HasLatticeClassNumberOne Q L := by
  rw [hasLatticeClassNumberOne_iff Q]
  intro M hgen
  have hgenH : SameGenus (Hyperbolic.form Q) L.hyperbolic M.hyperbolic :=
    sameGenus_hyperbolic hgen
  have hglobalH : GloballyIsometric (Hyperbolic.form Q) L.hyperbolic M.hyperbolic :=
    (hasLatticeClassNumberOne_iff (Hyperbolic.form Q) L.hyperbolic).mp
      hH M.hyperbolic hgenH
  obtain ⟨e⟩ := hglobalH
  let φ : Hyperbolic.Isometry Q Q M.carrier L.carrier := {
    toLinearEquiv := e.inverse.toLinearEquiv
    q_eq := e.inverse.q_eq
    mem_iff := fun z => by
      change e.inverse.toLinearEquiv z ∈ Hyperbolic.submodule L.carrier ↔
        z ∈ Hyperbolic.submodule M.carrier
      exact e.inverse.mem_iff z }
  obtain ⟨g⟩ := Hyperbolic.norm_euclidean_cancellation
    (numberFieldNorm K) L.integral hA hE φ
  exact ⟨g.inverse⟩

/-- The adelic route removes the packaged `h(L ⊥ H) = 1` hypothesis from
the cancellation theorem.  Its two explicit inputs are precisely the
completion-descent statement and the finite adelic Spin strong-approximation
hit used to prove that packaged conclusion. -/
theorem hasLatticeClassNumberOne_of_adelicStrongApproximation
    [FiniteDimensional K V]
    (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hrecover :
      AdelicApproximation.CompletedCarriersRecoverGlobalLattices
        (Hyperbolic.form Q))
    (happrox :
      AdelicApproximation.HasFiniteAdelicStrongApproximation
        (Hyperbolic.form Q)) :
    HasLatticeClassNumberOne Q L := by
  apply hasLatticeClassNumberOne_of_hyperbolic L hA hE
  exact AdelicApproximation.hyperbolic_hasLatticeClassNumberOne Q
    (quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hA)
    L hrecover happrox

/-- Completion descent is now a theorem. The only remaining input to this
adelic cancellation endpoint is the global hit principle for the hyperbolic
enlargement; its proof still requires spinor correction and strong approximation. -/
theorem hasLatticeClassNumberOne_of_adelicHits
    [FiniteDimensional K V]
    (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (happrox : AdelicApproximation.HasFiniteAdelicStrongApproximation (Hyperbolic.form Q)) :
    HasLatticeClassNumberOne Q L := by
  apply hasLatticeClassNumberOne_of_hyperbolic L hA hE
  exact AdelicApproximation.hyperbolic_hasLatticeClassNumberOne_of_adelicHits Q
    (quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hA) L happrox

/-- In rank at least three, the existing arithmetic argument gives field class
number one; the preceding transfer gives lattice class number one once the
enlarged ordinary genus has one class. -/
theorem field_and_lattice_classNumberOne_of_rank_ge_three
    (L : Lattice (integerSubring K) Q) (hdim : 3 ≤ Module.finrank K V)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hH : HasLatticeClassNumberOne (Hyperbolic.form Q) L.hyperbolic) :
    NumberField.classNumber K = 1 ∧ HasLatticeClassNumberOne Q L :=
  ⟨classNumber_eq_one_of_rank_ge_three L hdim hA hE,
    hasLatticeClassNumberOne_of_hyperbolic L hA hE hH⟩

/-- Rank at least three gives the field class-number conclusion, while the
adelic recovery and approximation inputs give the lattice conclusion without
an `hH` parameter. -/
theorem field_and_lattice_classNumberOne_of_rank_ge_three_and_adelic
    [FiniteDimensional K V]
    (L : Lattice (integerSubring K) Q) (hdim : 3 ≤ Module.finrank K V)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hrecover :
      AdelicApproximation.CompletedCarriersRecoverGlobalLattices
        (Hyperbolic.form Q))
    (happrox :
      AdelicApproximation.HasFiniteAdelicStrongApproximation
        (Hyperbolic.form Q)) :
    NumberField.classNumber K = 1 ∧ HasLatticeClassNumberOne Q L :=
  ⟨classNumber_eq_one_of_rank_ge_three L hdim hA hE,
    hasLatticeClassNumberOne_of_adelicStrongApproximation
      L hA hE hrecover happrox⟩

/-- The rank-at-least-three endpoint supplies global completion recovery
internally, leaving the hyperbolic adelic hit principle as the outstanding input. -/
theorem field_and_lattice_classNumberOne_of_rank_ge_three_and_adelicHits
    [FiniteDimensional K V]
    (L : Lattice (integerSubring K) Q) (hdim : 3 ≤ Module.finrank K V)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (happrox : AdelicApproximation.HasFiniteAdelicStrongApproximation (Hyperbolic.form Q)) :
    NumberField.classNumber K = 1 ∧ HasLatticeClassNumberOne Q L :=
  ⟨classNumber_eq_one_of_rank_ge_three L hdim hA hE,
    hasLatticeClassNumberOne_of_adelicHits L hA hE happrox⟩

/-- In rank at least three, arithmetic supplies the PID hypothesis and the
proved spinor correction supplies its witnesses. Only kernel approximation
at the fixed hyperbolic lattice remains as a geometric input. -/
theorem hasLatticeClassNumberOne_of_rank_ge_three_and_kernelApproximation
    [FiniteDimensional K V]
    (L : Lattice (integerSubring K) Q) (hdim : 3 ≤ Module.finrank K V)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (happrox : AdelicSpinorCorrection.HasSpinorKernelApproximationAt (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q
        (quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hA)) L.hyperbolic) :
    HasLatticeClassNumberOne Q L := by
  letI := isPrincipalIdealRing_of_rank_ge_three L hdim hA hE
  apply hasLatticeClassNumberOne_of_hyperbolic L hA hE
  exact AdelicSpinorCorrection.hyperbolic_hasLatticeClassNumberOne_of_kernelApproximation Q
    (quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hA) L happrox

/-- The field and lattice class-number conclusions with no packaged enlarged
class number, completion recovery, correction witnesses, or all-lattice hit input. -/
theorem field_and_lattice_classNumberOne_of_rank_ge_three_and_kernelApproximation
    [FiniteDimensional K V]
    (L : Lattice (integerSubring K) Q) (hdim : 3 ≤ Module.finrank K V)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (happrox : AdelicSpinorCorrection.HasSpinorKernelApproximationAt (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q
        (quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hA)) L.hyperbolic) :
    NumberField.classNumber K = 1 ∧ HasLatticeClassNumberOne Q L :=
  ⟨classNumber_eq_one_of_rank_ge_three L hdim hA hE,
    hasLatticeClassNumberOne_of_rank_ge_three_and_kernelApproximation L hdim hA hE happrox⟩

end NormEuclidean
