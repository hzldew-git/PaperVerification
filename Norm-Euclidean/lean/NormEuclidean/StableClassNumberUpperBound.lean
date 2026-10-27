import NormEuclidean.HyperbolicClassSeparation
import NormEuclidean.OrdinaryGenusMass

/-!
# Ordinary stable classes inject into the ordinary field class group

Choose an actual representative of each ordinary genus class, and attach
the ideal class of its actual comparison spinor idele. Equal labels force
global isometry, so this choice defines an injection. Kernel approximation
is the sole remaining geometric input; no freeness or PID is assumed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.StableClassNumberUpperBound

open IsDedekindDomain CompletedIntegralLattice ProperSpinor AdelicOrthogonal
  AdelicApproximation AdelicSpinorKernel AdelicComparison
open scoped NumberField

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
  (L : Lattice (integerSubring K) Q)

/-- The actual ordinary ideal class of the spinor idele of a chosen proper comparison. -/
def memberLabel (A : GenusMember (Hyperbolic.form Q) L.hyperbolic) :
    ClassGroup (integerSubring K) :=
  FiniteIdele.classHom (finiteComparisonSpinorIdele
    (Hyperbolic.form_polarBilin_nondegenerate Q hQ)
    ((hyperbolic_sameGenus_iff_sameProperGenus Q hQ L A.1).mp A.2))

set_option maxHeartbeats 1000000 in
/-- Equal labels of actual genus members imply global integral isometry. -/
theorem globally_isometric_of_label_eq
    (happrox : HasSpinorKernelStrongApproximation (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ))
    (A B : GenusMember (Hyperbolic.form Q) L.hyperbolic)
    (hlabel : memberLabel Q hQ L A = memberLabel Q hQ L B) :
    GloballyIsometric (Hyperbolic.form Q) A.1 B.1 := by
  let hH := Hyperbolic.form_polarBilin_nondegenerate Q hQ
  let ha := (hyperbolic_sameGenus_iff_sameProperGenus Q hQ L A.1).mp A.2
  let hb := (hyperbolic_sameGenus_iff_sameProperGenus Q hQ L B.1).mp B.2
  apply ProperlyGloballyIsometric.globallyIsometric (Hyperbolic.form Q)
  apply HyperbolicClassSeparation.properly_isometric_of_same_ideal_class Q hQ L happrox
    (comparisonOfSameProperGenus ha) (comparisonOfSameProperGenus hb)
    (finiteComparisonSpinorIdele hH ha) (finiteComparisonSpinorIdele hH hb)
  · intro p
    exact (squareClass_component_finiteComparisonSpinorIdele hH ha p).symm
  · intro p
    exact (squareClass_component_finiteComparisonSpinorIdele hH hb p).symm
  · exact hlabel

/-- Choose a representative first; an ideal label need not be invariant under every other choice. -/
def classLabel (x : GenusClassSet (Hyperbolic.form Q) L.hyperbolic) :
    ClassGroup (integerSubring K) := memberLabel Q hQ L x.out

/-- The chosen actual ideal labels inject the full ordinary genus class set into the class group. -/
theorem classLabel_injective
    (happrox : HasSpinorKernelStrongApproximation (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ)) :
    Function.Injective (classLabel Q hQ L) := by
  intro x y h
  have hrel := globally_isometric_of_label_eq Q hQ L happrox x.out y.out h
  exact (Quotient.out_equiv_out).mp hrel

/-- The actual ordinary stable class number is bounded by the actual ordinary field class number. -/
theorem classNumber_le
    (happrox : HasSpinorKernelStrongApproximation (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ)) :
    OrdinaryGenusMass.classNumber L.hyperbolic ≤ NumberField.classNumber K := by
  letI : Fintype (ClassGroup (integerSubring K)) :=
    inferInstanceAs (Fintype (ClassGroup (𝓞 K)))
  change Nat.card (GenusClassSet (Hyperbolic.form Q) L.hyperbolic) ≤ _
  calc
    _ ≤ Nat.card (ClassGroup (integerSubring K)) :=
      Nat.card_le_card_of_injective _ (classLabel_injective Q hQ L happrox)
    _ = NumberField.classNumber K := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_congr (Equiv.refl _)

end NormEuclidean.StableClassNumberUpperBound
