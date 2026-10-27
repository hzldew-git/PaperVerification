import NormEuclidean.LocalIntegrality
import NormEuclidean.LocalRescaling
import NormEuclidean.GenusClassNumber
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Rescaling the complete ordinary genus class set

For a nonzero integral scalar, scaling preserves the ordinary genus class set.
The inverse construction applies to every integral member of the scaled genus:
finite local isometries first recover integrality for the original form.
Thus surjectivity is proved, not supplied as an arithmetic interface.
-/

namespace NormEuclidean

open CompletedIntegralLattice
open scoped NumberField

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

namespace GenusMember

/-- Rescale a member of the ordinary genus without changing its carrier. -/
def rescale {M : Lattice (integerSubring K) Q}
    (a : integerSubring K) (ha : (a : K) ≠ 0) (N : GenusMember Q M) :
    GenusMember ((a : K) • Q) (M.rescale a) :=
  ⟨N.1.rescale a, (sameGenus_rescale_iff M N.1 a ha).mpr N.2⟩

/-- A member of the scaled genus is integral for the original form as well. -/
theorem integral_of_rescaled_genus {M : Lattice (integerSubring K) Q}
    (a : integerSubring K) (ha : (a : K) ≠ 0)
    (N : GenusMember ((a : K) • Q) (M.rescale a)) :
    ∀ x ∈ N.1.carrier, Q x ∈ integerSubring K := by
  apply integral_of_finiteLocallyIsometric (integerSubring K) M.integral
  exact (finiteLocallyIsometric_rescale_iff (integerSubring K) (a : K) ha).mp N.2.1

/-- Descale any member of the scaled genus, with global integrality derived
from its finite local comparisons. -/
def descale {M : Lattice (integerSubring K) Q}
    (a : integerSubring K) (ha : (a : K) ≠ 0)
    (N : GenusMember ((a : K) • Q) (M.rescale a)) : GenusMember Q M :=
  ⟨{ carrier := N.1.carrier
     finite := N.1.finite
     full := N.1.full
     integral := integral_of_rescaled_genus a ha N },
    (allPlaceLocallyIsometric_rescale_iff (a : K) ha).mp N.2⟩

/-- Scaling and descaling are inverse on all members of the ordinary genus. -/
def rescaleEquiv (M : Lattice (integerSubring K) Q)
    (a : integerSubring K) (ha : (a : K) ≠ 0) :
    GenusMember Q M ≃ GenusMember ((a : K) • Q) (M.rescale a) where
  toFun := rescale a ha
  invFun := descale a ha
  left_inv N := by
    apply Subtype.ext
    cases N with | mk N hN => cases N; rfl
  right_inv N := by
    apply Subtype.ext
    cases N with | mk N hN => cases N; rfl

end GenusMember

/-- A bijection of the complete ordinary genus class sets under rescaling. -/
def genusClassSetRescaleEquiv (M : Lattice (integerSubring K) Q)
    (a : integerSubring K) (ha : (a : K) ≠ 0) :
    GenusClassSet Q M ≃ GenusClassSet ((a : K) • Q) (M.rescale a) :=
  Quotient.congr (GenusMember.rescaleEquiv M a ha) fun _ _ ↦
    (LatticeIsometry.rescale_nonempty_iff (a : K) ha).symm

/-- Finiteness of the ordinary genus class set is unchanged by rescaling. -/
theorem finite_genusClassSet_rescale_iff (M : Lattice (integerSubring K) Q)
    (a : integerSubring K) (ha : (a : K) ≠ 0) :
    Finite (GenusClassSet ((a : K) • Q) (M.rescale a)) ↔ Finite (GenusClassSet Q M) :=
  (genusClassSetRescaleEquiv M a ha).finite_iff.symm

/-- The natural cardinalities agree. To interpret them as numerical class
numbers, independently establish finiteness on one side and transport it with
`finite_genusClassSet_rescale_iff`. This statement does not prove finiteness. -/
theorem card_genusClassSet_rescale (M : Lattice (integerSubring K) Q)
    (a : integerSubring K) (ha : (a : K) ≠ 0) :
    Nat.card (GenusClassSet ((a : K) • Q) (M.rescale a)) = Nat.card (GenusClassSet Q M) :=
  (Nat.card_congr (genusClassSetRescaleEquiv M a ha)).symm

/-- Class number one is unchanged by common nonzero integral rescaling. -/
theorem hasLatticeClassNumberOne_rescale_iff (M : Lattice (integerSubring K) Q)
    (a : integerSubring K) (ha : (a : K) ≠ 0) :
    HasLatticeClassNumberOne ((a : K) • Q) (M.rescale a) ↔ HasLatticeClassNumberOne Q M :=
  (genusClassSetRescaleEquiv M a ha).subsingleton_congr.symm

/-- The doubling required for the binary finiteness argument preserves the
entire ordinary genus class set. -/
def genusClassSetTwoRescaleEquiv (M : Lattice (integerSubring K) Q) :
    GenusClassSet Q M ≃
      GenusClassSet ((2 : K) • Q) (M.rescale (2 : integerSubring K)) :=
  genusClassSetRescaleEquiv M 2 (by norm_num)

end NormEuclidean
