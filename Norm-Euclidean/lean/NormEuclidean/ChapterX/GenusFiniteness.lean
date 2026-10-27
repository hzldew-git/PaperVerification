import NormEuclidean.ChapterX.ClassFiniteness
import NormEuclidean.ChapterX.GenusVolumeFiniteness

/-!
# Actual general genus finiteness and the number-field 104:1 multiplier

Both branches of 103:3 are now proved. Actual genus invariants and rank
induction give ordinary genus finiteness; doubling and the two-sign fibers
give finite proper genus quotients for every norm-integral lattice. The
104:1 endpoint has no supplied arithmetic coverage or class-finiteness premise.
Strong approximation and integrality in 104:3 remain separate work.
-/

noncomputable section

namespace NormEuclidean.GenusFiniteness

open GenusVolumeFiniteness CompletedIntegralLattice IsDedekindDomain
open scoped nonZeroDivisors

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V]

/-- Actual ordinary genus finiteness in any regular number-field space. -/
theorem finite_genus_classes (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (L : Lattice (integerSubring K) Q) (hs : L.scaleIdeal ≤ 1) :
    Finite (GenusClassSet Q L) := by
  letI := L.finiteDimensional
  apply finite_genus_classes_of_volume_representatives Q L hs
  exact ClassFiniteness.finite_volume_classes Q hQ L.volumeIdeal (L.volumeIdeal_ne_zero hQ)

/-- Doubling removes the integral-scale restriction on the norm-integral base lattice. -/
theorem finite_integral_genus_classes (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (L : Lattice (integerSubring K) Q) :
    Finite (GenusClassSet Q L) := by
  apply (finite_genusClassSet_rescale_iff L 2 (by norm_num)).mp
  exact finite_genus_classes ((2 : K) • Q)
    (polarBilin_smul_nondegenerate Q hQ 2 (by norm_num)) (L.rescale 2)
    L.doubled_scaleIdeal_le_one

/-- Proper genus finiteness follows from the actual ordinary quotient and two-sign fibers. -/
theorem finite_integral_proper_genus_classes (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (L : Lattice (integerSubring K) Q) :
    Finite (ProperGenusClassSet Q L) := by
  letI := L.finiteDimensional
  exact ProperClassFiniteness.finite_proper_classes_of_finite_classes Q hQ L
    (finite_integral_genus_classes Q hQ L)

/-- The exact number-field norm-integral 104:1 conclusion, representing the
original divisible value on the original lattice. Both formerly supplied
class-finiteness and almost-everywhere integral-universality premises are proved. -/
theorem exists_integral_divided_value_multiplier (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (L : Lattice (integerSubring K) Q)
    (hdim : 3 ≤ Module.finrank K V) (T : Finset (HeightOneSpectrum (integerSubring K))) :
    ∃ γ : integerSubring K, γ ≠ 0 ∧
      (∀ v ∈ T, IsUnit (⟨algebraMap K (LocalField (integerSubring K) v) (γ : K),
        algebraMap_mem (integerSubring K) v γ.property⟩ : LocalRing (integerSubring K) v)) ∧
      ∀ a : K, (∃ b : integerSubring K, a = (γ : K) * (b : K)) →
        (∃ x : V, Q x = a) →
        (∀ v : HeightOneSpectrum (integerSubring K),
          ∃ z ∈ carrier (integerSubring K) v L.carrier,
            form (integerSubring K) v Q z =
              algebraMap K (LocalField (integerSubring K) v) a) →
        ∃ x ∈ L.carrier, Q x = a := by
  exact LocalIntegralUniversality.exists_divided_value_multiplier_of_finite_classes Q hQ L
    hdim (finite_integral_genus_classes Q hQ L) T

end NormEuclidean.GenusFiniteness
