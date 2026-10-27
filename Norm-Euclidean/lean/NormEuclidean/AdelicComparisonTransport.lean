import NormEuclidean.AdelicSpinorKernel

/-!
# Transporting actual adelic comparisons between genus members

Changing the reference lattice preserves restrictedness. Two comparisons
from a common lattice give an actual relative comparison, and conjugation
transports the full integral stabilizer to that of the target lattice.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.AdelicComparisonTransport

open IsDedekindDomain CompletedIntegralLattice ProperSpinor AdelicOrthogonal
  AdelicApproximation AdelicSpinorKernel Filter

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)

/-- Any restricted orthogonal family can use another full integral lattice as its reference. -/
def rebase (L M : Lattice (integerSubring K) Q) (a : FiniteAdelicProperOrthogonal Q L) :
    FiniteAdelicProperOrthogonal Q M :=
  ⟨a.1, by
    filter_upwards [a.2, carrier_eventually_eq (integerSubring K) L M] with p hp heq
    simpa only [← heq] using hp⟩

/-- Rebasing leaves every actual completed isometry unchanged. -/
theorem rebase_apply (L M : Lattice (integerSubring K) Q)
    (a : FiniteAdelicProperOrthogonal Q L) (p : HeightOneSpectrum (integerSubring K)) :
    rebase Q L M a p = a p := rfl

/-- Comparisons from a common base compose to an actual comparison between their targets. -/
def relative {L M N : Lattice (integerSubring K) Q}
    (c : FiniteAdelicProperComparison Q L M) (d : FiniteAdelicProperComparison Q L N) :
    FiniteAdelicProperComparison Q M N where
  toAdelic := rebase Q L M (d.toAdelic * c.toAdelic⁻¹)
  maps_carrier p x := by
    have h := c.maps_carrier p (((c.toAdelic p)⁻¹).1.1 x)
    simp only [Subgroup.coe_inv, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] at h
    exact (d.maps_carrier p (((c.toAdelic p)⁻¹).1.1 x)).trans h.symm

/-- The relative comparison has the expected actual orthogonal-group components. -/
theorem relative_apply {L M N : Lattice (integerSubring K) Q}
    (c : FiniteAdelicProperComparison Q L M) (d : FiniteAdelicProperComparison Q L N)
    (p : HeightOneSpectrum (integerSubring K)) :
    (relative Q c d).toAdelic p = d.toAdelic p * (c.toAdelic p)⁻¹ := rfl

/-- Conjugation by an actual integral comparison preserves the whole target completed lattice. -/
theorem conjugate_mem_stabilizer {L M : Lattice (integerSubring K) Q}
    (c : FiniteAdelicProperComparison Q L M)
    (s : FiniteAdelicProperOrthogonal Q L) (hs : IsIntegralAdelic Q L s)
    (p : HeightOneSpectrum (integerSubring K)) :
    c.toAdelic p * s p * (c.toAdelic p)⁻¹ ∈
      properStabilizerWithin (form (integerSubring K) p Q)
        (carrier (integerSubring K) p M.carrier) := by
  intro x
  have hc := c.maps_carrier p (((c.toAdelic p)⁻¹).1.1 x)
  simp only [Subgroup.coe_inv, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] at hc
  exact (c.maps_carrier p ((s p).1.1 (((c.toAdelic p)⁻¹).1.1 x))).trans
    ((hs p (((c.toAdelic p)⁻¹).1.1 x)).trans hc.symm)

/-- The conjugated stabilizer is an actual restricted adelic integral stabilizer of the target. -/
def conjugateIntegral {L M : Lattice (integerSubring K) Q}
    (c : FiniteAdelicProperComparison Q L M)
    (s : FiniteAdelicProperOrthogonal Q L) (hs : IsIntegralAdelic Q L s) :
    FiniteAdelicProperOrthogonal Q M :=
  ⟨fun p ↦ c.toAdelic p * s p * (c.toAdelic p)⁻¹,
    Filter.Eventually.of_forall (conjugate_mem_stabilizer Q c s hs)⟩

/-- The transported adelic element stabilizes at every finite place, including the exceptions. -/
theorem conjugateIntegral_integral {L M : Lattice (integerSubring K) Q}
    (c : FiniteAdelicProperComparison Q L M)
    (s : FiniteAdelicProperOrthogonal Q L) (hs : IsIntegralAdelic Q L s) :
    IsIntegralAdelic Q M (conjugateIntegral Q c s hs) :=
  conjugate_mem_stabilizer Q c s hs

set_option maxHeartbeats 800000 in
/-- Any abelian-valued norm is unchanged under the comparison conjugation. -/
theorem conjugateIntegral_norm {L M : Lattice (integerSubring K) Q}
    (c : FiniteAdelicProperComparison Q L M)
    (s : FiniteAdelicProperOrthogonal Q L) (hs : IsIntegralAdelic Q L s)
    (p : HeightOneSpectrum (integerSubring K)) {A : Type*} [CommGroup A]
    (theta : properGroup (form (integerSubring K) p Q) →* A) :
    theta (conjugateIntegral Q c s hs p) = theta (s p) := by
  change theta (c.toAdelic p * s p * (c.toAdelic p)⁻¹) = _
  rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]

end NormEuclidean.AdelicComparisonTransport
