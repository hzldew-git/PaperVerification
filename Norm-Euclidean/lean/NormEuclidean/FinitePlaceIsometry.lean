import NormEuclidean.CompletedIntegralLattice

/-!
# Actual isometries at every finite completion

This relation quantifies over mathlib's height-one primes of `R` and over actual
isometries of the completed integral lattices. It is not an assumed genus or
class-number interface. Archimedean comparison and the local-to-global theorem
of Xu–Zhang are not asserted here. When `R` is the full ring of integers
of a number field, these primes are precisely its finite places.
-/

namespace NormEuclidean.CompletedIntegralLattice

open IsDedekindDomain
variable {K V W U : Type*} [Field K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup U] [Module K U]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]

/-- Actual integral isometries at all height-one places of `R`.
No global isometry is assumed. For a full number ring these are all finite places. -/
def FiniteLocallyIsometric (Q : QuadraticForm K V) (Q' : QuadraticForm K W)
    (L : Submodule R V) (L' : Submodule R W) : Prop :=
  ∀ v : HeightOneSpectrum R,
    Nonempty (LatticeIsometry (form R v Q) (form R v Q') (carrier R v L) (carrier R v L'))

theorem finiteLocallyIsometric_refl (Q : QuadraticForm K V) (L : Submodule R V) :
    FiniteLocallyIsometric R Q Q L L := by
  intro v
  exact ⟨{ toLinearEquiv := LinearEquiv.refl _ _
           q_eq := fun _ => rfl
           mem_iff := fun _ => Iff.rfl }⟩

theorem finiteLocallyIsometric_symm {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
    {L : Submodule R V} {L' : Submodule R W}
    (h : FiniteLocallyIsometric R Q Q' L L') : FiniteLocallyIsometric R Q' Q L' L := by
  intro v
  obtain ⟨e⟩ := h v
  exact ⟨{ toLinearEquiv := e.toLinearEquiv.symm
           q_eq := fun z => by simpa using (e.q_eq (e.toLinearEquiv.symm z)).symm
           mem_iff := fun z => by simpa using (e.mem_iff (e.toLinearEquiv.symm z)).symm }⟩

theorem finiteLocallyIsometric_trans {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
    {Q'' : QuadraticForm K U} {L : Submodule R V} {L' : Submodule R W} {L'' : Submodule R U}
    (h : FiniteLocallyIsometric R Q Q' L L') (h' : FiniteLocallyIsometric R Q' Q'' L' L'') :
    FiniteLocallyIsometric R Q Q'' L L'' := by
  intro v
  obtain ⟨e⟩ := h v
  obtain ⟨f⟩ := h' v
  exact ⟨{ toLinearEquiv := e.toLinearEquiv.trans f.toLinearEquiv
           q_eq := fun z => (f.q_eq (e.toLinearEquiv z)).trans (e.q_eq z)
           mem_iff := fun z => (f.mem_iff (e.toLinearEquiv z)).trans (e.mem_iff z) }⟩

/-- Global integral isometry implies actual finite local integral isometry. -/
theorem finiteLocallyIsometric_of_isometry {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
    {L : Submodule R V} {L' : Submodule R W} (e : LatticeIsometry Q Q' L L') :
    FiniteLocallyIsometric R Q Q' L L' := fun v => ⟨isometry R v e⟩

end NormEuclidean.CompletedIntegralLattice
