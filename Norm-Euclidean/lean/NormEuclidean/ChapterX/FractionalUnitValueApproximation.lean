import NormEuclidean.ChapterX.SupportedVectorDenominator
import NormEuclidean.ChapterX.UnitValueStrongApproximation

/-!
# Unit-value vector approximation with fractional targets

At the finitely many target primes the vectors may have arbitrary
denominators. At every other finite prime the output is in the original
completed module. The excluded isotropic place is infinite.
-/

noncomputable section

namespace NormEuclidean.FractionalUnitValueApproximation

open IsDedekindDomain CompletedIntegralLattice ScalarIntegralApproximation
  LocalPrimitivePairing ProjectedComplement Filter Topology
open scoped NormEuclidean.OrthogonalTopology

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

set_option backward.isDefEq.respectTransparency false in
/-- Unit-value approximation with arbitrary finite targets and literal off-target integrality. -/
theorem exists_vector (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : 4 ≤ Module.finrank K V) (L : Submodule (integerSubring K) V) (hfg : L.FG)
    (hfull : Submodule.span K (L : Set V) = ⊤) (a : (integerSubring K)ˣ)
    (hrep : ∃ x : V, Q x = ((a : integerSubring K) : K))
    (T : Finset (HeightOneSpectrum (integerSubring K)))
    (hdyadic : ∀ p : HeightOneSpectrum (integerSubring K),
      (2 : integerSubring K) ∈ p.asIdeal → p ∈ T)
    (hunimodular : ∀ p : HeightOneSpectrum (integerSubring K), p ∉ T →
      SelfDual (LocalRing (integerSubring K) p) (halfPolar (form _ p Q))
        (carrier (integerSubring K) p L))
    (q : NumberField.InfinitePlace K) (hiso : ¬ (Q.baseChange q.Completion).Anisotropic)
    (z : (p : T) → Space (V := V) (integerSubring K) p.1)
    (hz : ∀ p, form (integerSubring K) p.1 Q (z p) =
      algebraMap K (LocalField (integerSubring K) p.1) ((a : integerSubring K) : K))
    (W : (p : T) → Set (Space (V := V) (integerSubring K) p.1))
    (hW : ∀ p, W p ∈ 𝓝 (z p)) :
    ∃ x : V, Q x = ((a : integerSubring K) : K) ∧
      (∀ p : T, inclusion (integerSubring K) p.1 x ∈ W p) ∧
      ∀ p : HeightOneSpectrum (integerSubring K), p ∉ T →
        inclusion (integerSubring K) p x ∈ carrier (integerSubring K) p L := by
  obtain ⟨M, hMfg, hMfull, hzM, hout⟩ :=
    SupportedVectorDenominator.exists_module L hfg hfull T z
  have hMself (p : HeightOneSpectrum (integerSubring K)) (hp : p ∉ T) :
      SelfDual (LocalRing (integerSubring K) p) (halfPolar (form _ p Q))
        (carrier (integerSubring K) p M) := by
    rw [hout p hp]
    exact hunimodular p hp
  obtain ⟨x, hxM, hxQ, hxW⟩ := UnitValueStrongApproximation.exists_vector Q hQ hdim
    M hMfg hMfull a hrep T hdyadic hMself q hiso z hz hzM W hW
  refine ⟨x, hxQ, hxW, fun p hp ↦ ?_⟩
  rw [← hout p hp]
  exact inclusion_mem (integerSubring K) p M hxM

end NormEuclidean.FractionalUnitValueApproximation
