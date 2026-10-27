import NormEuclidean.ChapterX.HasseResidualCorrection
import NormEuclidean.ChapterX.IntegralPreliminaryVector

/-!
# The integral-unit, infinite-excluded branch of O'Meara 104:3

Local targets are arbitrary points of the fixed-value fibers in the actual
completed lattice. Weak approximation and a denominator prime to the
targets construct the preliminary vector. The proved residual correction
then gives an actual global integral vector with the exact target value.

The excluded place is infinite; dyadic and non-unimodular places must
already be among the finite targets. This does not assert the other
branches of the full 104:3 theorem.
-/

noncomputable section

namespace NormEuclidean.UnitValueStrongApproximation

open IsDedekindDomain CompletedIntegralLattice ScalarIntegralApproximation LocalPrimitivePairing
  ProjectedComplement Filter Topology
open scoped NormEuclidean.OrthogonalTopology

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

set_option backward.isDefEq.respectTransparency false in
/-- Arbitrary finite integral targets for a represented integral unit can be met globally. -/
theorem exists_vector (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : 4 ≤ Module.finrank K V) (L : Submodule (integerSubring K) V) (hfg : L.FG)
    (hfull : Submodule.span K (L : Set V) = ⊤) (a : (integerSubring K)ˣ)
    (hrep : ∃ y : V, Q y = ((a : integerSubring K) : K))
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
    (hzL : ∀ p, z p ∈ carrier (integerSubring K) p.1 L)
    (W : (p : T) → Set (Space (V := V) (integerSubring K) p.1))
    (hW : ∀ p, W p ∈ 𝓝 (z p)) :
    ∃ y ∈ L, Q y = ((a : integerSubring K) : K) ∧
      ∀ p : T, inclusion (integerSubring K) p.1 y ∈ W p := by
  classical
  choose U hUW hU hzU using fun p : T ↦ mem_nhds_iff.mp (hW p)
  have hcar (p : T) : IsOpen
      (carrier (integerSubring K) p.1 L : Set (Space (V := V) (integerSubring K) p.1)) :=
    OrthogonalTopology.isOpen_of_full _ (OrthogonalTopology.isOpen_localRing _ _)
      _ (carrier_full _ _ _ hfull)
  have hnb (p : T) : U p ∩ carrier (integerSubring K) p.1 L ∈ 𝓝 (z p) :=
    inter_mem ((hU p).mem_nhds (hzU p)) ((hcar p).mem_nhds (hzL p))
  have ha : ((a : integerSubring K) : K) ≠ 0 := by exact_mod_cast Units.ne_zero a
  obtain ⟨x, hx, hxT⟩ := FixedValueWeakApproximation.exists_global_fixed_value_weak_approximation
    Q hQ (by omega) _ ha hrep T z hz (fun p ↦ U p ∩ carrier _ p.1 L) hnb
  obtain ⟨c, hc, hcT, hcxL⟩ := IntegralPreliminaryVector.exists_unit_denominator
    (integerSubring K) L hfg hfull x T (fun p hp ↦ (hxT ⟨p, hp⟩).2)
  let v := (c : K) • x
  have hcK : (c : K) ≠ 0 := by exact_mod_cast hc
  have hv : Q v ≠ 0 := by
    change Q ((c : K) • x) ≠ 0
    rw [Q.map_smul, hx, smul_eq_mul]
    exact mul_ne_zero (mul_ne_zero hcK hcK) ha
  have hvalue : Q v = (c : K) ^ 2 * ((a : integerSubring K) : K) := by
    simp only [v, Q.map_smul, hx, smul_eq_mul, pow_two]
  have hnorm : (c : K)⁻¹ • v = x := by
    dsimp only [v]
    rw [smul_smul, inv_mul_cancel₀ hcK, one_smul]
  obtain ⟨y, hyL, hy, hyT⟩ := HasseResidualCorrection.exists_prepared_vector Q hQ hdim
    L hfg hfull v hcxL hv a c hc hvalue T hcT hdyadic hunimodular q hiso U
    (fun p ↦ by rw [hnorm]; exact (hU p).mem_nhds (hxT p).1)
  exact ⟨y, hyL, hy, fun p ↦ hUW p (hyT p)⟩

end NormEuclidean.UnitValueStrongApproximation
