import NormEuclidean.ChapterX.FractionalUnitValueApproximation
import NormEuclidean.ChapterX.QuadraticValueNormalization

/-!
# Nonzero-value approximation with arbitrary finite denominators

Normalizing by the actual target value removes the global integral-unit
restriction. The target value must be a local unit outside the finite
target set; all target vectors may be fractional. The excluded isotropic
place is infinite, and the good-lattice conditions remain explicit.
-/

noncomputable section

namespace NormEuclidean.NonzeroValueStrongApproximation

open IsDedekindDomain CompletedIntegralLattice ScalarIntegralApproximation
  LocalPrimitivePairing ProjectedComplement Filter Topology
open scoped NormEuclidean.OrthogonalTopology

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

set_option backward.isDefEq.respectTransparency false in
/-- The infinite-excluded branch for any nonzero value and arbitrary finite vector targets. -/
theorem exists_vector (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : 4 ≤ Module.finrank K V) (L : Submodule (integerSubring K) V) (hfg : L.FG)
    (hfull : Submodule.span K (L : Set V) = ⊤) (a : K) (ha : a ≠ 0)
    (hrep : ∃ x : V, Q x = a) (T : Finset (HeightOneSpectrum (integerSubring K)))
    (hunit : ∀ p : HeightOneSpectrum (integerSubring K), p ∉ T → p.valuation K a = 1)
    (hdyadic : ∀ p : HeightOneSpectrum (integerSubring K),
      (2 : integerSubring K) ∈ p.asIdeal → p ∈ T)
    (hunimodular : ∀ p : HeightOneSpectrum (integerSubring K), p ∉ T →
      SelfDual (LocalRing (integerSubring K) p) (halfPolar (form _ p Q))
        (carrier (integerSubring K) p L))
    (q : NumberField.InfinitePlace K) (hiso : ¬ (Q.baseChange q.Completion).Anisotropic)
    (z : (p : T) → Space (V := V) (integerSubring K) p.1)
    (hz : ∀ p, form (integerSubring K) p.1 Q (z p) =
      algebraMap K (LocalField (integerSubring K) p.1) a)
    (W : (p : T) → Set (Space (V := V) (integerSubring K) p.1))
    (hW : ∀ p, W p ∈ 𝓝 (z p)) :
    ∃ x : V, Q x = a ∧ (∀ p : T, inclusion (integerSubring K) p.1 x ∈ W p) ∧
      ∀ p : HeightOneSpectrum (integerSubring K), p ∉ T →
        inclusion (integerSubring K) p x ∈ carrier (integerSubring K) p L := by
  let P := a⁻¹ • Q
  have hP : P.polarBilin.Nondegenerate :=
    GenusVolumeFiniteness.polarBilin_smul_nondegenerate Q hQ a⁻¹ (inv_ne_zero ha)
  have hrepP : ∃ x : V, P x = ((1 : (integerSubring K)ˣ) : integerSubring K) := by
    obtain ⟨x, hx⟩ := hrep
    refine ⟨x, ?_⟩
    change a⁻¹ * Q x = 1
    rw [hx, inv_mul_cancel₀ ha]
  have hselfP (p : HeightOneSpectrum (integerSubring K)) (hp : p ∉ T) :
      SelfDual (LocalRing (integerSubring K) p) (halfPolar (form _ p P))
        (carrier (integerSubring K) p L) :=
    QuadraticValueNormalization.selfDual_normalize Q a ha p (hunit p hp) _ (hunimodular p hp)
  have hisoP : ¬ (P.baseChange q.Completion).Anisotropic := by
    rw [QuadraticValueNormalization.baseChange_smul]
    letI : Invertible (2 : q.Completion) := invertibleOfNonzero (by norm_num)
    exact fun h ↦ hiso ((QuadraticValueNormalization.anisotropic_smul_iff _
      ((map_ne_zero _).mpr (inv_ne_zero ha)) (Q.baseChange q.Completion)).mp h)
  have hzP (p : T) : form (integerSubring K) p.1 P (z p) =
      algebraMap K (LocalField (integerSubring K) p.1)
        (((1 : (integerSubring K)ˣ) : integerSubring K) : K) := by
    change form (integerSubring K) p.1 (a⁻¹ • Q) (z p) = _
    rw [form_rescale, QuadraticMap.smul_apply, smul_eq_mul, hz, map_inv₀,
      inv_mul_cancel₀ ((map_ne_zero _).mpr ha)]
    simp
  obtain ⟨x, hx, hxT, hout⟩ := FractionalUnitValueApproximation.exists_vector P hP hdim
    L hfg hfull 1 hrepP T hdyadic hselfP q hisoP z hzP W hW
  refine ⟨x, ?_, hxT, hout⟩
  change a⁻¹ * Q x = 1 at hx
  calc
    Q x = a * (a⁻¹ * Q x) := by rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
    _ = a := by rw [hx, mul_one]

end NormEuclidean.NonzeroValueStrongApproximation
