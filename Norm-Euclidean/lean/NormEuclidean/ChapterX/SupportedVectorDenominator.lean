import NormEuclidean.ChapterX.PrimePowerDenominator
import NormEuclidean.ChapterX.ScalarMultipleModule

/-!
# Finite-place vector denominators with prescribed support

Arbitrary finite completed vector targets fit in a finite full global
module whose completed carriers agree with the base module away from
the targets. No integral coordinates or global integral basis are assumed.
-/

noncomputable section

namespace NormEuclidean.SupportedVectorDenominator

open IsDedekindDomain CompletedIntegralLattice ScalarIntegralApproximation
  PrimePowerDenominator ScalarMultipleModule Filter Topology
open scoped NormEuclidean.OrthogonalTopology

variable {K V : Type*} [Field K] [NumberField K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

set_option backward.isDefEq.respectTransparency false in
/-- A power of a prime-supported scalar moves any completed vector into a full carrier. -/
theorem exists_power (L : Submodule (integerSubring K) V)
    (hfull : Submodule.span K (L : Set V) = ⊤)
    (p : HeightOneSpectrum (integerSubring K)) (d : integerSubring K) (hd : d ∈ p.asIdeal)
    (x : Space (V := V) (integerSubring K) p) :
    ∃ n : ℕ, algebraMap K (LocalField (integerSubring K) p) ((d : K) ^ n) • x ∈
      carrier (integerSubring K) p L := by
  have hlt : Valued.v (algebraMap K (LocalField (integerSubring K) p) (d : K)) < 1 := by
    rw [valuation_algebraMap]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) p d).mpr hd
  have ht : Tendsto (fun n : ℕ ↦
      algebraMap K (LocalField (integerSubring K) p) (d : K) ^ n • x) atTop (𝓝 0) := by
    simpa only [zero_smul] using (Valued.tendsto_zero_pow_of_v_lt_one hlt).smul_const x
  have hopen := OrthogonalTopology.isOpen_of_full _ (OrthogonalTopology.isOpen_localRing _ _)
    (carrier (integerSubring K) p L) (carrier_full _ _ _ hfull)
  obtain ⟨n, hn⟩ := (ht.eventually_mem (hopen.mem_nhds (Submodule.zero_mem _))).exists
  refine ⟨n, ?_⟩
  rw [map_pow]
  exact hn

/-- One nonzero global integer clears every specified vector and is a unit elsewhere. -/
theorem exists_denominator (L : Submodule (integerSubring K) V)
    (hfull : Submodule.span K (L : Set V) = ⊤)
    (T : Finset (HeightOneSpectrum (integerSubring K)))
    (x : (p : T) → Space (V := V) (integerSubring K) p.1) :
    ∃ d : integerSubring K, d ≠ 0 ∧
      (∀ p : T, algebraMap K (LocalField (integerSubring K) p.1) (d : K) • x p ∈
        carrier (integerSubring K) p.1 L) ∧
      ∀ p : HeightOneSpectrum (integerSubring K), p ∉ T → d ∉ p.asIdeal := by
  classical
  choose a ha0 hap hao using fun p : T ↦ exists_single_prime_scalar p.1
  choose n hn using fun p : T ↦ exists_power L hfull p.1 (a p) (hap p) (x p)
  let f : T → integerSubring K := fun p ↦ a p ^ n p
  let d : integerSubring K := ∏ p : T, f p
  have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun p _ ↦ pow_ne_zero (n p) (ha0 p))
  refine ⟨d, hd0, ?_, ?_⟩
  · intro p
    obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem f (Finset.mem_univ p)
    have heq : d = a p ^ n p * b := hb
    rw [heq, Subring.coe_mul, Subring.coe_pow, map_mul, mul_smul, smul_comm]
    exact (carrier (integerSubring K) p.1 L).smul_mem
      (integerMap (integerSubring K) p.1 b) (hn p)
  · intro p hp
    have hf : ∀ v : T, f v ∉ p.asIdeal := by
      intro v
      exact p.asIdeal.primeCompl.pow_mem (hao v p (fun heq ↦ hp (heq ▸ v.2))) (n v)
    exact p.asIdeal.primeCompl.prod_mem (fun v _ ↦ hf v)

set_option backward.isDefEq.respectTransparency false in
/-- Fractional targets fit in an auxiliary module with literally unchanged off-target carriers. -/
theorem exists_module (L : Submodule (integerSubring K) V) (hfg : L.FG)
    (hfull : Submodule.span K (L : Set V) = ⊤)
    (T : Finset (HeightOneSpectrum (integerSubring K)))
    (x : (p : T) → Space (V := V) (integerSubring K) p.1) :
    ∃ M : Submodule (integerSubring K) V, M.FG ∧ Submodule.span K (M : Set V) = ⊤ ∧
      (∀ p : T, x p ∈ carrier (integerSubring K) p.1 M) ∧
      ∀ p : HeightOneSpectrum (integerSubring K), p ∉ T →
        carrier (integerSubring K) p M = carrier (integerSubring K) p L := by
  obtain ⟨d, hd, hx, hout⟩ := exists_denominator L hfull T x
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd
  let M := scale (integerSubring K) (d : K)⁻¹ L
  refine ⟨M, scale_fg _ _ L hfg, scale_full _ _ (inv_ne_zero hdK) L hfull, ?_, ?_⟩
  · intro p
    exact (mem_carrier_divide_iff _ p.1 (d : K) hdK L (x p)).mpr (hx p)
  · intro p hp
    have hdval : p.valuation K (d : K) = 1 := by
      exact (HeightOneSpectrum.valuation_eq_one_iff_notMem p).mpr (hout p hp)
    apply carrier_scale_eq _ p (d : K)⁻¹ (inv_ne_zero hdK)
    · change Valued.v (algebraMap K (LocalField (integerSubring K) p) (d : K)⁻¹) ≤ 1
      rw [map_inv₀, map_inv₀, valuation_algebraMap, hdval, inv_one]
    · change Valued.v (algebraMap K (LocalField (integerSubring K) p) ((d : K)⁻¹)⁻¹) ≤ 1
      rw [inv_inv, valuation_algebraMap, hdval]

end NormEuclidean.SupportedVectorDenominator
