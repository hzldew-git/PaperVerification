import NormEuclidean.ChapterX.UniformIdealPair
import NormEuclidean.ChapterX.IsotropicRayIdeals
import NormEuclidean.ChapterX.ClassFinitenessInduction

/-!
# Actual common represented values in isotropic regular spaces

Finite ideal classes normalize the coefficient ideal of a fixed isotropic ray.
The proved volume/dual bounds control its product with the actual pairing ideal.
A common integer then constructs an integral isotropic pair and the same nonzero
quadratic value in every lattice of the bounded-volume family. No maximal-lattice
classification, splitting or common-value law is assumed.
-/

noncomputable section

namespace NormEuclidean.IsotropicValues

open Module IsotropicRayIdeals ClassFinitenessInduction
open scoped nonZeroDivisors

variable {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]

/-- A fixed isotropic vector and a pairing beta squared produce the explicit
common value `4 beta^4`, without dividing by two in an integer ring. -/
theorem value_of_isotropic_pair (Q : QuadraticForm K V) (e u : V) (β : K)
    (he : Q e = 0) (hpair : halfPolar Q e u = β ^ 2) :
    Q (e + (2 * β ^ 2) • u - Q u • e) = 4 * β ^ 4 := by
  have hself : halfPolar Q e e = 0 := by simpa only [halfPolar_self] using he
  have hcomm : halfPolar Q u e = β ^ 2 := (halfPolar_comm Q u e).trans hpair
  rw [← halfPolar_self]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, hself, hpair, hcomm, halfPolar_self]
  ring

variable [FiniteDimensional K V]

/-- One actual nonzero integral beta gives the same represented value in
every integral-scale lattice above a fixed nonzero volume ideal on an isotropic space. -/
theorem exists_uniform_value (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (e : V) (he : e ≠ 0) (hiso : Q e = 0)
    (c : FractionalIdeal (integerSubring K)⁰ K) (hc : c ≠ 0) :
    ∃ β : integerSubring K, β ≠ 0 ∧
      ∀ L : Lattice (integerSubring K) Q, L.scaleIdeal ≤ 1 → c ≤ L.volumeIdeal →
        ∃ x ∈ L.carrier, Q x = 4 * (β : K) ^ 4 := by
  obtain ⟨β, hβ, hcommon⟩ := UniformIdealPair.exists_common_scalar c hc
  refine ⟨β, hβ, ?_⟩
  intro L hs hvol
  let I := GeneralContent.coefficientIdeal L.carrier L.finite e he
  let J := pairingIdeal (halfPolar Q) L.carrier L.finite e
  have hI : I ≠ 0 := GeneralContent.coefficientIdeal_ne_zero L.carrier L.finite L.full e he
  have hJ : J ≠ 0 := pairingIdeal_ne_zero (halfPolar Q)
    (SpinorBridge.quadraticSpace Q hQ).nondegenerate L.carrier L.finite L.full e he
  have hbounds := product_bounds Q hQ L hs e he
  obtain ⟨t, ht, htβ, hβt⟩ := hcommon I J hI hJ (hvol.trans hbounds.1) hbounds.2
  have hv : (t * (β : K)) • e ∈ L.carrier := htβ
  obtain ⟨u, hu, hQu⟩ := (mem_pairingIdeal _ _ _ _ _).mp hβt
  let v := (t * (β : K)) • e
  have hv0 : Q v = 0 := by simp only [v, Q.map_smul, hiso, smul_zero]
  have hvu : halfPolar Q v u = (β : K) ^ 2 := by
    rw [LinearMap.BilinForm.smul_left, hQu]
    field_simp [ht]
  let x := v + (2 * (β : K) ^ 2) • u - Q u • v
  have hx : x ∈ L.carrier := by
    apply L.carrier.sub_mem (L.carrier.add_mem hv ?_) ?_
    · exact L.carrier.smul_mem (2 * β ^ 2) hu
    · exact L.carrier.smul_mem ⟨Q u, L.integral u hu⟩ hv
  exact ⟨x, hx, value_of_isotropic_pair Q v u β hv0 hvu⟩

/-- The isotropic branch of 103:3 has an actual singleton nonzero value set. -/
theorem bounded_value_coverage (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (e : V) (he : e ≠ 0) (hiso : Q e = 0)
    (c : FractionalIdeal (integerSubring K)⁰ K) (hc : c ≠ 0) :
    BoundedValueCoverage Q c := by
  obtain ⟨β, hβ, hvalue⟩ := exists_uniform_value Q hQ e he hiso c hc
  have hβK : (β : K) ≠ 0 := by exact_mod_cast hβ
  refine ⟨{4 * (β : K) ^ 4}, Set.finite_singleton _, ?_, ?_⟩
  · intro hzero
    exact (mul_ne_zero (by norm_num : (4 : K) ≠ 0) (pow_ne_zero 4 hβK))
      (Set.mem_singleton_iff.mp hzero).symm
  · intro L hs hvol
    obtain ⟨x, hx, hQx⟩ := hvalue L hs hvol
    exact ⟨x, hx, Set.mem_singleton_iff.mpr hQx⟩

end NormEuclidean.IsotropicValues
