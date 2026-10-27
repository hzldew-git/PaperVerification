import Mathlib.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.RingTheory.Int.Basic

/-!
# The rational p-primary additive character

The rational circle is decomposed into its actual primary components.
Projection of the rational class onto the p-component is additive, and
its kernel consists exactly of fractions with denominator prime to p.
This constructs the arithmetic input for the continuous p-adic character.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.RationalPrimaryCharacter

open IsDedekindDomain
open scoped Classical

/-- The actual rational circle, with no character premise. -/
abbrev Circle := AddCircle (1 : ℚ)

/-- The rational class has its literal reduced denominator as additive order. -/
theorem order_class (q : ℚ) : addOrderOf (q : Circle) = q.den := by
  simpa only [Rat.cast_id, mul_one] using
    (AddCircle.addOrderOf_coe_rat (p := (1 : ℚ)) (q := q))

/-- Every actual rational-circle element is torsion. -/
theorem circle_torsion : Module.IsTorsion ℤ Circle := by
  apply AddMonoid.isTorsion_iff_isTorsion_int.mp
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H q => exact addOrderOf_pos_iff.mp (by rw [order_class]; exact q.den_pos)

/-- The actual primary submodules of the rational circle. -/
def Component (P : HeightOneSpectrum ℤ) : Submodule ℤ Circle :=
  Ideal.primaryComponent Circle P.asIdeal

/-- The primary components give an internal direct sum, by the proved torsion theorem. -/
theorem internal : DirectSum.IsInternal Component :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (Ideal.iSupIndep_primaryComponent ℤ Circle)
    (Ideal.iSup_primaryComponent_eq_top circle_torsion)

/-- The canonical recomposition equivalence; its inverse is the actual primary decomposition. -/
def decomposition : DirectSum (HeightOneSpectrum ℤ) (fun P ↦ Component P) ≃ₗ[ℤ] Circle :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap Component) internal

/-- Projection onto one actual primary component, followed by its original inclusion. -/
def primary (P : HeightOneSpectrum ℤ) : Circle →ₗ[ℤ] Circle :=
  (Component P).subtype ∘ₗ DirectSum.component ℤ _ _ P ∘ₗ decomposition.symm.toLinearMap

/-- The primary projection lands in the specified actual primary submodule. -/
theorem primary_mem (P : HeightOneSpectrum ℤ) (x : Circle) : primary P x ∈ Component P :=
  (decomposition.symm x P).property

/-- Projection fixes every element already belonging to that primary component. -/
theorem primary_fix (P : HeightOneSpectrum ℤ) (x : Circle) (hx : x ∈ Component P) :
    primary P x = x := by
  change ((decomposition.symm x P : Component P) : Circle) = x
  exact congrArg Subtype.val (internal.ofBijective_coeLinearMap_of_mem hx)

variable (p : ℕ) [hp : Fact p.Prime]

/-- The actual integer prime ideal associated to the original prime number. -/
def prime : HeightOneSpectrum ℤ :=
  ⟨Ideal.span {(p : ℤ)}, Ideal.isPrime_span_singleton_of_prime
    (Nat.prime_iff_prime_int.mp hp.out), by simpa using hp.out.ne_zero⟩

/-- Membership in the actual p-primary component is annihilation by a power of p. -/
theorem component_iff (x : Circle) : x ∈ Component (prime p) ↔ ∃ n : ℕ, p ^ n • x = 0 := by
  simp only [Component, Ideal.primaryComponent_mem, prime,
    Ideal.span_singleton_pow, Submodule.torsionBySet_ideal_span_singleton_eq,
    Submodule.mem_torsionBy_iff, ← Int.natCast_pow, natCast_zsmul]

/-- The original rational p-primary class, as an actual additive homomorphism. -/
def character : ℚ →+ Circle :=
  (primary (prime p)).toAddMonoidHom.comp (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)))

/-- The character is the primary projection of the original rational class. -/
theorem character_apply (q : ℚ) : character p q = primary (prime p) (q : Circle) := rfl

/-- A denominator prime to p kills no nonzero p-primary component. -/
theorem character_zero_of_not_dvd (q : ℚ) (hq : ¬ p ∣ q.den) : character p q = 0 := by
  obtain ⟨n, hn⟩ := (component_iff p _).mp (primary_mem (prime p) (q : Circle))
  have horder : addOrderOf (character p q) ∣ p ^ n :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr hn
  have hden : addOrderOf (character p q) ∣ q.den := by
    apply addOrderOf_dvd_iff_nsmul_eq_zero.mpr
    change q.den • primary (prime p) (q : Circle) = 0
    rw [← map_nsmul, ← order_class, addOrderOf_nsmul_eq_zero, map_zero]
  have hc : q.den.Coprime (p ^ n) :=
    ((hp.out.coprime_iff_not_dvd.mpr hq).symm).pow_right n
  have hone : addOrderOf (character p q) ∣ 1 := by
    simpa only [hc.gcd_eq_one] using Nat.dvd_gcd hden horder
  exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp hone)

/-- Vanishing forces the literal reduced denominator to be prime to p. -/
theorem not_dvd_of_character_zero (q : ℚ) (hq : character p q = 0) : ¬ p ∣ q.den := by
  intro hdiv
  let z : Circle := (q.den / p) • (q : Circle)
  have hz : z ∈ Component (prime p) := by
    apply (component_iff p z).mpr
    refine ⟨1, ?_⟩
    change p ^ 1 • ((q.den / p) • (q : Circle)) = 0
    rw [pow_one, ← mul_nsmul, Nat.div_mul_cancel hdiv,
      ← order_class, addOrderOf_nsmul_eq_zero]
  have hz0 : z = 0 := by
    rw [← primary_fix (prime p) z hz]
    change primary (prime p) ((q.den / p) • (q : Circle)) = 0
    rw [map_nsmul]
    change (q.den / p) • character p q = 0
    rw [hq, smul_zero]
  have hden : q.den ∣ q.den / p := by
    have horder : addOrderOf (q : Circle) ∣ q.den / p :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz0
    simpa only [order_class] using horder
  have hpos : 0 < q.den / p := Nat.div_pos (Nat.le_of_dvd q.den_pos hdiv) hp.out.pos
  exact (Nat.not_le_of_gt (Nat.div_lt_self q.den_pos hp.out.one_lt))
    (Nat.le_of_dvd hpos hden)

/-- The exact rational-character kernel, proved without an assumed conductor statement. -/
theorem character_eq_zero_iff (q : ℚ) : character p q = 0 ↔ ¬ p ∣ q.den :=
  ⟨not_dvd_of_character_zero p q, character_zero_of_not_dvd p q⟩

end NormEuclidean.RationalPrimaryCharacter
