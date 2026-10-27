import NormEuclidean.Lattice
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic

/-!
# The genuine coefficient and content ideals of terminalized vectors

The coefficient submodule is defined by scalar membership in the lattice.
Whenever it is fractional, `coefficientIdeal` bundles that exact submodule,
and `contentIdeal` is its inverse, as in Proposition 2.1 of the manuscript.
There is no default value or assumed content law. Terminalization proves
fractionality, identifies the coefficient ideal, and computes its inverse.

The full nonzero-vector construction for every finitely generated full
lattice, and Proposition 2.1(ii), are separate development tasks.
-/

namespace NormEuclidean.Hyperbolic

open scoped nonZeroDivisors

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {R : Subring K} {Q : QuadraticForm K V} (L : Submodule R V)

/-- Scalars that carry `z` into the lattice, as an actual submodule. -/
def coefficientSubmodule (z : Hyperbolic K V) : Submodule R K where
  carrier := coefficientSet L z
  zero_mem' := by simp [coefficientSet, Mem]
  add_mem' := by
    intro a b ha hb
    change Mem L ((a + b) • z)
    rw [add_smul]
    exact ⟨L.add_mem ha.1 hb.1, R.add_mem ha.2.1 hb.2.1,
      R.add_mem ha.2.2 hb.2.2⟩
  smul_mem' := by
    intro r a ha
    change Mem L (((r : K) * a) • z)
    rw [mul_smul]
    exact ⟨L.smul_mem r ha.1, R.mul_mem r.property ha.2.1,
      R.mul_mem r.property ha.2.2⟩

@[simp] theorem mem_coefficientSubmodule (z : Hyperbolic K V) (a : K) :
    a ∈ coefficientSubmodule L z ↔ Mem L (a • z) := Iff.rfl

theorem coefficientSubmodule_aut (g : Aut (Q := Q) L) (z : Hyperbolic K V) :
    coefficientSubmodule L (g z) = coefficientSubmodule L z := by
  apply SetLike.coe_injective
  exact coefficientSet_aut L g z

theorem coefficientSubmodule_smul_e {c : K} (hc : c ≠ 0) :
    coefficientSubmodule L (c • (e : Hyperbolic K V)) = Submodule.span R {c⁻¹} := by
  ext a
  change a ∈ coefficientSet L (c • (e : Hyperbolic K V)) ↔ _
  rw [coefficientSet_smul_e]
  change a * c ∈ R ↔ _
  rw [Submodule.mem_span_singleton]
  constructor
  · intro ha
    refine ⟨⟨a * c, ha⟩, ?_⟩
    change (a * c) * c⁻¹ = a
    rw [mul_assoc, mul_inv_cancel₀ hc, mul_one]
  · rintro ⟨r, hr⟩
    change (r : K) * c⁻¹ = a at hr
    rw [← hr, mul_assoc, inv_mul_cancel₀ hc, mul_one]
    exact r.property

variable [IsFractionRing R K]

/-- The coefficient ideal, available when the defining submodule is fractional. -/
def coefficientIdeal (z : Hyperbolic K V)
    (hz : IsFractional R⁰ (coefficientSubmodule L z)) : FractionalIdeal R⁰ K :=
  ⟨coefficientSubmodule L z, hz⟩

/-- Content is the inverse of the genuine coefficient ideal. -/
noncomputable def contentIdeal (z : Hyperbolic K V)
    (hz : IsFractional R⁰ (coefficientSubmodule L z)) : FractionalIdeal R⁰ K :=
  (coefficientIdeal L z hz)⁻¹

/-- Primitivity in content-ideal language. The nonzero condition is the
manuscript's convention that the zero vector has content zero. -/
def ContentPrimitive (z : Hyperbolic K V) : Prop :=
  z ≠ 0 ∧ ∃ hz : IsFractional R⁰ (coefficientSubmodule L z), contentIdeal L z hz = 1

theorem coefficient_isFractional_of_terminal (g : Aut (Q := Q) L)
    {z : Hyperbolic K V} {c : K} (hc : c ≠ 0) (hgz : g z = c • e) :
    IsFractional R⁰ (coefficientSubmodule L z) := by
  rw [← coefficientSubmodule_aut L g z, hgz, coefficientSubmodule_smul_e L hc]
  exact FractionalIdeal.isFractional_span_singleton _

theorem coefficientIdeal_eq_of_terminal (g : Aut (Q := Q) L)
    {z : Hyperbolic K V} {c : K} (hc : c ≠ 0) (hgz : g z = c • e)
    (hz : IsFractional R⁰ (coefficientSubmodule L z)) :
    coefficientIdeal L z hz = FractionalIdeal.spanSingleton R⁰ c⁻¹ := by
  apply FractionalIdeal.coeToSubmodule_injective
  change coefficientSubmodule L z = _
  rw [← coefficientSubmodule_aut L g z, hgz, coefficientSubmodule_smul_e L hc]
  exact (FractionalIdeal.coe_spanSingleton _ _).symm

theorem coefficientIdeal_ne_zero_of_terminal (g : Aut (Q := Q) L)
    {z : Hyperbolic K V} {c : K} (hc : c ≠ 0) (hgz : g z = c • e)
    (hz : IsFractional R⁰ (coefficientSubmodule L z)) :
    coefficientIdeal L z hz ≠ 0 := by
  rw [coefficientIdeal_eq_of_terminal L g hc hgz hz,
    FractionalIdeal.spanSingleton_ne_zero_iff]
  exact inv_ne_zero hc

/-- The content conclusion in Lemma 2.4, derived from terminalization.
No free basis, principal-ideal-domain assumption, or content axiom is used. -/
theorem contentIdeal_eq_of_terminal (g : Aut (Q := Q) L)
    {z : Hyperbolic K V} {c : K} (hc : c ≠ 0) (hgz : g z = c • e)
    (hz : IsFractional R⁰ (coefficientSubmodule L z)) :
    contentIdeal L z hz = FractionalIdeal.spanSingleton R⁰ c := by
  unfold contentIdeal
  rw [coefficientIdeal_eq_of_terminal L g hc hgz hz, FractionalIdeal.spanSingleton_inv,
    inv_inv]

theorem contentIdeal_eq_coe_span_of_terminal (g : Aut (Q := Q) L)
    {z : Hyperbolic K V} {c : K} (hc : c ≠ 0) (hcR : c ∈ R) (hgz : g z = c • e)
    (hz : IsFractional R⁰ (coefficientSubmodule L z)) :
    contentIdeal L z hz =
      (Ideal.span ({(⟨c, hcR⟩ : R)} : Set R) : FractionalIdeal R⁰ K) := by
  rw [contentIdeal_eq_of_terminal L g hc hgz hz,
    FractionalIdeal.coeIdeal_span_singleton]
  rfl

omit [IsFractionRing R K] in
/-- For a subring of a field, the unit fractional ideal has exactly the
elements of that subring. -/
@[simp] theorem mem_one_fractionalIdeal (a : K) :
    a ∈ (1 : FractionalIdeal R⁰ K) ↔ a ∈ R := by
  rw [FractionalIdeal.mem_one_iff]
  constructor
  · rintro ⟨r, hr⟩
    exact hr ▸ r.property
  · intro ha
    exact ⟨⟨a, ha⟩, rfl⟩

/-- Over a Dedekind domain, the coefficient-set formulation of primitivity
is equivalent to the manuscript's content-ideal formulation. -/
theorem contentIdeal_eq_one_iff [IsDedekindDomain R]
    (z : Hyperbolic K V) (hz : IsFractional R⁰ (coefficientSubmodule L z)) :
    contentIdeal L z hz = 1 ↔ coefficientSet L z = (R : Set K) := by
  change (coefficientIdeal L z hz)⁻¹ = 1 ↔ _
  rw [inv_eq_one]
  constructor
  · intro h
    ext a
    change a ∈ coefficientIdeal L z hz ↔ a ∈ R
    rw [h, mem_one_fractionalIdeal]
  · intro h
    ext a
    change a ∈ coefficientSet L z ↔ a ∈ (1 : FractionalIdeal R⁰ K)
    rw [h, mem_one_fractionalIdeal]
    rfl

end NormEuclidean.Hyperbolic
