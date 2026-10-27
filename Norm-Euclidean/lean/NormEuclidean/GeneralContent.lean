import NormEuclidean.Content
import NormEuclidean.ScalarExtension
import NormEuclidean.HyperbolicModule
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Intrinsic coefficient and content ideals of arbitrary lattices

The coefficient submodule consists exactly of the scalars carrying the given
vector into the lattice. Finite generation makes this submodule fractional
for every nonzero vector; fullness makes it nonzero. No freeness, principal
ideal domain, quadratic form, or Dedekind domain hypothesis is needed.

Content is the inverse of this actual fractional ideal for nonzero vectors,
and is zero at the zero vector, as in Proposition 2.1 of the manuscript.
-/

namespace NormEuclidean.GeneralContent

open scoped nonZeroDivisors

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {R : Subring K} (L : Submodule R V)

/-- Scalars carrying a vector into the lattice, without auxiliary choices. -/
def coefficientSubmodule (x : V) : Submodule R K where
  carrier := {a | a • x ∈ L}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change (a + b) • x ∈ L
    rw [add_smul]
    exact L.add_mem ha hb
  smul_mem' := by
    intro r a ha
    change ((r : K) * a) • x ∈ L
    rw [mul_smul]
    exact L.smul_mem r ha

@[simp] theorem mem_coefficientSubmodule (x : V) (a : K) :
    a ∈ coefficientSubmodule L x ↔ a • x ∈ L := Iff.rfl

@[simp] theorem coefficientSubmodule_zero :
    coefficientSubmodule L (0 : V) = ⊤ := by
  ext a
  simp

/-- A separating linear functional bounds all coefficients by its image of `L`.
This proof does not need a basis of `L`, nor finite dimensionality of `V`. -/
theorem coefficient_le_map (x : V) (φ : V →ₗ[K] K) (hφ : φ x = 1) :
    coefficientSubmodule L x ≤ L.map (φ.restrictScalars R) := by
  intro a ha
  refine ⟨a • x, ha, ?_⟩
  change φ (a • x) = a
  rw [map_smul, hφ, smul_eq_mul, mul_one]

variable [IsFractionRing R K]

/-- Finite generation alone ensures the coefficient submodule of a nonzero
vector is fractional; the full-lattice hypothesis is not needed here. -/
theorem coefficient_isFractional (hL : L.FG) {x : V} (hx : x ≠ 0) :
    IsFractional R⁰ (coefficientSubmodule L x) := by
  have hxbot : x ∉ (⊥ : Submodule K V) := by simpa using hx
  obtain ⟨φ, _, hφ⟩ :=
    LinearMap.exists_extend_of_notMem (0 : (⊥ : Submodule K V) →ₗ[K] K) hxbot 1
  let J : FractionalIdeal R⁰ K :=
    ⟨L.map (φ.restrictScalars R), FractionalIdeal.isFractional_of_fg (hL.map _)⟩
  exact FractionalIdeal.isFractional_of_le (J := J) (coefficient_le_map L x φ hφ)

/-- Fullness alone ensures the coefficient submodule contains a nonzero scalar,
even at the zero vector. -/
theorem coefficientSubmodule_ne_bot
    (hfull : Submodule.span K (L : Set V) = ⊤) (x : V) :
    coefficientSubmodule L x ≠ ⊥ := by
  obtain ⟨d, hd, hdx⟩ := ScalarExtension.exists_denominator L hfull x
  intro h
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd
  have hmem : (d : K) ∈ coefficientSubmodule L x := hdx
  rw [h, Submodule.mem_bot] at hmem
  exact hdK hmem

/-- The genuine coefficient fractional ideal of a nonzero vector. -/
def coefficientIdeal (hL : L.FG) (x : V) (hx : x ≠ 0) : FractionalIdeal R⁰ K :=
  ⟨coefficientSubmodule L x, coefficient_isFractional L hL hx⟩

@[simp] theorem coe_coefficientIdeal (hL : L.FG) (x : V) (hx : x ≠ 0) :
    (coefficientIdeal L hL x hx : Submodule R K) = coefficientSubmodule L x := rfl

@[simp] theorem mem_coefficientIdeal (hL : L.FG) (x : V) (hx : x ≠ 0) (a : K) :
    a ∈ coefficientIdeal L hL x hx ↔ a • x ∈ L := Iff.rfl

theorem coefficientIdeal_ne_zero (hL : L.FG)
    (hfull : Submodule.span K (L : Set V) = ⊤) (x : V) (hx : x ≠ 0) :
    coefficientIdeal L hL x hx ≠ 0 := by
  intro h
  apply coefficientSubmodule_ne_bot L hfull x
  simpa only [coe_coefficientIdeal, FractionalIdeal.coe_zero] using
    congrArg FractionalIdeal.coeToSubmodule h

/-- Total content: inverse coefficient ideal off zero, and zero at zero. -/
noncomputable def contentIdeal (hL : L.FG) (x : V) : FractionalIdeal R⁰ K := by
  classical
  exact if hx : x = 0 then 0 else (coefficientIdeal L hL x hx)⁻¹

@[simp] theorem contentIdeal_zero (hL : L.FG) : contentIdeal L hL (0 : V) = 0 := by
  simp [contentIdeal]

theorem contentIdeal_of_ne_zero (hL : L.FG) (x : V) (hx : x ≠ 0) :
    contentIdeal L hL x = (coefficientIdeal L hL x hx)⁻¹ := by
  simp [contentIdeal, hx]

/-- Content of a nonzero vector in a full lattice is nonzero. This only
uses that the coefficient ideal is nonzero and fractional, not invertibility
of all fractional ideals. -/
theorem contentIdeal_ne_zero (hL : L.FG)
    (hfull : Submodule.span K (L : Set V) = ⊤) (x : V) (hx : x ≠ 0) :
    contentIdeal L hL x ≠ 0 := by
  rw [contentIdeal_of_ne_zero L hL x hx]
  intro hzero
  have hpos := FractionalIdeal.bot_lt_mul_inv (coefficientIdeal_ne_zero L hL hfull x hx)
  rw [hzero, mul_zero] at hpos
  exact (lt_irrefl (0 : FractionalIdeal R⁰ K)) hpos

@[simp] theorem contentIdeal_eq_zero_iff (hL : L.FG)
    (hfull : Submodule.span K (L : Set V) = ⊤) (x : V) :
    contentIdeal L hL x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    exact contentIdeal_ne_zero L hL hfull x hx h
  · rintro rfl
    exact contentIdeal_zero L hL

omit [IsFractionRing R K] in
/-- The arbitrary-vector coefficient construction agrees definitionally in
membership with the existing hyperbolic-coordinate construction. -/
theorem coefficientSubmodule_hyperbolic (z : Hyperbolic K V) :
    coefficientSubmodule (Hyperbolic.submodule L) z =
      Hyperbolic.coefficientSubmodule L z := by
  ext a
  rfl

omit [IsFractionRing R K] in
/-- Adding the standard hyperbolic plane preserves finite generation. -/
theorem hyperbolicSubmodule_fg (hL : L.FG) : (Hyperbolic.submodule L).FG := by
  letI : Module.Finite R L := Module.Finite.iff_fg.mpr hL
  letI : Module.Finite R (Hyperbolic.submodule L) :=
    Module.Finite.equiv (Hyperbolic.moduleEquivProduct L).symm
  exact Module.Finite.iff_fg.mp inferInstance

/-- The old hyperbolic coefficient ideal and the intrinsic construction bundle
exactly the same submodule; their fractionality proofs need not agree. -/
theorem coefficientIdeal_hyperbolic (hL : L.FG) (z : Hyperbolic K V) (hz : z ≠ 0)
    (hfrac : IsFractional R⁰ (Hyperbolic.coefficientSubmodule L z)) :
    coefficientIdeal (Hyperbolic.submodule L) (hyperbolicSubmodule_fg L hL) z hz =
      Hyperbolic.coefficientIdeal L z hfrac := by
  apply FractionalIdeal.coeToSubmodule_injective
  exact coefficientSubmodule_hyperbolic L z

/-- Total intrinsic content recovers the previous hyperbolic content whenever
the vector is nonzero. -/
theorem contentIdeal_hyperbolic (hL : L.FG) (z : Hyperbolic K V) (hz : z ≠ 0)
    (hfrac : IsFractional R⁰ (Hyperbolic.coefficientSubmodule L z)) :
    contentIdeal (Hyperbolic.submodule L) (hyperbolicSubmodule_fg L hL) z =
      Hyperbolic.contentIdeal L z hfrac := by
  rw [contentIdeal_of_ne_zero _ _ _ hz, coefficientIdeal_hyperbolic L hL z hz hfrac]
  rfl

end NormEuclidean.GeneralContent
