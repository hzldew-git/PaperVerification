import NormEuclidean.NumberFieldNorm
import NormEuclidean.Descent
import NormEuclidean.Content
import NormEuclidean.Cancellation

/-!
# Concrete number-field endpoints

These endpoints use the actual absolute field norm and finite full integral
lattices over the ring of integers. The underlying descent and content
proofs do not require a free lattice.
-/

namespace NormEuclidean

open scoped NumberField nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

/-- The proved arithmetic interface for the absolute norm of a number field. -/
noncomputable def numberFieldNorm : IntegralNorm (integerSubring K) where
  norm := fieldAbsNorm K
  measure := integralNormMeasure K
  map_mul := fieldAbsNorm_mul K
  map_neg := fieldAbsNorm_neg K
  pos := fun _ ha => fieldAbsNorm_pos K ha
  measure_spec := integralNormMeasure_spec K

variable {K} {V : Type*} [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

/-- The exact approximation inequality from Definition 1.1. Anisotropy is
kept as a separate hypothesis in the theorem, as is common for quadratic forms. -/
def HasNumberFieldApproximation (L : Submodule (integerSubring K) V) : Prop :=
  ∀ x : V, ∃ u ∈ L, |Algebra.norm ℚ (Q (x - u))| < 1

theorem numberFieldApproximation_iff (L : Submodule (integerSubring K) V) :
    HasNumberFieldApproximation Q L ↔ IsNormEuclidean (numberFieldNorm K) Q L :=
  Iff.rfl

/-- Lemma 2.4 for an actual number field: the orbit normal form and the
principal content conclusion, with the coefficient ideal explicitly bundled
from its defining scalar-membership submodule. -/
theorem numberField_norm_descent (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    {z : Hyperbolic K V} (hz : Hyperbolic.Mem L.carrier z) (hz0 : z ≠ 0)
    (hiso : Hyperbolic.q Q z = 0) :
    ∃ g : Hyperbolic.Aut (Q := Q) L.carrier, ∃ c : K,
      c ∈ integerSubring K ∧ c ≠ 0 ∧ g z = c • (Hyperbolic.e : Hyperbolic K V) ∧
      ∃ hfrac : IsFractional (integerSubring K)⁰
          (Hyperbolic.coefficientSubmodule L.carrier z),
        Hyperbolic.coefficientIdeal L.carrier z hfrac ≠ 0 ∧
        Hyperbolic.contentIdeal L.carrier z hfrac =
          FractionalIdeal.spanSingleton (integerSubring K)⁰ c := by
  obtain ⟨g, c, hc, hc0, hg⟩ := Hyperbolic.norm_descent Q L.carrier
    (numberFieldNorm K) L.integral hA hE hz hz0 hiso
  have hfrac := Hyperbolic.coefficient_isFractional_of_terminal L.carrier g hc0 hg
  exact ⟨g, c, hc, hc0, hg, hfrac,
    Hyperbolic.coefficientIdeal_ne_zero_of_terminal L.carrier g hc0 hg hfrac,
    Hyperbolic.contentIdeal_eq_of_terminal L.carrier g hc0 hg hfrac⟩

/-- The primitive-orbit conclusion of Lemma 2.4. Primitivity is expressed
intrinsically as coefficient ideal `R`, equivalent to content `R` for the
nonzero coefficient ideal constructed by the descent theorem. -/
theorem numberField_primitive_orbit (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    {z : Hyperbolic K V} (hz : Hyperbolic.Mem L.carrier z) (hz0 : z ≠ 0)
    (hiso : Hyperbolic.q Q z = 0)
    (hprimitive : Hyperbolic.coefficientSet L.carrier z = (integerSubring K : Set K)) :
    ∃ g : Hyperbolic.Aut (Q := Q) L.carrier, g z = (Hyperbolic.e : Hyperbolic K V) :=
  Hyperbolic.primitive_orbit_transitivity Q L.carrier (numberFieldNorm K)
    L.integral hA hE hz hz0 hiso hprimitive

/-- The same primitive-orbit endpoint, now with content equal to the unit
fractional ideal exactly as in the manuscript. -/
theorem numberField_primitive_orbit_of_content (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    {z : Hyperbolic K V} (hz : Hyperbolic.Mem L.carrier z) (hz0 : z ≠ 0)
    (hiso : Hyperbolic.q Q z = 0)
    (hfrac : IsFractional (integerSubring K)⁰
      (Hyperbolic.coefficientSubmodule L.carrier z))
    (hprimitive : Hyperbolic.contentIdeal L.carrier z hfrac = 1) :
    ∃ g : Hyperbolic.Aut (Q := Q) L.carrier, g z = (Hyperbolic.e : Hyperbolic K V) :=
  numberField_primitive_orbit Q L hA hE hz hz0 hiso
    ((Hyperbolic.contentIdeal_eq_one_iff L.carrier z hfrac).mp hprimitive)

/-- The full orbit-set equality in the "Moreover" clause of Lemma 2.4,
with primitivity expressed by the genuine content ideal. -/
theorem numberField_primitive_isotropic_eq_orbit (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier) :
    {z : Hyperbolic K V | Hyperbolic.Mem L.carrier z ∧ Hyperbolic.q Q z = 0 ∧
      Hyperbolic.ContentPrimitive L.carrier z} =
    Set.range (fun g : Hyperbolic.Aut (Q := Q) L.carrier =>
      g (Hyperbolic.e : Hyperbolic K V)) := by
  ext z
  constructor
  · rintro ⟨hz, hiso, hz0, hfrac, hprimitive⟩
    obtain ⟨g, hg⟩ :=
      numberField_primitive_orbit_of_content Q L hA hE hz hz0 hiso hfrac hprimitive
    refine ⟨Hyperbolic.Aut.symm L.carrier g, ?_⟩
    change Hyperbolic.Aut.symm L.carrier g (Hyperbolic.e : Hyperbolic K V) = z
    rw [← hg, Hyperbolic.Aut.symm_apply_apply]
  · rintro ⟨g, rfl⟩
    have he0 : (Hyperbolic.e : Hyperbolic K V) ≠ 0 := by
      intro he
      have hone : (1 : K) = 0 :=
        congrArg (fun w : Hyperbolic K V => w.2.1) he
      exact one_ne_zero hone
    have hg0 : g (Hyperbolic.e : Hyperbolic K V) ≠ 0 := by
      intro hg
      apply he0
      apply g.injective
      simpa using hg
    have hterminal : Hyperbolic.Aut.symm L.carrier g
        (g (Hyperbolic.e : Hyperbolic K V)) = (1 : K) • Hyperbolic.e := by
      simp
    have hfrac := Hyperbolic.coefficient_isFractional_of_terminal L.carrier
      (Hyperbolic.Aut.symm L.carrier g) one_ne_zero hterminal
    refine ⟨(g.mem_iff _).mpr (Hyperbolic.mem_e L.carrier),
      (g.q_eq _).trans Hyperbolic.q_e, hg0, hfrac, ?_⟩
    rw [Hyperbolic.contentIdeal_eq_of_terminal L.carrier
      (Hyperbolic.Aut.symm L.carrier g) one_ne_zero hterminal hfrac,
      FractionalIdeal.spanSingleton_one]

variable {W : Type*} [AddCommGroup W] [Module K W] (Q' : QuadraticForm K W)

/-- Lemma 3.1 (reference manuscript) with an ambient stabilized isometry as input. The
module-level scalar-extension adapter supplies this input from a lattice
isometry in the manuscript's original convention. -/
theorem numberField_hyperbolic_cancellation_ambient (L : Lattice (integerSubring K) Q)
    (L' : Lattice (integerSubring K) Q')
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (φ : Hyperbolic.Isometry Q' Q L'.carrier L.carrier) :
    Nonempty (LatticeIsometry Q' Q L'.carrier L.carrier) :=
  Hyperbolic.norm_euclidean_cancellation (numberFieldNorm K) L.integral hA hE φ

/-- The cancellation output is an integral module isometry, without any
choice of basis or freeness assumption. -/
theorem numberField_hyperbolic_cancellation_ambient_module (L : Lattice (integerSubring K) Q)
    (L' : Lattice (integerSubring K) Q')
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (φ : Hyperbolic.Isometry Q' Q L'.carrier L.carrier) :
    ∃ ψ : L'.carrier ≃ₗ[integerSubring K] L.carrier,
      ∀ x : L'.carrier, Q (ψ x : V) = Q' (x : W) := by
  obtain ⟨ψ⟩ := numberField_hyperbolic_cancellation_ambient Q Q' L L' hA hE φ
  exact ⟨ψ.toModuleEquiv, ψ.toModuleEquiv_q⟩

end NormEuclidean
