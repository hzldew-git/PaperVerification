import NormEuclidean.IdealRealization
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Conditional class-number and freeness reduction

This file exposes the exact unproved arithmetic input in Step 1 of Theorem 1.2 (reference manuscript):
for each nonzero ideal, a coprime prime in the inverse ideal class with a
nonzero isotropic residue vector. From that concrete input, the actual
isotropic-content construction and norm descent prove that every ideal is
principal. The standard class-number and torsion-free-module theorems then
prove class number one and lattice freeness.

The field-theoretic existence of the good primes, and the good-reduction
construction of their residue vectors, are **not** proved here. Accordingly,
these are explicitly conditional reductions, not unconditional Theorem 1.2 (reference manuscript).
No content-realization conclusion, PID assumption, or lattice basis is part
of the input.
-/

namespace NormEuclidean

open scoped nonZeroDivisors NumberField

variable {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V}

/-- The explicit remaining arithmetic data for every nonzero integral ideal.
The generator is an actual algebraic integer; the residue vector is supplied
as an integral representative, with nonvanishing and isotropy modulo `p`.
This is a hypothesis interface, not a theorem asserting prime existence. -/
def HasGoodPrimeData (L : Lattice (integerSubring K) Q) : Prop :=
  ∀ i : Ideal (integerSubring K), i ≠ ⊥ →
    ∃ p : Ideal (integerSubring K), p.IsMaximal ∧ p ≠ ⊥ ∧ IsCoprime i p ∧
      ∃ a : integerSubring K, a ≠ 0 ∧ i * p = Ideal.span {a} ∧
        ∃ w : V, w ∈ L.carrier ∧
          w ∉ (p : FractionalIdeal (integerSubring K)⁰ K).1 • L.carrier ∧
          Q w ∈ (p : FractionalIdeal (integerSubring K)⁰ K)

/-- Actual ideal principality follows from the explicit good-prime data by
the constructed isotropic vector and Lemma 2.4. -/
theorem isPrincipalIdealRing_of_good_prime_data
    (L : Lattice (integerSubring K) Q) (hA : Q.Anisotropic)
    (hE : HasNumberFieldApproximation Q L.carrier) (hdata : HasGoodPrimeData L) :
    IsPrincipalIdealRing (integerSubring K) := by
  constructor
  intro i
  by_cases hi : i = ⊥
  · subst i
    infer_instance
  · obtain ⟨p, hp, hp0, hicop, a, ha0, hgen, w, hw, hwp, hQw⟩ := hdata i hi
    have haK : (a : K) ≠ 0 := by
      intro h
      exact ha0 (Subtype.ext h)
    have hgenK : (i : FractionalIdeal (integerSubring K)⁰ K) *
        (p : FractionalIdeal (integerSubring K)⁰ K) =
        FractionalIdeal.spanSingleton (integerSubring K)⁰ (a : K) := by
      rw [← FractionalIdeal.coeIdeal_mul, hgen, FractionalIdeal.coeIdeal_span_singleton]
      rfl
    obtain ⟨c, _, hc⟩ := numberField_ideal_principal_of_good_prime L hA hE
      i p hi hp hp0 hicop (a : K) haK hgenK w hw hwp hQw
    exact ⟨c, hc⟩

/-- Conditional Step 1: the actual number-field class number is one. -/
theorem classNumber_eq_one_of_good_prime_data
    (L : Lattice (integerSubring K) Q) (hA : Q.Anisotropic)
    (hE : HasNumberFieldApproximation Q L.carrier) (hdata : HasGoodPrimeData L) :
    NumberField.classNumber K = 1 :=
  NumberField.classNumber_eq_one_iff.mpr
    (isPrincipalIdealRing_of_good_prime_data L hA hE hdata)

/-- Conditional Step 2: freeness is deduced from the proved PID conclusion
and finite torsion-freeness, rather than assumed in the lattice interface. -/
theorem lattice_free_of_good_prime_data
    (L : Lattice (integerSubring K) Q) (hA : Q.Anisotropic)
    (hE : HasNumberFieldApproximation Q L.carrier) (hdata : HasGoodPrimeData L) :
    Module.Free (integerSubring K) L.carrier := by
  letI : IsPrincipalIdealRing (integerSubring K) :=
    isPrincipalIdealRing_of_good_prime_data L hA hE hdata
  letI : Module.Finite (integerSubring K) L.carrier := Module.Finite.iff_fg.mpr L.finite
  letI : NoZeroSMulDivisors (integerSubring K) V := by
    constructor
    intro c x h
    have hK : (c : K) • x = 0 := h
    rcases smul_eq_zero.mp hK with hc | hx
    · exact Or.inl (Subtype.ext hc)
    · exact Or.inr hx
  exact Module.free_of_finite_type_torsion_free'

/-- Combined conditional class-number/freeness endpoint. Its good-prime
hypothesis records precisely the remaining arithmetic construction. -/
theorem classNumber_and_freeness_of_good_prime_data
    (L : Lattice (integerSubring K) Q) (hA : Q.Anisotropic)
    (hE : HasNumberFieldApproximation Q L.carrier) (hdata : HasGoodPrimeData L) :
    IsPrincipalIdealRing (integerSubring K) ∧ NumberField.classNumber K = 1 ∧
      Module.Free (integerSubring K) L.carrier :=
  ⟨isPrincipalIdealRing_of_good_prime_data L hA hE hdata,
    classNumber_eq_one_of_good_prime_data L hA hE hdata,
    lattice_free_of_good_prime_data L hA hE hdata⟩

end NormEuclidean
