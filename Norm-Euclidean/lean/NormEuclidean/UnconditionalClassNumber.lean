import NormEuclidean.GoodReduction
import NormEuclidean.GoodPrimePrincipality
import NormEuclidean.FiniteBadPrimesPID
import NormEuclidean.Maximality

/-!
# Unconditional field class number one in rank at least three

Good reduction supplies isotropic residue vectors outside finitely many
primes. For each such prime, an elementary coprime ideal complement and norm
descent prove principality. Dedekind factorization and the Chinese remainder
theorem then remove the finite exceptional set. No inverse-class prime
existence theorem, integral basis, PID, or class-number hypothesis is used.

The field class number here is `NumberField.classNumber K`. These theorems
do not assert the lattice genus class number is one.
-/

namespace NormEuclidean

open scoped nonZeroDivisors NumberField

variable {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V}

/-- An isotropic nonzero residue vector forces the corresponding nonzero
prime ideal to be principal. The lattice may initially be nonfree. -/
theorem prime_isPrincipal_of_isotropic_residue
    (L : Lattice (integerSubring K) Q) (hA : Q.Anisotropic)
    (hE : HasNumberFieldApproximation Q L.carrier)
    (p : Ideal (integerSubring K)) (hp : p.IsMaximal) (hp0 : p ≠ ⊥)
    (w : V) (hw : w ∈ L.carrier)
    (hwp : w ∉ (p : FractionalIdeal (integerSubring K)⁰ K).1 • L.carrier)
    (hQw : Q w ∈ (p : FractionalIdeal (integerSubring K)⁰ K)) :
    p.IsPrincipal := by
  obtain ⟨i, hi, hcop, a, ha0, hgen⟩ := exists_coprime_ideal_mul_eq_span p hp hp0
  have haK : (a : K) ≠ 0 := by
    intro h
    exact ha0 (Subtype.ext h)
  have hgenK : (i : FractionalIdeal (integerSubring K)⁰ K) *
      (p : FractionalIdeal (integerSubring K)⁰ K) =
      FractionalIdeal.spanSingleton (integerSubring K)⁰ (a : K) := by
    rw [← FractionalIdeal.coeIdeal_mul, hgen, FractionalIdeal.coeIdeal_span_singleton]
    rfl
  obtain ⟨c, _, hc⟩ := numberField_ideal_principal_of_good_prime
    L hA hE i p hi hp hp0 hcop (a : K) haK hgenK w hw hwp hQw
  letI : i.IsPrincipal := ⟨c, hc⟩
  exact isPrincipal_of_mul_eq_span i p hi hgen

/-- The rank-at-least-three PID conclusion, with no unproved arithmetic input. -/
theorem isPrincipalIdealRing_of_rank_ge_three
    (L : Lattice (integerSubring K) Q) (hdim : 3 ≤ Module.finrank K V)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier) :
    IsPrincipalIdealRing (integerSubring K) := by
  obtain ⟨t, ht, hresidue⟩ := exists_good_reduction_denominator L hdim
  apply isPrincipalIdealRing_of_principal_primes_away (2 * t)
    (mul_ne_zero (by norm_num) ht)
  intro p hp hp0 havoid
  have htwo : (2 : integerSubring K) ∉ p := by
    intro h
    exact havoid (p.mul_mem_right t h)
  have htp : t ∉ p := by
    intro h
    exact havoid (p.mul_mem_left 2 h)
  obtain ⟨w, hw, hwp, hQw⟩ := hresidue p hp hp0 htwo htp
  exact prime_isPrincipal_of_isotropic_residue L hA hE p hp hp0 w hw hwp hQw

/-- The actual number-field class number is one in rank at least three. -/
theorem classNumber_eq_one_of_rank_ge_three
    (L : Lattice (integerSubring K) Q) (hdim : 3 ≤ Module.finrank K V)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier) :
    NumberField.classNumber K = 1 :=
  NumberField.classNumber_eq_one_iff.mpr
    (isPrincipalIdealRing_of_rank_ge_three L hdim hA hE)

/-- Freeness is a conclusion from finite generation and torsion-freeness. -/
theorem lattice_free_of_rank_ge_three
    (L : Lattice (integerSubring K) Q) (hdim : 3 ≤ Module.finrank K V)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier) :
    Module.Free (integerSubring K) L.carrier := by
  letI : IsPrincipalIdealRing (integerSubring K) :=
    isPrincipalIdealRing_of_rank_ge_three L hdim hA hE
  letI : Module.Finite (integerSubring K) L.carrier := Module.Finite.iff_fg.mpr L.finite
  letI : NoZeroSMulDivisors (integerSubring K) V := by
    constructor
    intro c x h
    have hK : (c : K) • x = 0 := h
    rcases smul_eq_zero.mp hK with hc | hx
    · exact Or.inl (Subtype.ext hc)
    · exact Or.inr hx
  exact Module.free_of_finite_type_torsion_free'

/-- The unconditional field-class-number and freeness conclusions. -/
theorem classNumber_and_freeness_of_rank_ge_three
    (L : Lattice (integerSubring K) Q) (hdim : 3 ≤ Module.finrank K V)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier) :
    IsPrincipalIdealRing (integerSubring K) ∧ NumberField.classNumber K = 1 ∧
      Module.Free (integerSubring K) L.carrier :=
  ⟨isPrincipalIdealRing_of_rank_ge_three L hdim hA hE,
    classNumber_eq_one_of_rank_ge_three L hdim hA hE,
    lattice_free_of_rank_ge_three L hdim hA hE⟩

/-- Rank-at-least-three freeness together with full integral maximality. -/
theorem free_and_maximal_of_rank_ge_three
    (L : Lattice (integerSubring K) Q) (hdim : 3 ≤ Module.finrank K V)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier) :
    Module.Free (integerSubring K) L.carrier ∧
      ∀ M : Lattice (integerSubring K) Q,
        L.carrier ≤ M.carrier → L.carrier = M.carrier := by
  refine ⟨lattice_free_of_rank_ge_three L hdim hA hE, ?_⟩
  intro M hLM
  exact numberField_normEuclidean_maximal Q L hA hE M.carrier hLM M.integral

end NormEuclidean
