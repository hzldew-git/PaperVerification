import NormEuclidean.UnaryFiniteness
import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# Comparing integral rank with ambient field dimension

Localization equates the integral and ambient ranks without assuming the
lattice free or the coefficient ring principal. This closes the unary-rank
convention gap with the manuscript; the unary theorems separately assume
freeness exactly where the manuscript does.
-/

namespace NormEuclidean

open scoped nonZeroDivisors

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {R : Subring K} [IsFractionRing R K] {Q : QuadraticForm K V}

/-- Integral module rank equals ambient field dimension for every full
lattice. No freeness or principal-ideal-ring hypothesis is used. -/
theorem Lattice.finrank_eq_ambient (L : Lattice R Q) :
    Module.finrank R L.carrier = Module.finrank K V := by
  letI := ScalarExtension.localizedSubtype L.carrier L.full
  have h₁ := IsLocalizedModule.finrank_eq R⁰ L.carrier.subtype le_rfl
  have h₂ := IsLocalization.rank_eq K R⁰ (N := V) le_rfl
  have h₂' : Module.finrank K V = Module.finrank R V :=
    congrArg Cardinal.toNat h₂
  exact h₁.symm.trans h₂'.symm

variable [NumberField K] (Q)

/-- The unary reduction with the manuscript's literal ambient rank-one
hypothesis and its separate freeness hypothesis. -/
theorem normEuclideanNumberField_of_freeUnary_ambient_rank
    (L : Lattice (integerSubring K) Q)
    [Module.Free (integerSubring K) L.carrier]
    (hrank : Module.finrank K V = 1)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier) :
    IsNormEuclideanNumberField K :=
  normEuclideanNumberField_of_freeUnary K Q L
    (L.finrank_eq_ambient.trans hrank) hA hE

/-- Scalar isometric normal form using ambient rank one, as stated in
Proposition `prop:unary-finiteness`. -/
theorem exists_freeUnary_model_ambient_rank
    (L : Lattice (integerSubring K) Q)
    [Module.Free (integerSubring K) L.carrier]
    (hrank : Module.finrank K V = 1) (hA : Q.Anisotropic) :
    ∃ a : NumberField.RingOfIntegers K, a ≠ 0 ∧
      ∃ e : integerModule K ≃ₗ[integerSubring K] L.carrier,
        (∀ x : integerModule K, Q (e x : V) = unaryForm K a (x : K)) ∧
        (HasNumberFieldApproximation Q L.carrier ↔
          HasNumberFieldApproximation (unaryForm K a) (integerModule K)) := by
  exact exists_freeUnary_model K Q L (L.finrank_eq_ambient.trans hrank) hA

/-- The norm-ideal bound under the manuscript's literal positive ambient
rank hypothesis. -/
theorem normIdeal_absNorm_lt_of_pos_finrank
    (L : Lattice (integerSubring K) Q) (hrank : 0 < Module.finrank K V)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier) :
    Ideal.absNorm L.normIdeal < 4 ^ Module.finrank ℚ K := by
  letI : Nontrivial V := Module.nontrivial_of_finrank_pos hrank
  exact normIdeal_absNorm_lt Q L hA hE

end NormEuclidean
