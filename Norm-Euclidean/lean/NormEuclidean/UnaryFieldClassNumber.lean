import NormEuclidean.EuclideanIdealClasses
import NormEuclidean.UnaryIdealSquare
import NormEuclidean.UnaryClassNumber

/-!
# The unary field class-number theorem from the original hypotheses

The ideal model, norm descent, and square-class calculation prove the ordinary
field class number bound. Equality with two is precisely the obstruction to an
integral basis of the original lattice. No Euclidean ideal or class-number
premise is supplied by the caller.
-/

noncomputable section

namespace NormEuclidean.UnaryFieldClassNumber

open scoped NumberField
open EuclideanIdealDescent

variable {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- The original unary norm-Euclidean hypothesis makes the field class number divide two. -/
theorem classNumber_dvd_two (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 1) : NumberField.classNumber K ∣ 2 := by
  obtain ⟨M, ⟨e⟩⟩ := UnaryIdealModel.exists_model Q L hA hdim
  have hM := (UnaryIdealModel.approximation_iff e).mpr hE
  exact classNumber_dvd_two_of_sq M.ideal M.ideal_ne_zero
    (UnaryIdealNorm.normEuclidean_ideal M hM) (UnaryIdealSquare.idealClass_sq M hM)

/-- The actual field class number is at most two, with no freeness assumption. -/
theorem classNumber_le_two (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 1) : NumberField.classNumber K ≤ 2 :=
  Nat.le_of_dvd (by decide) (classNumber_dvd_two L hA hE hdim)

/-- Class number one is equivalent to freeness of the original unary lattice. -/
theorem classNumber_eq_one_iff_free (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 1) :
    NumberField.classNumber K = 1 ↔ Module.Free (integerSubring K) L.carrier := by
  obtain ⟨M, ⟨e⟩⟩ := UnaryIdealModel.exists_model Q L hA hdim
  have hM := (UnaryIdealModel.approximation_iff e).mpr hE
  exact (classNumber_eq_one_iff_isPrincipal M.ideal M.ideal_ne_zero
    (UnaryIdealNorm.normEuclidean_ideal M hM)).trans
      (UnaryIdealModel.free_iff_model_isPrincipal M e).symm

/-- The exceptional field class number two occurs exactly for nonfree unary lattices. -/
theorem classNumber_eq_two_iff_not_free (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 1) :
    NumberField.classNumber K = 2 ↔ ¬Module.Free (integerSubring K) L.carrier := by
  obtain ⟨M, ⟨e⟩⟩ := UnaryIdealModel.exists_model Q L hA hdim
  have hM := (UnaryIdealModel.approximation_iff e).mpr hE
  exact (classNumber_eq_two_iff_not_isPrincipal M.ideal M.ideal_ne_zero
    (UnaryIdealNorm.normEuclidean_ideal M hM) (UnaryIdealSquare.idealClass_sq M hM)).trans
      (not_congr (UnaryIdealModel.free_iff_model_isPrincipal M e).symm)

/-- The complete unary field/lattice statement, retaining the original integral module. -/
theorem field_and_lattice_class_number (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 1) :
    HasLatticeClassNumberOne Q L ∧ NumberField.classNumber K ≤ 2 ∧
      (NumberField.classNumber K = 2 ↔ ¬Module.Free (integerSubring K) L.carrier) := by
  letI : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
  exact ⟨UnaryClassNumber.classNumberOne L
      (quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hA) hdim,
    classNumber_le_two L hA hE hdim, classNumber_eq_two_iff_not_free L hA hE hdim⟩

end NormEuclidean.UnaryFieldClassNumber
