import NormEuclidean.IdealHyperbolicGenus
import NormEuclidean.UnaryFieldClassNumber
import NormEuclidean.BinaryFieldArithmetic
import NormEuclidean.OrdinaryGenusMass

/-!
# The lower bound in the stable class-number equality

An actual nonprincipal ideal gives a second ordinary genus class after
hyperbolic stabilization. With the now proved positive-rank field bound, this
gives h(F) <= h(L orthogonal H). The opposite inequality, particularly for a
unary target and a ternary stabilization, remains a separate spinor argument.
-/

noncomputable section

namespace NormEuclidean.StableClassNumberLowerBound

open scoped NumberField nonZeroDivisors

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

/-- A nonprincipal ideal constructs two distinct actual ordinary classes in the stabilized genus. -/
theorem two_le_of_nonprincipal (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (I : FractionalIdeal (integerSubring K)⁰ K) (hI : I ≠ 0)
    (hprincipal : ¬(I : Submodule (integerSubring K) K).IsPrincipal) :
    2 ≤ OrdinaryGenusMass.classNumber L.hyperbolic := by
  let H := Hyperbolic.form Q
  let A : GenusMember H L.hyperbolic := selfGenusMember H L.hyperbolic
  let B : GenusMember H L.hyperbolic :=
    ⟨IdealHyperbolic.lattice L I hI, IdealHyperbolicGenus.sameGenus Q L I hI⟩
  have hne : (Quotient.mk (genusClassSetoid H L.hyperbolic) A : GenusClassSet H L.hyperbolic) ≠
      Quotient.mk (genusClassSetoid H L.hyperbolic) B := by
    intro h
    obtain ⟨e⟩ := Quotient.exact h
    exact hprincipal (IdealHyperbolic.isPrincipal_of_isometry L L I hI hA hE e.inverse)
  letI : Finite (GenusClassSet H L.hyperbolic) :=
    GenusFiniteness.finite_integral_genus_classes H
      (Hyperbolic.form_polarBilin_nondegenerate Q
        (quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hA)) L.hyperbolic
  letI : Nontrivial (GenusClassSet H L.hyperbolic) := ⟨⟨_, _, hne⟩⟩
  exact Finite.one_lt_card

omit [Invertible (2 : K)] in
/-- A nontrivial ordinary field class group has an actual nonprincipal fractional ideal. -/
theorem exists_nonprincipal_of_classNumber_ne_one (hclass : NumberField.classNumber K ≠ 1) :
    ∃ I : FractionalIdeal (integerSubring K)⁰ K, I ≠ 0 ∧
      ¬(I : Submodule (integerSubring K) K).IsPrincipal := by
  have hpid : ¬IsPrincipalIdealRing (integerSubring K) :=
    fun h ↦ hclass (NumberField.classNumber_eq_one_iff.mpr h)
  obtain ⟨J, hJ⟩ : ∃ J : Ideal (integerSubring K), ¬J.IsPrincipal := by
    by_contra h
    apply hpid
    exact ⟨fun J ↦ not_not.mp (fun hn ↦ h ⟨J, hn⟩)⟩
  have hJ0 : J ≠ ⊥ := by
    intro h
    apply hJ
    rw [h]
    infer_instance
  refine ⟨J, FractionalIdeal.coeIdeal_ne_zero.mpr hJ0, ?_⟩
  intro h
  exact hJ ((IsFractionRing.coeSubmodule_isPrincipal
    (R := integerSubring K) (K := K) (I := J)).mp h)

/-- Nontrivial field class number forces at least two stabilized ordinary classes. -/
theorem two_le_of_classNumber_ne_one (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hclass : NumberField.classNumber K ≠ 1) :
    2 ≤ OrdinaryGenusMass.classNumber L.hyperbolic := by
  obtain ⟨I, hI, hnonprincipal⟩ := exists_nonprincipal_of_classNumber_ne_one hclass
  exact two_le_of_nonprincipal L hA hE I hI hnonprincipal

/-- The original field class-number bound now holds in every positive rank. -/
theorem field_classNumber_le_two (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hpos : 1 ≤ Module.finrank K V) : NumberField.classNumber K ≤ 2 := by
  by_cases hone : Module.finrank K V = 1
  · exact UnaryFieldClassNumber.classNumber_le_two L hA hE hone
  by_cases htwo : Module.finrank K V = 2
  · exact BinaryFieldArithmetic.classNumber_le_two L hA hE htwo
  rw [classNumber_eq_one_of_rank_ge_three L (by omega) hA hE]
  decide

/-- The field class number is a proved lower bound for the stabilized ordinary class number. -/
theorem field_classNumber_le_stable (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hpos : 1 ≤ Module.finrank K V) :
    NumberField.classNumber K ≤ OrdinaryGenusMass.classNumber L.hyperbolic := by
  by_cases hone : NumberField.classNumber K = 1
  · rw [hone]
    letI : Finite (GenusClassSet (Hyperbolic.form Q) L.hyperbolic) :=
      GenusFiniteness.finite_integral_genus_classes (Hyperbolic.form Q)
        (Hyperbolic.form_polarBilin_nondegenerate Q
          (quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hA)) L.hyperbolic
    exact Nat.card_pos
  · exact (field_classNumber_le_two L hA hE hpos).trans
      (two_le_of_classNumber_ne_one L hA hE hone)

/-- Explicit remaining reduction: an independently proved upper bound finishes stable equality. -/
theorem stable_equality_of_upper_bound (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hpos : 1 ≤ Module.finrank K V)
    (hupper : OrdinaryGenusMass.classNumber L.hyperbolic ≤ NumberField.classNumber K) :
    OrdinaryGenusMass.classNumber L.hyperbolic = NumberField.classNumber K :=
  le_antisymm hupper (field_classNumber_le_stable L hA hE hpos)

end NormEuclidean.StableClassNumberLowerBound
