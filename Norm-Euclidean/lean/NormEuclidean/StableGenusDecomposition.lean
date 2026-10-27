import NormEuclidean.UnaryStableClassNumber

/-!
# The two-class stable genus in every positive rank

The stable equality includes ternary stabilizations of unary lattices. For
each nonprincipal fractional ideal the two specified global integral
isometry classes are distinct, belong to the genus, and exhaust it.
-/

noncomputable section

namespace NormEuclidean.StableGenusDecomposition

open scoped nonZeroDivisors

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

omit [Invertible (2 : K)] in
/-- The two proposed representatives are distinct even when the original rank is one. -/
theorem not_isometric (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (I : FractionalIdeal (integerSubring K)⁰ K) (hI : I ≠ 0)
    (hprincipal : ¬(I : Submodule (integerSubring K) K).IsPrincipal) :
    ¬GloballyIsometric (Hyperbolic.form Q) L.hyperbolic
      (IdealHyperbolic.lattice L I hI) := by
  rintro ⟨e⟩
  exact hprincipal (IdealHyperbolic.isPrincipal_of_isometry L L I hI hA hE e.inverse)

/-- Every stable genus member is isometric to a specified representative, in every positive rank. -/
theorem standard_or_ideal (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hpos : 1 ≤ Module.finrank K V) (hclass : NumberField.classNumber K = 2)
    (I : FractionalIdeal (integerSubring K)⁰ K) (hI : I ≠ 0)
    (hprincipal : ¬(I : Submodule (integerSubring K) K).IsPrincipal)
    (M : Lattice (integerSubring K) (Hyperbolic.form Q))
    (hgen : SameGenus (Hyperbolic.form Q) L.hyperbolic M) :
    GloballyIsometric (Hyperbolic.form Q) L.hyperbolic M ∨
      GloballyIsometric (Hyperbolic.form Q) (IdealHyperbolic.lattice L I hI) M := by
  let H := Hyperbolic.form Q
  let A : GenusMember H L.hyperbolic := selfGenusMember H L.hyperbolic
  let B : GenusMember H L.hyperbolic :=
    ⟨IdealHyperbolic.lattice L I hI, IdealHyperbolicGenus.sameGenus Q L I hI⟩
  let C : GenusMember H L.hyperbolic := ⟨M, hgen⟩
  let a : GenusClassSet H L.hyperbolic := Quotient.mk _ A
  let b : GenusClassSet H L.hyperbolic := Quotient.mk _ B
  let c : GenusClassSet H L.hyperbolic := Quotient.mk _ C
  have hb : b ≠ a := by
    intro h
    exact not_isometric L hA hE I hI hprincipal
      (GloballyIsometric.symm H (Quotient.exact h))
  have hcard : Nat.card (GenusClassSet H L.hyperbolic) = 2 :=
    (UnaryStableClassNumber.equality_of_positive_rank L hA hE hpos).trans hclass
  obtain ⟨t, _, hunique⟩ := (Nat.card_eq_two_iff' a).mp hcard
  by_cases hca : c = a
  · exact Or.inl (GloballyIsometric.symm H (Quotient.exact hca))
  · have hcb : c = b := (hunique c hca).trans (hunique b hb).symm
    exact Or.inr (GloballyIsometric.symm H (Quotient.exact hcb))

/-- The stable genus condition is equivalent to membership in one of the two actual classes. -/
theorem sameGenus_iff (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hpos : 1 ≤ Module.finrank K V) (hclass : NumberField.classNumber K = 2)
    (I : FractionalIdeal (integerSubring K)⁰ K) (hI : I ≠ 0)
    (hprincipal : ¬(I : Submodule (integerSubring K) K).IsPrincipal)
    (M : Lattice (integerSubring K) (Hyperbolic.form Q)) :
    SameGenus (Hyperbolic.form Q) L.hyperbolic M ↔
      GloballyIsometric (Hyperbolic.form Q) L.hyperbolic M ∨
        GloballyIsometric (Hyperbolic.form Q) (IdealHyperbolic.lattice L I hI) M := by
  constructor
  · exact standard_or_ideal L hA hE hpos hclass I hI hprincipal M
  · intro h
    rcases h with h | h
    · obtain ⟨e⟩ := h
      exact allPlaceLocallyIsometric_of_isometry e
    · obtain ⟨e⟩ := h
      exact allPlaceLocallyIsometric_trans (IdealHyperbolicGenus.sameGenus Q L I hI)
        (allPlaceLocallyIsometric_of_isometry e)

/-- The genus is the union of the two global isometry classes, including unary inputs. -/
theorem genus_eq_union (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hpos : 1 ≤ Module.finrank K V) (hclass : NumberField.classNumber K = 2)
    (I : FractionalIdeal (integerSubring K)⁰ K) (hI : I ≠ 0)
    (hprincipal : ¬(I : Submodule (integerSubring K) K).IsPrincipal) :
    {M | SameGenus (Hyperbolic.form Q) L.hyperbolic M} =
      {M | GloballyIsometric (Hyperbolic.form Q) L.hyperbolic M} ∪
        {M | GloballyIsometric (Hyperbolic.form Q) (IdealHyperbolic.lattice L I hI) M} := by
  ext M
  exact sameGenus_iff L hA hE hpos hclass I hI hprincipal M

omit [Invertible (2 : K)] in
/-- The two classes in the displayed union are disjoint. -/
theorem classes_disjoint (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (I : FractionalIdeal (integerSubring K)⁰ K) (hI : I ≠ 0)
    (hprincipal : ¬(I : Submodule (integerSubring K) K).IsPrincipal) :
    Disjoint {M | GloballyIsometric (Hyperbolic.form Q) L.hyperbolic M}
      {M | GloballyIsometric (Hyperbolic.form Q) (IdealHyperbolic.lattice L I hI) M} := by
  apply Set.disjoint_left.mpr
  intro M hM hI'
  exact not_isometric L hA hE I hI hprincipal
    (GloballyIsometric.trans _ hM (GloballyIsometric.symm _ hI'))

end NormEuclidean.StableGenusDecomposition
