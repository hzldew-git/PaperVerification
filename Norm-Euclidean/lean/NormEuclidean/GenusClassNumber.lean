import NormEuclidean.AllPlaceGenus

/-!
# Global classes inside an ordinary genus

The manuscript's lattice class number counts global integral isometry classes
inside the ordinary genus.  This file represents that class set exactly and
defines the proposition that it has one element.  It does not prove that a
norm-Euclidean lattice has class number one; that is the remaining global
theorem.
-/

namespace NormEuclidean

section GlobalIsometry

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V) {R : Subring K}

namespace LatticeIsometry

/-- Identity integral isometry of a lattice. -/
def identity (M : Lattice R Q) : LatticeIsometry Q Q M.carrier M.carrier where
  toLinearEquiv := LinearEquiv.refl K V
  q_eq := fun _ => rfl
  mem_iff := fun _ => Iff.rfl

end LatticeIsometry

/-- Global integral isometry of two lattices in the same quadratic space. -/
def GloballyIsometric (M M' : Lattice R Q) : Prop :=
  Nonempty (LatticeIsometry Q Q M.carrier M'.carrier)

namespace GloballyIsometric

theorem refl (M : Lattice R Q) : GloballyIsometric Q M M :=
  ⟨LatticeIsometry.identity Q M⟩

theorem symm {M M' : Lattice R Q}
    (h : GloballyIsometric Q M M') : GloballyIsometric Q M' M := by
  obtain ⟨e⟩ := h
  exact ⟨e.inverse⟩

theorem trans {M M' M'' : Lattice R Q}
    (h : GloballyIsometric Q M M') (h' : GloballyIsometric Q M' M'') :
    GloballyIsometric Q M M'' := by
  obtain ⟨e⟩ := h
  obtain ⟨e'⟩ := h'
  exact ⟨e.compose e'⟩

end GloballyIsometric

end GlobalIsometry

section GenusClasses

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

/-- A lattice together with evidence that it lies in the ordinary genus of
`M`. -/
def GenusMember (M : Lattice (integerSubring K) Q) :=
  {M' : Lattice (integerSubring K) Q // SameGenus Q M M'}

/-- Two members of one genus represent the same class precisely when they are
globally integrally isometric. -/
def genusClassSetoid (M : Lattice (integerSubring K) Q) :
    Setoid (GenusMember Q M) where
  r A B := GloballyIsometric Q A.1 B.1
  iseqv := ⟨fun A => GloballyIsometric.refl Q A.1,
    fun h => GloballyIsometric.symm Q h,
    fun h h' => GloballyIsometric.trans Q h h'⟩

/-- Global integral isometry classes in the ordinary genus of `M`. -/
def GenusClassSet (M : Lattice (integerSubring K) Q) :=
  Quotient (genusClassSetoid Q M)

/-- The exact proposition expressed in the paper as `h(M) = 1`. -/
def HasLatticeClassNumberOne (M : Lattice (integerSubring K) Q) : Prop :=
  Subsingleton (GenusClassSet Q M)

/-- The base lattice is a member of its own genus. -/
def selfGenusMember (M : Lattice (integerSubring K) Q) : GenusMember Q M :=
  ⟨M, allPlaceLocallyIsometric_refl Q M.carrier⟩

instance genusClassSet_nonempty (M : Lattice (integerSubring K) Q) :
    Nonempty (GenusClassSet Q M) :=
  ⟨Quotient.mk (genusClassSetoid Q M) (selfGenusMember Q M)⟩

/-- The class set has one element if and only if every lattice in the ordinary
genus is globally integrally isometric to the base lattice. -/
theorem hasLatticeClassNumberOne_iff (M : Lattice (integerSubring K) Q) :
    HasLatticeClassNumberOne Q M ↔
      ∀ M' : Lattice (integerSubring K) Q,
        SameGenus Q M M' → GloballyIsometric Q M M' := by
  constructor
  · intro h M' hM'
    let A : GenusMember Q M := selfGenusMember Q M
    let B : GenusMember Q M := ⟨M', hM'⟩
    have heq : Quotient.mk (genusClassSetoid Q M) A =
        Quotient.mk (genusClassSetoid Q M) B :=
      @Subsingleton.elim (GenusClassSet Q M) h _ _
    exact Quotient.exact heq
  · intro h
    constructor
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro A B
    apply Quotient.sound
    obtain ⟨eA⟩ := h A.1 A.2
    obtain ⟨eB⟩ := h B.1 B.2
    exact ⟨eA.inverse.compose eB⟩

end GenusClasses

end NormEuclidean
