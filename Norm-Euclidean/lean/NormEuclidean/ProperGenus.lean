import NormEuclidean.HyperbolicSpinor
import NormEuclidean.GenusClassNumber
import Bong.QuadraticSpace.IsometryDeterminant

/-!
# Proper classes and the ordinary genus

Proper means determinant one. We count proper global integral classes inside
the already defined ordinary genus. When the base lattice represents one,
a norm-one reflection adjusts any improper local isometry to a proper one.
The hyperbolic enlargement has this property at every finite place.
No uniqueness theorem or strong approximation is asserted here.
-/

namespace NormEuclidean

section ProperIsometry

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {R : Subring K} (Q : QuadraticForm K V)

/-- Global integral isometry with determinant one. -/
def ProperlyGloballyIsometric (L M : Lattice R Q) : Prop :=
  ∃ e : LatticeIsometry Q Q L.carrier M.carrier, LinearEquiv.det e.toLinearEquiv = 1

namespace ProperlyGloballyIsometric

theorem refl (L : Lattice R Q) : ProperlyGloballyIsometric Q L L :=
  ⟨LatticeIsometry.identity Q L, LinearEquiv.det_refl⟩

theorem symm {L M : Lattice R Q} (h : ProperlyGloballyIsometric Q L M) :
    ProperlyGloballyIsometric Q M L := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.inverse, ?_⟩
  change LinearEquiv.det e.toLinearEquiv.symm = 1
  rw [LinearEquiv.det_symm, map_inv, he, inv_one]

theorem trans {L M N : Lattice R Q} (h : ProperlyGloballyIsometric Q L M)
    (h' : ProperlyGloballyIsometric Q M N) : ProperlyGloballyIsometric Q L N := by
  obtain ⟨e, he⟩ := h
  obtain ⟨f, hf⟩ := h'
  refine ⟨e.compose f, ?_⟩
  change LinearEquiv.det (e.toLinearEquiv.trans f.toLinearEquiv) = 1
  rw [LinearEquiv.det_trans, he, hf, mul_one]

theorem globallyIsometric {L M : Lattice R Q} (h : ProperlyGloballyIsometric Q L M) :
    GloballyIsometric Q L M := by
  obtain ⟨e, _⟩ := h
  exact ⟨e⟩

end ProperlyGloballyIsometric

variable [CharZero K] [FiniteDimensional K V]

/-- A norm-one integral reflection corrects the determinant sign of any
integral isometry from the given lattice. -/
theorem exists_proper_isometry_of_isometry_of_represents_one
    (hQ : Q.polarBilin.Nondegenerate) (L M : Submodule R V)
    (hInt : ∀ x ∈ L, Q x ∈ R) (hOne : ∃ w ∈ L, Q w = 1)
    (e : LatticeIsometry Q Q L M) :
    ∃ f : LatticeIsometry Q Q L M, LinearEquiv.det f.toLinearEquiv = 1 := by
  have hsign : LinearEquiv.det e.toLinearEquiv = 1 ∨
      LinearEquiv.det e.toLinearEquiv = (-1 : Kˣ) :=
    (SpinorBridge.toBongIsometry hQ hQ e).det_eq_one_or_neg_one
  rcases hsign with he | he
  · exact ⟨e, he⟩
  · obtain ⟨w, hw, hwQ⟩ := hOne
    have hw0 : Q w ≠ 0 := by simp [hwQ]
    have hinv : (Q w)⁻¹ ∈ R := by rw [hwQ, inv_one]; exact R.one_mem
    let r := IntegralReflection.isometry Q R L hInt w hw hw0 hinv
    refine ⟨r.compose e, ?_⟩
    change LinearEquiv.det (r.toLinearEquiv.trans e.toLinearEquiv) = 1
    rw [LinearEquiv.det_trans, he,
      SpinorBridge.det_integralReflection Q hQ R L hInt w hw hw0 hinv]
    simp

end ProperIsometry

section ProperClasses

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V]
  (Q : QuadraticForm K V)

/-- Proper global integral isometry classes within the ordinary genus. -/
def properGenusClassSetoid (L : Lattice (integerSubring K) Q) :
    Setoid (GenusMember Q L) where
  r A B := ProperlyGloballyIsometric Q A.1 B.1
  iseqv := ⟨fun A ↦ ProperlyGloballyIsometric.refl Q A.1,
    fun h ↦ ProperlyGloballyIsometric.symm Q h,
    fun h h' ↦ ProperlyGloballyIsometric.trans Q h h'⟩

/-- The proper class set of the full ordinary genus. -/
def ProperGenusClassSet (L : Lattice (integerSubring K) Q) :=
  Quotient (properGenusClassSetoid Q L)

/-- The genus consists of exactly one proper global integral class. -/
def HasProperLatticeClassNumberOne (L : Lattice (integerSubring K) Q) : Prop :=
  Subsingleton (ProperGenusClassSet Q L)

instance properGenusClassSet_nonempty (L : Lattice (integerSubring K) Q) :
    Nonempty (ProperGenusClassSet Q L) :=
  ⟨Quotient.mk (properGenusClassSetoid Q L) (selfGenusMember Q L)⟩

theorem hasProperLatticeClassNumberOne_iff (L : Lattice (integerSubring K) Q) :
    HasProperLatticeClassNumberOne Q L ↔
      ∀ M : Lattice (integerSubring K) Q,
        SameGenus Q L M → ProperlyGloballyIsometric Q L M := by
  constructor
  · intro h M hM
    have heq : Quotient.mk (properGenusClassSetoid Q L) (selfGenusMember Q L) =
        Quotient.mk (properGenusClassSetoid Q L) ⟨M, hM⟩ :=
      @Subsingleton.elim (ProperGenusClassSet Q L) h _ _
    exact Quotient.exact heq
  · intro h
    constructor
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro A B
    exact Quotient.sound (ProperlyGloballyIsometric.trans Q
      (ProperlyGloballyIsometric.symm Q (h A.1 A.2)) (h B.1 B.2))

/-- Forgetting determinant one maps proper classes onto ordinary classes. -/
def properToOrdinaryClass (L : Lattice (integerSubring K) Q) :
    ProperGenusClassSet Q L → GenusClassSet Q L :=
  Quotient.map id (fun _ _ h ↦ ProperlyGloballyIsometric.globallyIsometric Q h)

theorem properToOrdinaryClass_surjective (L : Lattice (integerSubring K) Q) :
    Function.Surjective (properToOrdinaryClass Q L) := by
  intro x
  refine Quotient.inductionOn x ?_
  intro A
  exact ⟨Quotient.mk (properGenusClassSetoid Q L) A, rfl⟩

/-- A genus with one proper class has one ordinary class. -/
theorem hasLatticeClassNumberOne_of_proper (L : Lattice (integerSubring K) Q)
    (h : HasProperLatticeClassNumberOne Q L) : HasLatticeClassNumberOne Q L := by
  rw [hasLatticeClassNumberOne_iff]
  intro M hM
  exact ProperlyGloballyIsometric.globallyIsometric Q
    ((hasProperLatticeClassNumberOne_iff Q L).mp h M hM)

/-- Proper finite-place comparisons in a fixed ambient quadratic space.
At infinite places the ambient identity is automatically proper. -/
def SameProperGenus (L M : Lattice (integerSubring K) Q) : Prop :=
  ∀ v : IsDedekindDomain.HeightOneSpectrum (integerSubring K),
    ∃ e : LatticeIsometry (CompletedIntegralLattice.form (integerSubring K) v Q)
        (CompletedIntegralLattice.form (integerSubring K) v Q)
        (CompletedIntegralLattice.carrier (integerSubring K) v L.carrier)
        (CompletedIntegralLattice.carrier (integerSubring K) v M.carrier),
      LinearEquiv.det e.toLinearEquiv = 1

theorem sameGenus_of_sameProperGenus {L M : Lattice (integerSubring K) Q}
    (h : SameProperGenus Q L M) : SameGenus Q L M := by
  rw [sameGenus_iff_finite]
  intro v
  obtain ⟨e, _⟩ := h v
  exact ⟨e⟩

/-- For a hyperbolic enlargement, every ordinary local comparison can be
made proper by a reflection of a represented unit one. -/
theorem hyperbolic_sameGenus_iff_sameProperGenus
    (hQ : Q.polarBilin.Nondegenerate) (L : Lattice (integerSubring K) Q)
    (M : Lattice (integerSubring K) (Hyperbolic.form Q)) :
    SameGenus (Hyperbolic.form Q) L.hyperbolic M ↔
      SameProperGenus (Hyperbolic.form Q) L.hyperbolic M := by
  letI := L.finiteDimensional
  constructor
  · intro h v
    obtain ⟨e⟩ := h.1 v
    exact exists_proper_isometry_of_isometry_of_represents_one _
      (CompletedIntegralLattice.hyperbolic_form_polarBilin_nondegenerate _ v Q hQ) _ _
      (CompletedIntegralLattice.carrier_integral _ v _ _ L.hyperbolic.integral)
      (CompletedIntegralLattice.hyperbolic_represents _ v Q L.carrier 1) e
  · exact sameGenus_of_sameProperGenus _

end ProperClasses

end NormEuclidean
