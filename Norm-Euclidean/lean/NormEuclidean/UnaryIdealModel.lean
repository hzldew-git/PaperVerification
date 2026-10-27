import NormEuclidean.FractionalIdealLattice
import NormEuclidean.Unary
import NormEuclidean.UnaryRankFiniteness

/-!
# Unary lattices on arbitrary fractional ideals

An ideal model retains the actual nonzero fractional ideal `I` and the scalar
quadratic form `c*x^2`. Every anisotropic rank-one integral lattice has such
a model. The ideal is not assumed principal, and the ambient coordinate
choice is not claimed to be an integral basis.
-/

noncomputable section

namespace NormEuclidean.UnaryIdealModel

open scoped nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

/-- A full integral unary lattice, with its possibly nonprincipal ideal retained. -/
structure Model where
  ideal : FractionalIdeal (integerSubring K)⁰ K
  ideal_ne_zero : ideal ≠ 0
  coefficient : K
  coefficient_ne_zero : coefficient ≠ 0
  integral : ∀ x ∈ ideal, coefficient * x ^ 2 ∈ integerSubring K

variable {K}

/-- The ideal model as the same full integral lattice structure used by the main library. -/
def Model.lattice (M : Model K) : Lattice (integerSubring K) (unaryForm K M.coefficient) where
  carrier := M.ideal
  finite := FractionalIdealLattice.fg M.ideal
  full := FractionalIdealLattice.full M.ideal M.ideal_ne_zero
  integral := by
    intro x hx
    rw [unaryForm_apply]
    exact M.integral x hx

@[simp] theorem Model.mem_lattice (M : Model K) (x : K) :
    x ∈ M.lattice.carrier ↔ x ∈ M.ideal := Iff.rfl

omit [NumberField K] in
/-- Nonzero coefficients make every ideal model anisotropic over the entire field. -/
theorem Model.anisotropic (M : Model K) : (unaryForm K M.coefficient).Anisotropic :=
  unaryForm_anisotropic K M.coefficient_ne_zero

/-- A model is free exactly when its retained fractional ideal is principal. -/
theorem Model.free_iff_isPrincipal (M : Model K) :
    Module.Free (integerSubring K) M.lattice.carrier ↔
      (M.ideal : Submodule (integerSubring K) K).IsPrincipal :=
  FractionalIdealLattice.free_iff_isPrincipal M.ideal M.ideal_ne_zero

/-- Nonprincipal ideals give genuinely nonfree integral unary lattices. -/
theorem Model.not_free_of_not_isPrincipal (M : Model K)
    (hM : ¬(M.ideal : Submodule (integerSubring K) K).IsPrincipal) :
    ¬Module.Free (integerSubring K) M.lattice.carrier :=
  fun h ↦ hM (M.free_iff_isPrincipal.mp h)

/-- An ambient lattice isometry preserves the original strict norm approximation property. -/
theorem approximation_iff {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {Q : QuadraticForm K V} {P : QuadraticForm K W}
    {L : Submodule (integerSubring K) V} {J : Submodule (integerSubring K) W}
    (e : LatticeIsometry Q P L J) :
    HasNumberFieldApproximation Q L ↔ HasNumberFieldApproximation P J := by
  constructor
  · intro h x
    obtain ⟨y, hy, hlt⟩ := h (e.toLinearEquiv.symm x)
    refine ⟨e.toLinearEquiv y, (e.mem_iff y).mpr hy, ?_⟩
    have hx : x - e.toLinearEquiv y = e.toLinearEquiv (e.toLinearEquiv.symm x - y) := by
      simp
    rw [hx, e.q_eq]
    exact hlt
  · intro h x
    obtain ⟨y, hy, hlt⟩ := h (e.toLinearEquiv x)
    refine ⟨e.toLinearEquiv.symm y, ?_, ?_⟩
    · exact (e.mem_iff _).mp (by simpa using hy)
    · have hx : e.toLinearEquiv x - y = e.toLinearEquiv (x - e.toLinearEquiv.symm y) := by
        simp
      rwa [hx, e.q_eq] at hlt

/-- Every anisotropic rank-one lattice has an actual fractional-ideal unary model.
The isometry identifies the entire integral module; no integral freeness is required. -/
theorem exists_model {V : Type*} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hrank : Module.finrank K V = 1) :
    ∃ M : Model K, Nonempty
      (LatticeIsometry (unaryForm K M.coefficient) Q M.lattice.carrier L.carrier) := by
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hrank
  have he1 : e (1 : K) ≠ 0 := e.map_ne_zero_iff.mpr one_ne_zero
  let I := GeneralContent.coefficientIdeal L.carrier L.finite (e 1) he1
  have hI : I ≠ 0 :=
    GeneralContent.coefficientIdeal_ne_zero L.carrier L.finite L.full (e 1) he1
  have hmem (x : K) : x ∈ I ↔ e x ∈ L.carrier := by
    change x • e 1 ∈ L.carrier ↔ e x ∈ L.carrier
    rw [← e.map_smul]
    simp only [smul_eq_mul, mul_one]
  have hform (x : K) : Q (e x) = unaryForm K (Q (e 1)) x := by
    have hx : e x = x • e 1 := by rw [← e.map_smul]; simp
    rw [hx, Q.map_smul, unaryForm_apply]
    simp only [smul_eq_mul]
    ring
  let M : Model K := {
    ideal := I
    ideal_ne_zero := hI
    coefficient := Q (e 1)
    coefficient_ne_zero := fun h ↦ he1 (hA _ h)
    integral := by
      intro x hx
      have h := L.integral (e x) ((hmem x).mp hx)
      rw [hform x, unaryForm_apply] at h
      exact h }
  refine ⟨M, ⟨{ toLinearEquiv := e, q_eq := hform, mem_iff := ?_ }⟩⟩
  exact fun x ↦ (hmem x).symm

/-- The ideal model and the original lattice have exactly the same norm-Euclidean property. -/
theorem exists_model_with_approximation {V : Type*} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hrank : Module.finrank K V = 1) :
    ∃ M : Model K,
      Nonempty (LatticeIsometry (unaryForm K M.coefficient) Q M.lattice.carrier L.carrier) ∧
      (HasNumberFieldApproximation (unaryForm K M.coefficient) M.lattice.carrier ↔
        HasNumberFieldApproximation Q L.carrier) := by
  obtain ⟨M, ⟨e⟩⟩ := exists_model Q L hA hrank
  exact ⟨M, ⟨e⟩, approximation_iff e⟩

/-- The model identifies freeness of the original lattice with principality of its ideal. -/
theorem free_iff_model_isPrincipal {V : Type*} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {L : Lattice (integerSubring K) Q} (M : Model K)
    (e : LatticeIsometry (unaryForm K M.coefficient) Q M.lattice.carrier L.carrier) :
    Module.Free (integerSubring K) L.carrier ↔
      (M.ideal : Submodule (integerSubring K) K).IsPrincipal :=
  (Module.Free.iff_of_equiv e.toModuleEquiv).symm.trans M.free_iff_isPrincipal

/-- Equivalence of ideal models means actual ambient integral isometry. -/
def modelSetoid : Setoid (Model K) where
  r M N := Nonempty (LatticeIsometry (unaryForm K M.coefficient)
    (unaryForm K N.coefficient) M.lattice.carrier N.lattice.carrier)
  iseqv := ⟨fun M ↦ ⟨LatticeIsometry.identity _ M.lattice⟩,
    fun ⟨e⟩ ↦ ⟨e.inverse⟩, fun ⟨e⟩ ⟨f⟩ ↦ ⟨e.compose f⟩⟩

/-- Integral-isometry classes of ideal unary models, allowing both ideal and coefficient to vary. -/
def ClassSet (K : Type*) [Field K] [NumberField K] := Quotient (modelSetoid (K := K))

/-- The class of an ideal unary lattice. -/
def classOf (M : Model K) : ClassSet K := Quotient.mk modelSetoid M

/-- Equality in the ideal-model quotient is precisely integral isometry. -/
theorem classOf_eq_iff (M N : Model K) :
    classOf M = classOf N ↔ Nonempty (LatticeIsometry (unaryForm K M.coefficient)
      (unaryForm K N.coefficient) M.lattice.carrier N.lattice.carrier) := Quotient.eq

/-- A field basis gives a coordinate presentation of the entire ideal lattice. -/
def Model.coordinates (M : Model K) : FixedFieldRankFiniteness.Model K 1 :=
  let b : Module.Basis (Fin 1) K K := Module.basisUnique (Fin 1) (by simp)
  ⟨(unaryForm K M.coefficient).basisRepr b,
    IntegralFrameIntervals.map M.lattice ((unaryForm K M.coefficient).isometryEquivBasisRepr b)⟩

/-- The coordinate presentation is an actual isometry, also for nonprincipal ideals. -/
def Model.coordinateIsometry (M : Model K) :
    LatticeIsometry (unaryForm K M.coefficient) M.coordinates.1
      M.lattice.carrier M.coordinates.2.carrier :=
  IntegralFrameIntervals.mapIsometry M.lattice _

/-- The ideal quotient maps to the existing coordinate quotient by actual isometry. -/
def toCoordinateClasses : ClassSet K → FixedFieldClassSet.ClassSet K 1 :=
  Quotient.lift (fun M ↦ FixedFieldClassSet.classOf K M.coordinates) (by
    intro M N h
    obtain ⟨e⟩ := h
    exact (FixedFieldClassSet.classOf_eq_iff K _ _).mpr
      ⟨M.coordinateIsometry.inverse.compose (e.compose N.coordinateIsometry)⟩)

@[simp] theorem toCoordinateClasses_classOf (M : Model K) :
    toCoordinateClasses (classOf M) = FixedFieldClassSet.classOf K M.coordinates := rfl

/-- No ideal-lattice isometry classes are identified by passing to coordinates. -/
theorem toCoordinateClasses_injective : Function.Injective (toCoordinateClasses (K := K)) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro M N h
  obtain ⟨e⟩ := (FixedFieldClassSet.classOf_eq_iff K _ _).mp h
  exact (classOf_eq_iff M N).mpr
    ⟨M.coordinateIsometry.compose (e.compose N.coordinateIsometry.inverse)⟩

/-- The norm-Euclidean classes in the ideal-model quotient. -/
def euclideanClasses : Set (ClassSet K) :=
  {c | ∃ M : Model K,
    HasNumberFieldApproximation (unaryForm K M.coefficient) M.lattice.carrier ∧ classOf M = c}

/-- Fixed-field finiteness also holds directly in the quotient of actual fractional-ideal
unary models, without excluding nonprincipal ideals or mixed real signatures. -/
theorem finite_euclideanClasses : (euclideanClasses (K := K)).Finite := by
  have hfinite := Set.Finite.preimage toCoordinateClasses_injective.injOn
    (UnaryRankFiniteness.finite_euclideanClasses K)
  apply hfinite.subset
  rintro c ⟨M, hM, rfl⟩
  change FixedFieldClassSet.classOf K M.coordinates ∈ UnaryRankFiniteness.euclideanClasses K
  have hA : M.coordinates.1.Anisotropic := by
    intro x hx
    let e := M.coordinateIsometry
    have hq : unaryForm K M.coefficient (e.toLinearEquiv.symm x) = 0 := by
      rw [← e.q_eq, e.toLinearEquiv.apply_symm_apply]
      exact hx
    have hz := M.anisotropic _ hq
    simpa using congrArg e.toLinearEquiv hz
  exact ⟨M.coordinates, hA, (approximation_iff M.coordinateIsometry).mp hM, rfl⟩

end NormEuclidean.UnaryIdealModel
