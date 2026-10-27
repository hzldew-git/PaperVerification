import NormEuclidean.Unary
import NormEuclidean.NormBound
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
Supplementary result retained from reference manuscript. The free-unary finiteness proposition
is absent from reference manuscript; this module is not counted as a current-paper theorem.

# Finiteness of scalar unary integral isometry classes over a fixed field

The coefficient relation is proved equivalent to an actual linear isometry
of the underlying rank-one integral modules. Dirichlet's unit theorem supplies
finiteness of units modulo squares; it is not an additional hypothesis.
The final finiteness result concerns scalar unary forms over a fixed number
field, and makes no global assertion about varying number fields.
-/

namespace NormEuclidean

section IntegralUnary

variable (R : Type*) [CommRing R]

/-- Integral changes of coordinates for scalar unary forms. -/
def IntegralUnaryIsometric (a b : R) : Prop :=
  ∃ e : R ≃ₗ[R] R, ∀ x : R, a * (e x) ^ 2 = b * x ^ 2

/-- Two unary coefficients represent the same class if they differ by a
square of an integral unit. -/
def unaryCoefficientSetoid : Setoid R where
  r a b := ∃ u : Rˣ, a * (u : R) ^ 2 = b
  iseqv := {
    refl := fun a => ⟨1, by simp⟩
    symm := by
      rintro a b ⟨u, rfl⟩
      refine ⟨u⁻¹, ?_⟩
      rw [mul_assoc, ← mul_pow]
      simp
    trans := by
      rintro a b c ⟨u, rfl⟩ ⟨v, rfl⟩
      exact ⟨u * v, by simp [mul_pow, mul_assoc]⟩ }

/-- Scalar unary integral isometry classes, including the zero form. -/
abbrev UnaryIntegralClass := Quotient (unaryCoefficientSetoid R)

/-- The coefficient description is exactly integral module isometry. -/
theorem integralUnaryIsometric_iff (a b : R) :
    IntegralUnaryIsometric R a b ↔ (unaryCoefficientSetoid R).r a b := by
  constructor
  · rintro ⟨e, he⟩
    have hmul (x : R) : e x = x * e 1 := by
      simpa only [smul_eq_mul, mul_one] using e.map_smul x (1 : R)
    have hinv : e.symm 1 * e 1 = 1 := by
      rw [← hmul, e.apply_symm_apply]
    let u : Rˣ := ⟨e 1, e.symm 1, by rwa [mul_comm], hinv⟩
    exact ⟨u, by simpa [u] using he 1⟩
  · rintro ⟨u, rfl⟩
    let e : R ≃ₗ[R] R := {
      toFun := fun x => (u : R) * x
      invFun := fun x => (↑u⁻¹ : R) * x
      left_inv := by intro x; simp [← mul_assoc]
      right_inv := by intro x; simp [← mul_assoc]
      map_add' := by intro x y; exact mul_add _ _ _
      map_smul' := by intro r x; simp only [smul_eq_mul, RingHom.id_apply]; ring }
    refine ⟨e, ?_⟩
    intro x
    change a * ((u : R) * x) ^ 2 = _
    ring

/-- Equality in the class space has its literal module-isometry meaning. -/
theorem unaryIntegralClass_eq_iff (a b : R) :
    (Quotient.mk (unaryCoefficientSetoid R) a = Quotient.mk _ b) ↔
      IntegralUnaryIsometric R a b := by
  rw [Quotient.eq, integralUnaryIsometric_iff]

end IntegralUnary

open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

omit [NumberField K] in
/-- The coefficient quotient also classifies isometries of the actual integral
modules inside `K`, with the field-valued scalar quadratic forms. -/
theorem unaryIntegralClass_eq_iff_latticeIsometry (a b : 𝓞 K) :
    (Quotient.mk (unaryCoefficientSetoid (𝓞 K)) a = Quotient.mk _ b) ↔
      ∃ e : integerModule K ≃ₗ[integerSubring K] integerModule K,
        ∀ x : integerModule K,
          unaryForm K a (e x : K) = unaryForm K b (x : K) := by
  rw [unaryIntegralClass_eq_iff]
  constructor
  · rintro ⟨e, he⟩
    let e' : integerSubring K ≃ₗ[integerSubring K] integerSubring K := e
    let f := (integerModuleEquiv K).symm.trans (e'.trans (integerModuleEquiv K))
    refine ⟨f, ?_⟩
    intro x
    rw [unaryForm_apply, unaryForm_apply]
    exact congrArg (fun t : 𝓞 K => (t : K)) (he ((integerModuleEquiv K).symm x))
  · rintro ⟨e, he⟩
    let f' : integerSubring K ≃ₗ[integerSubring K] integerSubring K :=
      (integerModuleEquiv K).trans (e.trans (integerModuleEquiv K).symm)
    let f : 𝓞 K ≃ₗ[𝓞 K] 𝓞 K := f'
    refine ⟨f, ?_⟩
    intro x
    apply Subtype.ext
    exact (unaryForm_apply K a _).symm.trans
      ((he (integerModuleEquiv K x)).trans (unaryForm_apply K b _))

section UnaryModels

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- An arbitrary anisotropic integral lattice with rank-one coordinates has
an actual scalar unary model. The integral module isometry is exhibited, and
the norm-Euclidean approximation property is transported in both directions. -/
theorem exists_unary_model_of_equiv
    (Q : QuadraticForm K V) (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic)
    (e : integerSubring K ≃ₗ[integerSubring K] L.carrier) :
    ∃ a : 𝓞 K, a ≠ 0 ∧
      ∃ f : integerModule K ≃ₗ[integerSubring K] L.carrier,
        (∀ x : integerModule K, Q (f x : V) = unaryForm K a (x : K)) ∧
        (HasNumberFieldApproximation Q L.carrier ↔
          HasNumberFieldApproximation (unaryForm K a) (integerModule K)) := by
  let f := (integerModuleEquiv K).symm.trans e
  let g := ScalarExtension.ambientEquiv (integerModule K) L.carrier
    (integerModule_full K) L.full f
  have hg (x : integerModule K) : g (x : K) = (f x : V) :=
    ScalarExtension.ambientEquiv_apply _ _ _ _ _ x
  have hg1 : g 1 = (e 1 : V) := hg ⟨1, (integerSubring K).one_mem⟩
  have ha : Q (g 1) ∈ integerSubring K := by
    rw [hg1]
    exact L.integral _ (e 1).property
  let a : 𝓞 K := ⟨Q (g 1), ha⟩
  have ha0 : a ≠ 0 := by
    intro h
    have hQ : Q (g 1) = 0 := congrArg (fun t : 𝓞 K => (t : K)) h
    have hz := hA _ hQ
    exact one_ne_zero (g.injective (hz.trans g.map_zero.symm))
  have hform (t : K) : Q (g t) = unaryForm K a t := by
    have hgt : g t = t • g 1 := by rw [← g.map_smul]; simp
    rw [hgt, Q.map_smul, unaryForm_apply]
    simp only [smul_eq_mul]
    dsimp [a]
    ring
  refine ⟨a, ha0, f, ?_, ?_⟩
  · intro x
    rw [← hg, hform]
  · constructor
    · intro hE x
      obtain ⟨u, hu, happ⟩ := hE (g x)
      let y : integerModule K := f.symm ⟨u, hu⟩
      have hgy : g (y : K) = u := (hg y).trans (by simp [y])
      refine ⟨y, y.property, ?_⟩
      rw [← hgy] at happ
      have hsub : g x - g (y : K) = g (x - y) := (map_sub g x (y : K)).symm
      rw [hsub, hform] at happ
      exact happ
    · intro hE v
      obtain ⟨x, hx, happ⟩ := hE (g.symm v)
      refine ⟨f ⟨x, hx⟩, (f ⟨x, hx⟩).property, ?_⟩
      have hsub : v - (f ⟨x, hx⟩ : V) = g (g.symm v - x) := by
        rw [map_sub, g.apply_symm_apply, hg ⟨x, hx⟩]
      rw [hsub, hform]
      exact happ

/-- The normal form applies under literal freeness and rank one, with no
chosen coordinates required in the statement. -/
theorem exists_freeUnary_model
    (Q : QuadraticForm K V) (L : Lattice (integerSubring K) Q)
    [Module.Free (integerSubring K) L.carrier]
    (hrank : Module.finrank (integerSubring K) L.carrier = 1)
    (hA : Q.Anisotropic) :
    ∃ a : 𝓞 K, a ≠ 0 ∧
      ∃ f : integerModule K ≃ₗ[integerSubring K] L.carrier,
        (∀ x : integerModule K, Q (f x : V) = unaryForm K a (x : K)) ∧
        (HasNumberFieldApproximation Q L.carrier ↔
          HasNumberFieldApproximation (unaryForm K a) (integerModule K)) := by
  letI : Module.Finite (integerSubring K) L.carrier := Module.Finite.iff_fg.mpr L.finite
  let b := (Module.finBasis (integerSubring K) L.carrier).reindex (finCongr hrank)
  let e := b.equivFun.trans (LinearEquiv.funUnique (Fin 1) (integerSubring K) _)
  exact exists_unary_model_of_equiv K Q L hA e.symm

end UnaryModels

/-- The subgroup of squares of algebraic-integer units. -/
def unitSquares : Subgroup (𝓞 K)ˣ := (powMonoidHom 2).range

/-- Dirichlet's theorem implies that the unit-square quotient is finite. -/
instance finite_unitSquareQuotient : Finite ((𝓞 K)ˣ ⧸ unitSquares K) := by
  letI : Group.FG (𝓞 K)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance
  apply CommGroup.finite_of_fg_torsion
  intro x
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, ?_⟩
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (unitSquares K) x
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact ⟨u, rfl⟩

omit [NumberField K] in
/-- The norm ideal of the scalar unary lattice is the principal coefficient ideal. -/
theorem unaryLattice_normIdeal (a : 𝓞 K) :
    (unaryLattice K a a.property).normIdeal = Ideal.span {a} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨x, rfl⟩
    change (unaryLattice K a a.property).normValue x ∈ Ideal.span {a}
    rw [Ideal.mem_span_singleton]
    refine ⟨(⟨(x : K), x.property⟩ : 𝓞 K) ^ 2, ?_⟩
    apply Subtype.ext
    simp only [Lattice.normValue, unaryForm_apply]
    rfl
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    have h := (unaryLattice K a a.property).normValue_mem_normIdeal
      ⟨1, (integerSubring K).one_mem⟩
    convert h using 1
    apply Subtype.ext
    simp only [Lattice.normValue, unaryForm_apply, one_pow, mul_one]
    rfl

omit [NumberField K] in
/-- Units in the same square class give isometric multiples of any unary form. -/
theorem unaryClass_mul_unit_eq (a : 𝓞 K) {u v : (𝓞 K)ˣ}
    (h : QuotientGroup.mk' (unitSquares K) u = QuotientGroup.mk' (unitSquares K) v) :
    Quotient.mk (unaryCoefficientSetoid (𝓞 K)) (a * (u : 𝓞 K)) =
      Quotient.mk _ (a * (v : 𝓞 K)) := by
  obtain ⟨w, hw, huw⟩ := (QuotientGroup.mk'_eq_mk' (unitSquares K)).mp h
  obtain ⟨z, rfl⟩ := hw
  apply Quotient.sound
  refine ⟨z, ?_⟩
  simpa [mul_assoc] using congrArg (fun t : (𝓞 K)ˣ => a * (t : 𝓞 K)) huw

/-- A coefficient's unit multiples have only finitely many integral unary
isometry classes. -/
theorem finite_unit_mul_unaryClasses (a : 𝓞 K) :
    (Set.range fun u : (𝓞 K)ˣ =>
      Quotient.mk (unaryCoefficientSetoid (𝓞 K)) (a * (u : 𝓞 K))).Finite := by
  classical
  let f : ((𝓞 K)ˣ ⧸ unitSquares K) → UnaryIntegralClass (𝓞 K) :=
    fun q => Quotient.mk _ (a * (q.out : 𝓞 K))
  apply (Set.finite_range f).subset
  rintro c ⟨u, rfl⟩
  refine ⟨QuotientGroup.mk' (unitSquares K) u, ?_⟩
  apply unaryClass_mul_unit_eq
  exact Quotient.out_eq _

/-- All generators of a single principal ideal yield finitely many unary classes. -/
theorem finite_unaryClasses_with_ideal (I : Ideal (𝓞 K)) :
    {c : UnaryIntegralClass (𝓞 K) | ∃ a : 𝓞 K,
      Ideal.span {a} = I ∧ Quotient.mk _ a = c}.Finite := by
  classical
  by_cases h : ∃ a : 𝓞 K, Ideal.span {a} = I
  · obtain ⟨a, ha⟩ := h
    apply (finite_unit_mul_unaryClasses K a).subset
    rintro c ⟨b, hb, rfl⟩
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp (ha.trans hb.symm)
    exact ⟨u, congrArg (Quotient.mk (unaryCoefficientSetoid (𝓞 K))) hu⟩
  · have he : {c : UnaryIntegralClass (𝓞 K) | ∃ a : 𝓞 K,
        Ideal.span {a} = I ∧ Quotient.mk _ a = c} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro c ⟨a, ha, _⟩
      exact h ⟨a, ha⟩
    rw [he]
    exact Set.finite_empty

/-- Bounded principal norm gives finitely many actual integral unary isometry
classes over the fixed number field. Zero coefficients cause no exception. -/
theorem finite_bounded_unaryClasses (B : ℕ) :
    {c : UnaryIntegralClass (𝓞 K) | ∃ a : 𝓞 K,
      Ideal.absNorm (Ideal.span {a}) < B ∧ Quotient.mk _ a = c}.Finite := by
  have hI : {I : Ideal (𝓞 K) | Ideal.absNorm I < B}.Finite :=
    (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) B).subset fun _ h => Nat.le_of_lt h
  have h := hI.biUnion fun I _ => finite_unaryClasses_with_ideal K I
  apply h.subset
  rintro c ⟨a, ha, rfl⟩
  exact Set.mem_iUnion_of_mem (Ideal.span {a})
    (Set.mem_iUnion_of_mem ha ⟨a, rfl, rfl⟩)

/-- The fixed-field finiteness step in the unary proposition: nonzero integral
norm-Euclidean scalar unary forms have finitely many integral module-isometry
classes. Equality in this class space is `IntegralUnaryIsometric`, as proved
in `unaryIntegralClass_eq_iff`. -/
theorem finite_normEuclidean_unaryClasses :
    {c : UnaryIntegralClass (𝓞 K) | ∃ a : 𝓞 K, a ≠ 0 ∧
      HasNumberFieldApproximation (unaryForm K a) (integerModule K) ∧
      Quotient.mk _ a = c}.Finite := by
  apply (finite_bounded_unaryClasses K (4 ^ Module.finrank ℚ K)).subset
  rintro c ⟨a, ha, hE, rfl⟩
  refine ⟨a, ?_, rfl⟩
  rw [← unaryLattice_normIdeal K a]
  apply normIdeal_absNorm_lt (unaryForm K a) (unaryLattice K a a.property)
  · exact unaryForm_anisotropic K (by exact_mod_cast ha)
  · exact hE

end NormEuclidean
