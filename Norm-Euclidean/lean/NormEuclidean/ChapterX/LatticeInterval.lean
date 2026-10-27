import NormEuclidean.LatticeCommensurability
import NormEuclidean.NumberFieldNorm
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Ideal.Quotient.Index

/-!
# Finite lattice intervals in O'Meara 103:4

The finite-interval step of the proof is proved for finitely generated
modules over rings with finite quotients. Commensurability supplies the
annihilating scalar for actual number-field lattices, without freeness.
The global bounded-representative argument of 103:4 remains separate.
-/

noncomputable section

namespace NormEuclidean.LatticeInterval

section Modules

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A scalar carrying the upper module into the lower module makes their
quotient finite when the scalar ideal has finite quotient. -/
theorem finite_quotient_of_scalar_bound (L U : Submodule R M) (hU : U.FG)
    (a : R) [Finite (R ⧸ Ideal.span {a})] (ha : ∀ x ∈ U, a • x ∈ L) :
    Finite (U ⧸ L.comap U.subtype) := by
  let N := L.comap U.subtype
  let I : Ideal R := Ideal.span {a}
  letI : Module.Finite R U := Module.Finite.of_fg hU
  have hIN : I • (⊤ : Submodule R U) ≤ N := by
    apply Submodule.smul_le.mpr
    intro r hr x _
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    change (b * a) • (x : M) ∈ L
    rw [mul_smul]
    exact L.smul_mem b (ha x x.2)
  letI : Finite (U ⧸ I • (⊤ : Submodule R U)) :=
    Submodule.finite_quotient_smul I (Module.Finite.fg_top : (⊤ : Submodule R U).FG)
  exact Finite.of_surjective (Submodule.factor hIN) (Submodule.factor_surjective hIN)

/-- The finite interval used in O'Meara 103:4, step 2. -/
theorem finite_interval_of_scalar_bound (L U : Submodule R M) (hU : U.FG)
    (a : R) [Finite (R ⧸ Ideal.span {a})] (ha : ∀ x ∈ U, a • x ∈ L) :
    {P : Submodule R M | L ≤ P ∧ P ≤ U}.Finite := by
  let N := L.comap U.subtype
  letI := finite_quotient_of_scalar_bound L U hU a ha
  letI : Finite (Submodule R (U ⧸ N)) :=
    Finite.of_injective (fun P : Submodule R (U ⧸ N) ↦ (P : Set (U ⧸ N)))
      SetLike.coe_injective
  letI : Finite (Set.Ici N) :=
    Finite.of_equiv (Submodule R (U ⧸ N)) (Submodule.comapMkQRelIso N).toEquiv
  let f : {P : Submodule R M // L ≤ P ∧ P ≤ U} → Set.Ici N :=
    fun P ↦ ⟨P.1.comap U.subtype, Submodule.comap_mono P.2.1⟩
  apply Finite.of_injective f
  intro P P' h
  have heq : P.1.comap U.subtype = P'.1.comap U.subtype := congrArg Subtype.val h
  apply Subtype.ext
  apply le_antisymm
  · intro x hx
    have hxu : x ∈ U := P.2.2 hx
    have hx' : (⟨x, hxu⟩ : U) ∈ P.1.comap U.subtype := hx
    rw [heq] at hx'
    exact hx'
  · intro x hx
    have hxu : x ∈ U := P'.2.2 hx
    have hx' : (⟨x, hxu⟩ : U) ∈ P'.1.comap U.subtype := hx
    rw [← heq] at hx'
    exact hx'

end Modules

section Lattices

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (R : Subring K) [IsFractionRing R K] [Ring.HasFiniteQuotients R]

/-- Two commensurable finite full modules bound only finitely many
intermediate integral submodules. No integral basis is required. -/
theorem finite_interval_of_full (L U : Submodule R V)
    (hL : Submodule.span K (L : Set V) = ⊤) (hU : U.FG) :
    {P : Submodule R V | L ≤ P ∧ P ≤ U}.Finite := by
  obtain ⟨a, ha0, ha⟩ := exists_lattice_denominator U L hU hL
  letI : Finite (R ⧸ Ideal.span {a}) :=
    Ring.HasFiniteQuotients.finiteQuotient (by simpa using ha0)
  exact finite_interval_of_scalar_bound L U hU a ha

end Lattices

section NumberField

variable {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

/-- The interval-finiteness assertion for actual lattices on a number-field
space, as required for the fixed-space induction in O'Meara 103:4. -/
theorem finite_numberField_lattice_interval (L U : Lattice (integerSubring K) Q) :
    {P : Submodule (integerSubring K) V | L.carrier ≤ P ∧ P ≤ U.carrier}.Finite := by
  letI : Ring.HasFiniteQuotients (integerSubring K) :=
    inferInstanceAs (Ring.HasFiniteQuotients (NumberField.RingOfIntegers K))
  exact finite_interval_of_full (integerSubring K) L.carrier U.carrier L.full U.finite

end NumberField

end NormEuclidean.LatticeInterval
