import TraceEuclidean.Finiteness
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
Arithmetic finiteness reductions used in Lemma 5.1 of the manuscript.
-/

namespace TraceEuclidean

noncomputable section

/-- A number field represented as an intermediate field of one ambient field. -/
abbrev NumberFieldCode (A : Type*) [Field A] [CharZero A] :=
  {F : IntermediateField ℚ A // FiniteDimensional ℚ F}

noncomputable instance NumberFieldCode.numberField
    {A : Type*} [Field A] [CharZero A] (K : NumberFieldCode A) :
    NumberField K :=
  @NumberField.mk _ _ inferInstance K.prop

/-- The discriminant attached to a number-field code. -/
def NumberFieldCode.discriminant {A : Type*} [Field A] [CharZero A]
    (K : NumberFieldCode A) : ℤ :=
  NumberField.discr K

/-- Hermite's theorem in the exact representation used by mathlib. -/
theorem finite_numberFieldCodes_of_discriminant_le
    (A : Type*) [Field A] [CharZero A] (N : ℕ) :
    {K : NumberFieldCode A | |K.discriminant| ≤ N}.Finite := by
  simpa only [NumberFieldCode.discriminant] using
    (NumberField.finite_of_discr_bdd A N)

/--
Once each field fiber is finite, a discriminant bound makes the full family
of field-dependent objects finite. This is the Hermite step of Lemma 5.1.
-/
theorem finite_objects_of_bounded_field_discriminant
    {A α : Type*} [Field A] [CharZero A]
    (P : α → Prop) (fieldCode : α → NumberFieldCode A) (N : ℕ)
    (hdisc : ∀ a, P a → |(fieldCode a).discriminant| ≤ N)
    (hfiber : ∀ K, {a | P a ∧ fieldCode a = K}.Finite) :
    {a | P a}.Finite := by
  exact finite_of_finite_keys_and_fibers P fieldCode
    {K | |K.discriminant| ≤ N}
    (finite_numberFieldCodes_of_discriminant_le A N) hdisc hfiber

/--
For a fixed number field, bounded absolute norm leaves only finitely many
possible integral volume ideals. Finiteness for each fixed ideal therefore
implies finiteness of the whole lattice family. This is the ideal-enumeration
step of Lemma 5.1; the fixed-ideal hypothesis is precisely where the cited
O'Meara results enter.
-/
theorem finite_objects_of_bounded_volumeIdeal
    {F α : Type*} [Field F] [NumberField F]
    (P : α → Prop)
    (volumeIdeal : α → Ideal (NumberField.RingOfIntegers F)) (N : ℕ)
    (hvolume : ∀ a, P a → Ideal.absNorm (volumeIdeal a) ≤ N)
    (hfixedIdeal : ∀ I, {a | P a ∧ volumeIdeal a = I}.Finite) :
    {a | P a}.Finite := by
  exact finite_of_finite_keys_and_fibers P volumeIdeal
    {I | Ideal.absNorm I ≤ N}
    (Ideal.finite_setOf_absNorm_le N) hvolume hfixedIdeal

/-- The objects whose selected field code is `K`. -/
abbrev FieldFiber {A α : Type*} [Field A] [CharZero A]
    (fieldCode : α → NumberFieldCode A) (K : NumberFieldCode A) :=
  {a : α // fieldCode a = K}

/--
The complete arithmetic assembly in Lemma 5.1: Hermite reduces to finitely
many fields, bounded ideal norm reduces each field to finitely many volume
ideals, and the cited fixed-field fixed-volume theorem handles each fiber.
-/
theorem bounded_discriminant_volume_finiteness
    {A α : Type*} [Field A] [CharZero A]
    (P : α → Prop) (fieldCode : α → NumberFieldCode A)
    (discriminantBound volumeBound : ℕ)
    (volumeIdeal : ∀ K, FieldFiber fieldCode K →
      Ideal (NumberField.RingOfIntegers K))
    (hdisc : ∀ a, P a → |(fieldCode a).discriminant| ≤ discriminantBound)
    (hvolume : ∀ K (a : FieldFiber fieldCode K), P a.1 →
      Ideal.absNorm (volumeIdeal K a) ≤ volumeBound)
    (hfixed : ∀ K I,
      {a : FieldFiber fieldCode K | P a.1 ∧ volumeIdeal K a = I}.Finite) :
    {a | P a}.Finite := by
  apply finite_objects_of_bounded_field_discriminant P fieldCode
    discriminantBound hdisc
  intro K
  let PK : FieldFiber fieldCode K → Prop := fun a ↦ P a.1
  have hfinite : {a : FieldFiber fieldCode K | PK a}.Finite :=
    finite_objects_of_bounded_volumeIdeal PK (volumeIdeal K) volumeBound
      (hvolume K) (hfixed K)
  refine (hfinite.image Subtype.val).subset ?_
  intro a ha
  exact ⟨⟨a, ha.2⟩, ha.1, rfl⟩

end

end TraceEuclidean
