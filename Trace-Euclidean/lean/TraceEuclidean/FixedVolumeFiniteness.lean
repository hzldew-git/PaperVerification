import TraceEuclidean.ArithmeticFiniteness
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# A finite-code reduction for the fixed-volume finiteness step

This file develops the elementary finite-code infrastructure used by the
direct fixed-field proof.  It does not assume O'Meara's fixed-volume theorem.

For a fixed number field, the ring of integers in a bounded archimedean box is finite.  It follows
that there are only finitely many bounded Gram matrices and bounded matrices describing the action
of a fixed integral basis of the ground field.  Consequently, any family of lattice classes that
admits an injective bounded arithmetic Gram code is finite.

`DirectFixedFieldFiniteness` supplies the application-specific reduction:
short field bases produce bounded integral Gram/module codes, and equality of
codes reconstructs the lattice equivalence class.
-/

namespace TraceEuclidean

open scoped NumberField

noncomputable section

/-- An algebraic integer whose image under every complex embedding has norm at most `B`. -/
def ConjugateBounded {K : Type*} [Field K] [NumberField K]
    (B : ℝ) (x : 𝓞 K) : Prop :=
  ∀ φ : K →+* ℂ, ‖φ (x : K)‖ ≤ B

/-- For a fixed number field, only finitely many algebraic integers have all conjugates bounded. -/
theorem finite_ringOfIntegers_of_conjugateBounded
    (K : Type*) [Field K] [NumberField K] (B : ℝ) :
    {x : 𝓞 K | ConjugateBounded B x}.Finite := by
  let f : 𝓞 K → K := fun x ↦ (x : K)
  let s : Set K :=
    {x | _root_.IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ B}
  apply Set.Finite.of_injOn (f := f) (t := s)
  · intro x hx
    exact ⟨x.2, hx⟩
  · exact NumberField.RingOfIntegers.coe_injective.injOn
  · exact NumberField.Embeddings.finite_of_norm_le K ℂ B

/-- Entrywise archimedean boundedness for a matrix over the ring of integers. -/
def Matrix.ConjugateBounded {K : Type*} [Field K] [NumberField K]
    {ι κ : Type*} (B : ℝ) (M : Matrix ι κ (𝓞 K)) : Prop :=
  ∀ i j, TraceEuclidean.ConjugateBounded B (M i j)

/-- Matrices of fixed finite size with archimedean-bounded integral entries form a finite set. -/
theorem finite_matrices_of_conjugateBounded
    (K : Type*) [Field K] [NumberField K]
    (ι κ : Type*) [Finite ι] [Finite κ] (B : ℝ) :
    {M : Matrix ι κ (𝓞 K) | Matrix.ConjugateBounded B M}.Finite := by
  change {M : ι → κ → 𝓞 K |
    ∀ i j, ConjugateBounded B (M i j)}.Finite
  exact Set.Finite.pi' fun _ ↦ Set.Finite.pi' fun _ ↦
    finite_ringOfIntegers_of_conjugateBounded K B

/-- Entrywise boundedness for an integer matrix. -/
def Matrix.IntEntryBounded {ι κ : Type*} (B : ℤ) (M : Matrix ι κ ℤ) : Prop :=
  ∀ i j, M i j ∈ Set.Icc (-B) B

/-- Integer matrices of fixed finite size with a fixed entry bound form a finite set. -/
theorem finite_integerMatrices_of_entryBounded
    (ι κ : Type*) [Finite ι] [Finite κ] (B : ℤ) :
    {M : Matrix ι κ ℤ | Matrix.IntEntryBounded B M}.Finite := by
  change {M : ι → κ → ℤ | ∀ i j, M i j ∈ Set.Icc (-B) B}.Finite
  exact Set.Finite.pi' fun _ ↦ Set.Finite.pi' fun _ ↦ Set.finite_Icc (-B) B

/-
The finite arithmetic data attached to a lattice with a chosen `ℤ`-basis: its field-valued Gram
matrix and the integer matrices for the action of a fixed integral basis of the ground field.
-/
abbrev ArithmeticGramCode (K : Type*) [Field K] [NumberField K]
    (ι κ : Type*) :=
  Matrix κ κ (𝓞 K) × (ι → Matrix κ κ ℤ)

/-- Both parts of an arithmetic Gram code satisfy fixed archimedean entry bounds. -/
def ArithmeticGramCode.IsBounded
    {K : Type*} [Field K] [NumberField K] {ι κ : Type*}
    (gramBound : ℝ) (actionBound : ℤ) (c : ArithmeticGramCode K ι κ) : Prop :=
  Matrix.ConjugateBounded gramBound c.1 ∧
    ∀ i, Matrix.IntEntryBounded actionBound (c.2 i)

/-- There are only finitely many arithmetic Gram codes with fixed entry bounds. -/
theorem finite_boundedArithmeticGramCodes
    (K : Type*) [Field K] [NumberField K]
    (ι κ : Type*) [Finite ι] [Finite κ]
    (gramBound : ℝ) (actionBound : ℤ) :
    {c : ArithmeticGramCode K ι κ |
      ArithmeticGramCode.IsBounded gramBound actionBound c}.Finite := by
  have hgram :
      {G : Matrix κ κ (𝓞 K) |
        Matrix.ConjugateBounded gramBound G}.Finite :=
    finite_matrices_of_conjugateBounded K κ κ gramBound
  have haction :
      {A : ι → Matrix κ κ ℤ |
        ∀ i, Matrix.IntEntryBounded actionBound (A i)}.Finite := by
    simpa only [Set.mem_setOf_eq] using
      Set.Finite.pi' fun _ ↦ finite_integerMatrices_of_entryBounded κ κ actionBound
  exact (hgram.prod haction).subset fun c hc ↦ hc

/--
A bounded complete arithmetic Gram code proves finiteness.  In an application to quadratic
lattices, `encode` records a reduced Gram matrix together with the action matrices of an integral
basis of the fixed field.  `hcomplete` is the statement that this based data determines the
lattice class.
-/
theorem finite_of_bounded_complete_arithmeticGramCode
    {K : Type*} [Field K] [NumberField K]
    {ι κ α : Type*} [Finite ι] [Finite κ]
    (P : α → Prop) (encode : α → ArithmeticGramCode K ι κ)
    (gramBound : ℝ) (actionBound : ℤ)
    (hbounded : ∀ a, P a →
      ArithmeticGramCode.IsBounded gramBound actionBound (encode a))
    (hcomplete : Set.InjOn encode {a | P a}) :
    {a | P a}.Finite := by
  apply Set.Finite.of_injOn
    (t := {c : ArithmeticGramCode K ι κ |
      ArithmeticGramCode.IsBounded gramBound actionBound c})
  · intro a ha
    exact hbounded a ha
  · exact hcomplete
  · exact finite_boundedArithmeticGramCodes K ι κ gramBound actionBound

/-
Surjective coding is often the convenient reduction-theory interface.  It is enough that every
class in the target family can be reconstructed from some bounded code; the chosen code need not
be canonical.
-/
theorem finite_of_bounded_surjective_arithmeticGramCode
    {K : Type*} [Field K] [NumberField K]
    {ι κ α : Type*} [Finite ι] [Finite κ]
    (P : α → Prop) (decode : ArithmeticGramCode K ι κ → α)
    (gramBound : ℝ) (actionBound : ℤ)
    (hcovered : ∀ a, P a → ∃ c,
      ArithmeticGramCode.IsBounded gramBound actionBound c ∧ decode c = a) :
    {a | P a}.Finite := by
  apply (finite_boundedArithmeticGramCodes K ι κ gramBound actionBound).image decode |>.subset
  intro a ha
  obtain ⟨c, hc, rfl⟩ := hcovered a ha
  exact ⟨c, hc, rfl⟩

end

end TraceEuclidean
