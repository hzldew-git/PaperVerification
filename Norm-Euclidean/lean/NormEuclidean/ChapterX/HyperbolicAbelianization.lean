import NormEuclidean.ChapterX.CommutatorSquares
import NormEuclidean.ChapterX.FixedValueTransitivity

/-!
# Hyperbolic reflections and the actual orthogonal abelianization

The explicit hyperbolic correction is multiplicative. Its abelianized
image factors through the actual scalar square-class quotient.
-/

noncomputable section

namespace NormEuclidean.HyperbolicAbelianization

open ProperSpinor SpinorBaseChange CommutatorGeneration CommutatorSquares

variable {F E : Type*} [Field F] [CharZero F] [AddCommGroup E] [Module F E]
  [FiniteDimensional F E] (Q : QuadraticForm F E) (hQ : Q.polarBilin.Nondegenerate)

/-- Canonical anisotropic vectors in the distinguished hyperbolic plane. -/
def vector (a : Fˣ) : Hyperbolic F E := (0, (a : F), 1)

@[simp] theorem value_vector (a : Fˣ) : Hyperbolic.form Q (vector a) = (a : F) := by
  simp [vector, Hyperbolic.q]

/-- Reflection in the distinguished hyperbolic vector, on the whole ambient space. -/
theorem reflection_apply (a : Fˣ) (z : Hyperbolic F E) :
    (ambientReflection (Hyperbolic.form Q) (vector a)
      (by simp [vector, Hyperbolic.q])).1 z =
      (z.1, -(a : F) * z.2.2, -((a : F)⁻¹) * z.2.1) := by
  change IntegralReflection.linearEquiv (Hyperbolic.form Q) (vector a)
    (by simp [vector, Hyperbolic.q]) z = _
  rw [IntegralReflection.linearEquiv_apply]
  apply Prod.ext
  · simp [vector]
  · apply Prod.ext
    · simp [vector, QuadraticMap.polar, Hyperbolic.q]
      field_simp
      ring
    · simp [vector, QuadraticMap.polar, Hyperbolic.q]
      field_simp
      ring

/-- The existing correction is the actual diagonal dilation on the hyperbolic plane. -/
theorem correction_apply (a : Fˣ) (z : Hyperbolic F E) :
    (hyperbolicCorrection Q hQ a).1.1 z =
      (z.1, (a : F) * z.2.1, (a : F)⁻¹ * z.2.2) := by
  change (ambientReflection (Hyperbolic.form Q) (vector a)
    (by simp [vector, Hyperbolic.q])).1
    ((ambientReflection (Hyperbolic.form Q) (vector 1) (by simp [vector, Hyperbolic.q])).1 z) = _
  rw [reflection_apply, reflection_apply]
  simp

/-- Multiplication of actual hyperbolic corrections, with no quotient comparison assumed. -/
def correctionHom : Fˣ →* properGroup (Hyperbolic.form Q) where
  toFun := hyperbolicCorrection Q hQ
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    simpa using correction_apply Q hQ 1 z
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    change (hyperbolicCorrection Q hQ (a * b)).1.1 z =
      (hyperbolicCorrection Q hQ a).1.1 ((hyperbolicCorrection Q hQ b).1.1 z)
    simp only [correction_apply, Units.val_mul, mul_inv_rev]
    congr 1 <;> ring

/-- The canonical scalar map to the actual orthogonal abelianization. -/
def scalarAbelianization : Fˣ →* Abelianization (ambientGroup (Hyperbolic.form Q)) :=
  (Abelianization.of.comp (properGroup (Hyperbolic.form Q)).subtype).comp
    (correctionHom Q hQ)

/-- Squares of scalar units map to the identity, using the square part of 43:6. -/
theorem scalar_square (a : Fˣ) : scalarAbelianization Q hQ (a ^ 2) = 1 := by
  change Abelianization.of ((correctionHom Q hQ (a ^ 2)).1) = 1
  rw [map_pow]
  change Abelianization.of ((hyperbolicCorrection Q hQ a).1 ^ 2) = 1
  rw [map_pow]
  exact abelianization_sq (Hyperbolic.form Q)
    (Hyperbolic.form_polarBilin_nondegenerate Q hQ) _

/-- A proved homomorphism from actual square classes to orthogonal abelianization. -/
def squareClassAbelianization : Bong.Dyadic.SquareClass F →*
    Abelianization (ambientGroup (Hyperbolic.form Q)) :=
  QuotientGroup.lift (Subgroup.square Fˣ) (scalarAbelianization Q hQ) (by
    intro a ha
    change scalarAbelianization Q hQ a = 1
    obtain ⟨b, hb⟩ := ha
    rw [hb]
    simpa only [pow_two] using scalar_square Q hQ b)

@[simp] theorem squareClassAbelianization_apply (a : Fˣ) :
    squareClassAbelianization Q hQ (Bong.Dyadic.squareClass F a) =
      scalarAbelianization Q hQ a := rfl

end NormEuclidean.HyperbolicAbelianization
