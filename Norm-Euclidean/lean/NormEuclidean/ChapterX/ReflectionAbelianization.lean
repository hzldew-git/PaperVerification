import NormEuclidean.ChapterX.CommutatorSquares
import NormEuclidean.ChapterX.GenusPatching

/-! # Equal-value reflections in actual orthogonal abelianization -/

noncomputable section

namespace NormEuclidean.ReflectionAbelianization

open ProperSpinor SpinorBaseChange ReflectionApproximation

variable {F E : Type*} [Field F] [CharZero F] [AddCommGroup E] [Module F E]

/-- Conjugate reflections have the same class in the actual orthogonal abelianization. -/
theorem class_of_equal_value (P : QuadraticForm F E) (x y : E)
    (hx : P x ≠ 0) (hy : P y ≠ 0) (hxy : P x = P y) :
    Abelianization.of (ambientReflection P x hx) =
      Abelianization.of (ambientReflection P y hy) := by
  obtain ⟨g, he⟩ := GenusPatching.exists_ambient_map_of_value_eq P x y hx hxy
  have hc := ambientReflection_conjugate P g x hx
  have hsub : (⟨g.1 x, (g.2 x).trans_ne hx⟩ : {z // P z ≠ 0}) = ⟨y, hy⟩ :=
    Subtype.ext he
  have hr : ambientReflection P (g.1 x) ((g.2 x).trans_ne hx) = ambientReflection P y hy :=
    congrArg (fun z : {z // P z ≠ 0} ↦ ambientReflection P z.1 z.2) hsub
  have hh : Abelianization.of (g * ambientReflection P x hx * g⁻¹) =
      Abelianization.of (ambientReflection P y hy) := congrArg Abelianization.of (hc.trans hr)
  simpa [mul_comm, mul_left_comm, mul_assoc] using hh

end NormEuclidean.ReflectionAbelianization
