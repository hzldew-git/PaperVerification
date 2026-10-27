import NormEuclidean.BinaryNormForm
import NormEuclidean.ChapterX.ProperReflectionGeneration

/-!
# Proper binary spinor norms and quadratic norms

The actual Wall spinor image equals the quadratic norm group modulo squares.
The proof uses actual reflection pairs and the proved Cartan--Dieudonne
generation theorem. No local Hilbert-symbol law is assumed.
-/

noncomputable section

namespace NormEuclidean.BinarySpinorNorm

open Bong.Dyadic BinaryNormForm ProperSpinor SpinorBaseChange

variable {K : Type*} [Field K]

/-- The image of the quadratic norm group in the actual square-class quotient. -/
def normSquareClasses (theta : Kˣ) : Subgroup (SquareClass K) :=
  (quadraticNormGroup K theta).map (QuotientGroup.mk' (Subgroup.square Kˣ))

/-- Membership is independent of the chosen scalar representative. -/
theorem isNorm_of_squareClass_eq {theta a b : Kˣ}
    (hb : IsQuadraticNorm K theta b) (h : squareClass K a = squareClass K b) :
    IsQuadraticNorm K theta a := by
  have hs : IsSquare (a / b) := QuotientGroup.eq_iff_div_mem.mp h
  have hnorm := (isQuadraticNorm_of_isSquare_right K (a := theta) hs).mul K hb
  simpa only [div_mul_cancel] using hnorm

/-- The preimage of the norm square classes is exactly the scalar norm group. -/
theorem squareClass_mem_normSquareClasses_iff (theta a : Kˣ) :
    squareClass K a ∈ normSquareClasses theta ↔ IsQuadraticNorm K theta a := by
  constructor
  · rintro ⟨b, hb, heq⟩
    exact isNorm_of_squareClass_eq hb heq.symm
  · intro ha
    exact ⟨a, ha, rfl⟩

variable {V : Type*} [CharZero K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Invertible (2 : K)]
  {Q : QuadraticForm K V} {theta : Kˣ}

/-- The proper Wall spinor norm of every actual binary transformation is a norm class. -/
theorem proper_norm_mem (f : Frame Q theta) (hQ : Q.polarBilin.Nondegenerate)
    (g : properGroup Q) :
    properAmbientSpinorNormHom Q hQ g ∈ normSquareClasses theta := by
  let P := (normSquareClasses theta).comap (properAmbientSpinorNormHom Q hQ)
  have hP : ∀ (x : V) (hx : Q x ≠ 0) (y : V) (hy : Q y ≠ 0),
      doubleReflection Q hQ x hx y hy ∈ P := by
    intro x hx y hy
    change properAmbientSpinorNormHom Q hQ (doubleReflection Q hQ x hx y hy) ∈
      normSquareClasses theta
    rw [doubleReflection_spinorNorm, squareClass_mem_normSquareClasses_iff]
    exact f.value_product_isNorm x hx y hy
  exact ProperReflectionGeneration.proper_mem_of_contains_doubleReflections Q hQ P hP g

/-- Every scalar representative of a proper binary spinor norm is itself a norm. -/
theorem representative_isNorm (f : Frame Q theta) (hQ : Q.polarBilin.Nondegenerate)
    (g : properGroup Q) (a : Kˣ)
    (ha : squareClass K a = properAmbientSpinorNormHom Q hQ g) :
    IsQuadraticNorm K theta a := by
  apply (squareClass_mem_normSquareClasses_iff theta a).mp
  rw [ha]
  exact proper_norm_mem f hQ g

/-- Conversely a scalar norm is the spinor norm of an explicit pair of reflections. -/
theorem exists_proper_of_isNorm (f : Frame Q theta) (hQ : Q.polarBilin.Nondegenerate)
    (a : Kˣ) (ha : IsQuadraticNorm K theta a) :
    ∃ g : properGroup Q, properAmbientSpinorNormHom Q hQ g = squareClass K a := by
  obtain ⟨x, hx, hprod⟩ := f.norm_is_value_product a ha
  refine ⟨doubleReflection Q hQ x hx (f.basis 0) f.first_ne_zero, ?_⟩
  rw [doubleReflection_spinorNorm, hprod]

/-- Equality of actual subgroups, over arbitrary characteristic-zero fields. -/
theorem proper_spinor_range_eq (f : Frame Q theta) (hQ : Q.polarBilin.Nondegenerate) :
    (properAmbientSpinorNormHom Q hQ).range = normSquareClasses theta := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact proper_norm_mem f hQ g
  · rintro s ⟨a, ha, rfl⟩
    exact exists_proper_of_isNorm f hQ a ha

end NormEuclidean.BinarySpinorNorm
