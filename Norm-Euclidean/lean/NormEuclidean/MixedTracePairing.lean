import NormEuclidean.IdealThetaNormalization
import Mathlib.LinearAlgebra.BilinearForm.DualLattice

/-!
# The actual archimedean trace pairing

The bilinear form is the real trace of multiplication in the actual
mixed space. Complex places contribute twice the real part. Conjugation
turns this form into the positive Euclidean form already used by theta.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.MixedTracePairing

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module
open InfiniteTraceProduct ComplexConjugate
open scoped NumberField Classical

variable (F : Type*) [Field F] [NumberField F]

/-- The actual trace pairing in real and complex coordinates. -/
def form : LinearMap.BilinForm ℝ (mixedSpace F) where
  toFun x :=
    { toFun := fun y ↦ (∑ w : RealPlace F, x.1 w * y.1 w) +
        ∑ w : ComplexPlace F, 2 * (x.2 w * y.2 w).re
      map_add' y z := by simp [mul_add, Finset.sum_add_distrib]; ring
      map_smul' t y := by
        change (∑ w, x.1 w * (t * y.1 w)) +
          (∑ w, 2 * (x.2 w * (t • y.2 w)).re) =
          t * ((∑ w, x.1 w * y.1 w) + ∑ w, 2 * (x.2 w * y.2 w).re)
        rw [mul_add, Finset.mul_sum, Finset.mul_sum]
        congr 1
        · apply Finset.sum_congr rfl
          intro w _
          ring
        · apply Finset.sum_congr rfl
          intro w _
          simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im,
            Complex.ofReal_re, Complex.ofReal_im]
          ring }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    change (∑ w, (x.1 w + y.1 w) * z.1 w) +
      (∑ w, 2 * ((x.2 w + y.2 w) * z.2 w).re) =
      ((∑ w, x.1 w * z.1 w) + ∑ w, 2 * (x.2 w * z.2 w).re) +
        ((∑ w, y.1 w * z.1 w) + ∑ w, 2 * (y.2 w * z.2 w).re)
    simp only [add_mul, Complex.add_re, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' t x := by
    apply LinearMap.ext
    intro y
    change (∑ w, (t * x.1 w) * y.1 w) +
      (∑ w, 2 * ((t • x.2 w) * y.2 w).re) =
      t * ((∑ w, x.1 w * y.1 w) + ∑ w, 2 * (x.2 w * y.2 w).re)
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro w _
      ring
    · apply Finset.sum_congr rfl
      intro w _
      simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im]
      ring

theorem form_apply (x y : mixedSpace F) : form F x y =
    (∑ w : RealPlace F, x.1 w * y.1 w) +
      ∑ w : ComplexPlace F, 2 * (x.2 w * y.2 w).re := rfl

/-- Conjugation only acts at actual complex places and is an involutive linear equivalence. -/
def conjugation : mixedSpace F ≃L[ℝ] mixedSpace F :=
  (ContinuousLinearEquiv.refl ℝ _).prodCongr
    (ContinuousLinearEquiv.piCongrRight fun _ ↦ Complex.conjLIE.toContinuousLinearEquiv)

omit [NumberField F] in
@[simp]
theorem conjugation_real (x : mixedSpace F) (w : RealPlace F) :
    (conjugation F x).1 w = x.1 w := rfl

omit [NumberField F] in
@[simp]
theorem conjugation_complex (x : mixedSpace F) (w : ComplexPlace F) :
    (conjugation F x).2 w = conj (x.2 w) := rfl

/-- The trace pairing is symmetric, as multiplication in the mixed algebra is commutative. -/
theorem symmetric : (form F).IsSymm := by
  constructor
  intro x y
  simp only [form_apply, mul_comm]

/-- Conjugating the second argument gives exactly the fixed positive theta norm. -/
theorem form_conjugation (x : mixedSpace F) :
    form F x (conjugation F x) = ‖IdealTheta.euclidean F x‖ ^ 2 := by
  rw [IdealThetaNormalization.euclidean_norm_sq]
  simp only [form_apply, conjugation_real, conjugation_complex, Complex.mul_conj,
    Complex.ofReal_re, ← Complex.sq_norm, IdealThetaNormalization.energy,
    Finset.mul_sum, pow_two]

/-- Nondegeneracy is deduced from the actual positive norm, without a pairing hypothesis. -/
theorem nondegenerate : (form F).Nondegenerate := by
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
  intro x hx
  have h := hx (conjugation F x)
  rw [form_conjugation] at h
  have hz : IdealTheta.euclidean F x = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp h)
  exact (IdealTheta.euclidean F).injective (by simpa using hz)

/-- Coordinate trace of actual infinite adeles is the mixed-space pairing. -/
theorem coordinates (a b : InfiniteAdeleRing F) :
    form F (InfiniteTraceHaar.coordinates F a) (InfiniteTraceHaar.coordinates F b) =
      InfiniteAdelicTrace.trace (a * b) := by
  rw [trace_coordinates]
  have hm := map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a b
  change _ = (∑ w : RealPlace F, ((InfiniteTraceHaar.coordinates F (a * b)).1 w)) + _
  change InfiniteTraceHaar.coordinates F (a * b) =
    InfiniteTraceHaar.coordinates F a * InfiniteTraceHaar.coordinates F b at hm
  rw [hm]
  rfl

/-- On actual field elements this is the original rational algebra trace. -/
theorem diagonal (x y : F) :
    form F (mixedEmbedding F x) (mixedEmbedding F y) = (Algebra.trace ℚ F (x * y) : ℝ) := by
  rw [← InfiniteTraceHaar.coordinates_diagonal F x,
    ← InfiniteTraceHaar.coordinates_diagonal F y, coordinates, ← map_mul,
    InfiniteAdelicTrace.diagonal]

/-- The fixed Fourier phase uses this same pairing, including its negative sign. -/
theorem character (a b : InfiniteAdeleRing F) :
    AdelicTraceCharacter.infiniteCharacter (a * b) =
      (Real.fourierChar (-(form F (InfiniteTraceHaar.coordinates F a)
        (InfiniteTraceHaar.coordinates F b))) : ℂ) := by
  rw [coordinates, InfiniteTraceFourier.character_eq]

end NormEuclidean.MixedTracePairing
