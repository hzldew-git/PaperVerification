import NormEuclidean.BinaryResidueCriterion
import NormEuclidean.CompletedIntegralLattice
import Bong.Dyadic.HilbertSymbol

/-!
# Binary forms as scaled quadratic norm forms

The parameter is the negative associated Gram determinant. A frame is
constructed for every anisotropic binary space and is transported to actual
scalar extensions. The parameter may become a square after scalar extension.
-/

noncomputable section

namespace NormEuclidean.BinaryNormForm

open Bong.Dyadic
open scoped TensorProduct

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Invertible (2 : K)] (Q : QuadraticForm K V)

/-- Coordinates for the norm form, without any integral-basis requirement. -/
structure Frame (theta : Kˣ) where
  basis : Module.Basis (Fin 2) K V
  first_ne_zero : Q (basis 0) ≠ 0
  parameter_eq : (theta : K) =
    (Q.associated (basis 0) (basis 1)) ^ 2 - Q (basis 0) * Q (basis 1)

variable {Q} {theta : Kˣ}

/-- Completing the square in a binary basis gives the actual norm equation. -/
theorem Frame.scaled_value_combination (f : Frame Q theta) (x y : K) :
    Q (f.basis 0) * Q (x • f.basis 0 + y • f.basis 1) =
      (Q (f.basis 0) * x + Q.associated (f.basis 0) (f.basis 1) * y) ^ 2 -
        (theta : K) * y ^ 2 := by
  rw [quadraticForm_binary_expansion, f.parameter_eq]
  ring

/-- Every nonzero represented value becomes a quadratic norm after one fixed scaling. -/
theorem Frame.scaled_value_isNorm (f : Frame Q theta) (x : V) (hx : Q x ≠ 0) :
    IsQuadraticNorm K theta
      (Units.mk0 (Q (f.basis 0)) f.first_ne_zero * Units.mk0 (Q x) hx) := by
  refine ⟨Q (f.basis 0) * f.basis.repr x 0 +
    Q.associated (f.basis 0) (f.basis 1) * f.basis.repr x 1,
    f.basis.repr x 1, ?_⟩
  have he : f.basis.repr x 0 • f.basis 0 + f.basis.repr x 1 • f.basis 1 = x := by
    simpa only [Fin.sum_univ_two] using f.basis.sum_repr x
  simpa only [he, Units.val_mul, Units.val_mk0] using
    (f.scaled_value_combination (f.basis.repr x 0) (f.basis.repr x 1)).symm

/-- Products of two nonzero quadratic values are norms, including in the split case. -/
theorem Frame.value_product_isNorm (f : Frame Q theta)
    (x : V) (hx : Q x ≠ 0) (y : V) (hy : Q y ≠ 0) :
    IsQuadraticNorm K theta (Units.mk0 (Q x) hx * Units.mk0 (Q y) hy) := by
  apply (isQuadraticNorm_mul_square_right_iff K theta _
    (Units.mk0 (Q (f.basis 0)) f.first_ne_zero)).mp
  convert (f.scaled_value_isNorm x hx).mul K (f.scaled_value_isNorm y hy) using 1
  simp only [pow_two, mul_assoc, mul_left_comm, mul_comm]

/-- Conversely every norm is a product of two represented values, the second fixed. -/
theorem Frame.norm_is_value_product (f : Frame Q theta) (a : Kˣ)
    (ha : IsQuadraticNorm K theta a) :
    ∃ (x : V) (hx : Q x ≠ 0),
      Units.mk0 (Q x) hx * Units.mk0 (Q (f.basis 0)) f.first_ne_zero = a := by
  obtain ⟨r, s, hrs⟩ := ha
  let t := (r - Q.associated (f.basis 0) (f.basis 1) * s) / Q (f.basis 0)
  let x := t • f.basis 0 + s • f.basis 1
  have ht : Q (f.basis 0) * t + Q.associated (f.basis 0) (f.basis 1) * s = r := by
    dsimp only [t]
    field_simp [f.first_ne_zero]
    ring
  have hxval : Q (f.basis 0) * Q x = (a : K) := by
    rw [show Q (f.basis 0) * Q x = _ from f.scaled_value_combination t s, ht, hrs]
  have hx : Q x ≠ 0 := by
    intro h
    exact a.ne_zero (by simpa [h] using hxval.symm)
  refine ⟨x, hx, Units.ext ?_⟩
  simpa only [Units.val_mul, Units.val_mk0, mul_comm] using hxval

/-- An anisotropic binary space supplies a nonsquare parameter and an actual frame. -/
theorem exists_frame [FiniteDimensional K V] (hA : Q.Anisotropic)
    (hdim : Module.finrank K V = 2) :
    ∃ theta : Kˣ, ¬ IsSquare theta ∧ Nonempty (Frame Q theta) := by
  classical
  let e := (Module.finBasis K V).reindex (finCongr hdim)
  let d := (Q.associated (e 0) (e 1)) ^ 2 - Q (e 0) * Q (e 1)
  have hd : ¬ IsSquare d := by
    intro hd
    have hd' : IsSquare (-(LinearMap.toMatrix₂ e e Q.associated).det) := by
      simpa only [binary_gramDet_eq, neg_sub] using hd
    obtain ⟨x, hx, hQx⟩ := (quadraticForm_binary_isotropic_iff_isSquare_neg_det Q e).mpr hd'
    exact hx (hA x hQx)
  have hd0 : d ≠ 0 := by
    intro h
    exact hd (by rw [h]; exact ⟨0, by simp⟩)
  refine ⟨Units.mk0 d hd0, ?_, ⟨e, ?_, rfl⟩⟩
  · rintro ⟨s, hs⟩
    exact hd ⟨(s : K), congrArg Units.val hs⟩
  · exact fun h ↦ e.ne_zero 0 (hA _ h)

variable (A : Type*) [Field A] [Algebra K A] [Invertible (2 : A)]

/-- The same norm frame over an actual field extension, whether split or nonsplit. -/
def Frame.baseChange (f : Frame Q theta) :
    Frame (Q.baseChange A) (Units.map (algebraMap K A).toMonoidHom theta) where
  basis := f.basis.baseChange A
  first_ne_zero := by
    simp only [Module.Basis.baseChange_apply, QuadraticForm.baseChange_tmul,
      Algebra.smul_def, mul_one]
    intro h
    exact f.first_ne_zero ((algebraMap K A).injective (h.trans (map_zero _).symm))
  parameter_eq := by
    simp only [Units.coe_map, Module.Basis.baseChange_apply,
      QuadraticForm.baseChange_tmul, Algebra.smul_def, mul_one,
      QuadraticForm.associated_baseChange, LinearMap.BilinForm.baseChange_tmul]
    change algebraMap K A (theta : K) = _
    rw [f.parameter_eq, map_sub, map_pow, map_mul]

end NormEuclidean.BinaryNormForm
