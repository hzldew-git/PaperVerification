import NormEuclidean.ArchimedeanLogScale
import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# Actual norm-one shapes from the weighted unit logarithm space

The omitted coordinate is restored by the sum-zero relation. Dividing
each weighted coordinate by its real or complex multiplicity gives
the actual logarithm of the archimedean scaling. At a unit this is its
actual absolute value at every infinite place, including the omitted one.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.UnitLogShape

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField Classical

variable (F : Type*) [Field F] [NumberField F]

/-- Restore the omitted weighted coordinate by its actual sum-zero constraint. -/
def weighted : logSpace F →ₗ[ℝ] (InfinitePlace F → ℝ) where
  toFun l w := if h : w = w₀ then -∑ v, l v else l ⟨w, h⟩
  map_add' l m := by
    ext w
    by_cases h : w = w₀ <;> simp [h, Finset.sum_add_distrib, add_comm]
  map_smul' c l := by
    ext w
    by_cases h : w = w₀ <;> simp [h, Finset.mul_sum]

@[simp]
theorem weighted_base (l : logSpace F) : weighted F l w₀ = -∑ v, l v := by
  simp [weighted]

@[simp]
theorem weighted_other (l : logSpace F) (w : {w : InfinitePlace F // w ≠ w₀}) :
    weighted F l w = l w := by simp [weighted, w.2]

/-- All restored weighted coordinates have exactly zero sum. -/
theorem sum_weighted (l : logSpace F) : ∑ w, weighted F l w = 0 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀]
  simp only [weighted_base, weighted_other, neg_add_cancel]

/-- Actual logarithmic scales divide weighted logs by the actual place multiplicity. -/
def parameter : logSpace F →ₗ[ℝ] (InfinitePlace F → ℝ) where
  toFun l w := weighted F l w / (mult w : ℝ)
  map_add' l m := by ext w; simp [add_div]
  map_smul' c l := by ext w; simp [mul_div_assoc]

@[simp]
theorem parameter_apply (l : logSpace F) (w : InfinitePlace F) :
    parameter F l w = weighted F l w / (mult w : ℝ) := rfl

/-- No scalar radial factor is hidden in the shape variables. -/
theorem weighted_sum_parameter (l : logSpace F) :
    ∑ w, (mult w : ℝ) * parameter F l w = 0 := by
  simp_rw [parameter_apply, mul_div_cancel₀ _ (mult_coe_ne_zero (w := _))]
  exact sum_weighted F l

/-- The actual parameter map is continuous on the actual finite-dimensional log space. -/
theorem continuous_parameter : Continuous (parameter F) :=
  (parameter F).continuous_of_finiteDimensional

/-- Restoring a unit log recovers its weighted actual absolute log at every place. -/
theorem weighted_logEmbedding (u : (𝓞 F)ˣ) (w : InfinitePlace F) :
    weighted F (logEmbedding F (Additive.ofMul u)) w =
      (mult w : ℝ) * Real.log (w (u : F)) := by
  by_cases h : w = w₀
  · subst w
    rw [weighted_base, sum_logEmbedding_component]
    ring
  · simp only [weighted, LinearMap.coe_mk, AddHom.coe_mk, dif_neg h,
      logEmbedding_component]

/-- Actual unit scaling is its actual archimedean absolute value, with no missing place. -/
theorem parameter_logEmbedding (u : (𝓞 F)ˣ) (w : InfinitePlace F) :
    parameter F (logEmbedding F (Additive.ofMul u)) w = Real.log (w (u : F)) := by
  rw [parameter_apply, weighted_logEmbedding,
    mul_div_cancel_left₀ _ (mult_coe_ne_zero (w := w))]

/-- Every shape has multiplicative norm one on the original mixed space. -/
theorem preserves_multiplicative_norm (l : logSpace F) (x : mixedSpace F) :
    mixedEmbedding.norm (ArchimedeanLogScale.scale F (parameter F l) x) =
      mixedEmbedding.norm x := by
  rw [ArchimedeanLogScale.multiplicative_norm_scale, weighted_sum_parameter,
    Real.exp_zero, one_mul]

/-- Shifting by a unit logarithm reproduces actual unit multiplication in place norms. -/
theorem unit_place_norm (l : logSpace F) (u : (𝓞 F)ˣ) (x : mixedSpace F)
    (w : InfinitePlace F) :
    normAtPlace w (ArchimedeanLogScale.scale F
      (parameter F (l + logEmbedding F (Additive.ofMul u))) x) =
        normAtPlace w (ArchimedeanLogScale.scale F (parameter F l) (u • x)) := by
  rw [ArchimedeanLogScale.normAtPlace_scale, ArchimedeanLogScale.normAtPlace_scale,
    map_add, Pi.add_apply, parameter_logEmbedding, Real.exp_add,
    Real.exp_log (Units.pos_at_place u w), unitSMul_smul, map_mul, normAtPlace_apply]
  ring

/-- The actual Gaussian energy has the exact unit-log translation identity. -/
theorem unit_energy (l : logSpace F) (u : (𝓞 F)ˣ) (x : mixedSpace F) :
    ‖IdealTheta.euclidean F (ArchimedeanLogScale.scale F
      (parameter F (l + logEmbedding F (Additive.ofMul u))) x)‖ ^ 2 =
        ‖IdealTheta.euclidean F
          (ArchimedeanLogScale.scale F (parameter F l) (u • x))‖ ^ 2 :=
  ArchimedeanLogScale.energy_eq_of_place_norm F _ _ (unit_place_norm F l u x)

end NormEuclidean.UnitLogShape
