import NormEuclidean.InfiniteTraceHaar
import NormEuclidean.ArchimedeanTraceFourier
import Mathlib.MeasureTheory.Integral.Pi

/-! Explicit product of real and complex trace-normalized archimedean measures. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.InfiniteTraceProduct

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open MeasureTheory MeasureTheory.Measure Set ArchimedeanTraceFourier
open scoped NumberField Classical ENNReal NormEuclidean.InfiniteTraceHaar

variable (F : Type*) [Field F] [NumberField F]

abbrev RealPlace := {w : InfinitePlace F // IsReal w}
abbrev ComplexPlace := {w : InfinitePlace F // IsComplex w}

/-- The finite product uses the analytically verified complex trace Haar measure. -/
def complexProduct : Measure (ComplexPlace F → ℂ) :=
  Measure.pi (fun _ ↦ complexHaar)

instance complexProduct_sigmaFinite : SigmaFinite (complexProduct F) :=
  inferInstanceAs (SigmaFinite (Measure.pi (fun _ : ComplexPlace F ↦ complexHaar)))

/-- One factor two for each actual complex place. -/
theorem complex_product_eq :
    complexProduct F = (2 : ℝ≥0∞) ^ nrComplexPlaces F • volume := by
  apply Measure.pi_eq
  intro A hA
  rw [Measure.smul_apply, smul_eq_mul, volume_pi, Measure.pi_pi]
  simp only [complexHaar, Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ]

/-- The exact mixed measure is the product of real Lebesgue and complex trace measures. -/
theorem mixed_product_eq :
    (volume : Measure (RealPlace F → ℝ)).prod (complexProduct F) =
      InfiniteTraceHaar.mixedMeasure F := by
  rw [complex_product_eq, Measure.prod_smul_right]
  rfl

/-- Actual infinite trace written in the original real and complex completion coordinates. -/
theorem trace_coordinates (a : InfiniteAdeleRing F) :
    InfiniteAdelicTrace.trace a =
      (∑ w : RealPlace F, (InfiniteTraceHaar.coordinates F a).1 w) +
        ∑ w : ComplexPlace F, 2 * ((InfiniteTraceHaar.coordinates F a).2 w).re := by
  change (∑ w : InfinitePlace F, InfiniteAdelicTrace.localTrace w (a w)) = _
  rw [← Fintype.sum_subtype_add_sum_subtype (fun w : InfinitePlace F ↦ IsReal w)]
  congr 1
  · apply Finset.sum_congr rfl
    intro w _
    change (w.1.mult : ℝ) * (extensionEmbedding w.1 (a w.1)).re =
      extensionEmbeddingOfIsReal w.2 (a w.1)
    rw [mult_isReal, Nat.cast_one, one_mul, ← extensionEmbeddingOfIsReal_apply w.2]
    rfl
  · let e : {w : InfinitePlace F // ¬ IsReal w} ≃ ComplexPlace F :=
      Equiv.subtypeEquivRight fun _ ↦ not_isReal_iff_isComplex
    rw [← e.sum_comp]
    apply Finset.sum_congr rfl
    intro w _
    change (w.1.mult : ℝ) * (extensionEmbedding w.1 (a w.1)).re =
      2 * (extensionEmbedding w.1 (a w.1)).re
    rw [mult, if_neg w.2, Nat.cast_ofNat]

set_option maxHeartbeats 800000 in
/-- Actual integration of separated archimedean functions uses the local trace measures. -/
theorem tensor_integral
    (f : RealPlace F → ℝ → ℂ) (g : ComplexPlace F → ℂ → ℂ) :
    (∫ a : InfiniteAdeleRing F,
      (∏ w : RealPlace F, f w ((InfiniteTraceHaar.coordinates F a).1 w)) *
        ∏ w : ComplexPlace F, g w ((InfiniteTraceHaar.coordinates F a).2 w)
      ∂InfiniteTraceHaar.haar F) =
      (∏ w : RealPlace F, ∫ x : ℝ, f w x) *
        ∏ w : ComplexPlace F, ∫ z : ℂ, g w z ∂complexHaar := by
  have hm : MeasurableEmbedding (InfiniteTraceHaar.coordinates F).symm :=
    (InfiniteTraceHaar.coordinates F).symm.toHomeomorph.measurableEmbedding
  rw [InfiniteTraceHaar.haar, hm.integral_map]
  simp only [ContinuousAddEquiv.apply_symm_apply]
  rw [← mixed_product_eq]
  trans (∫ x : RealPlace F → ℝ, ∏ w, f w (x w)) *
    ∫ z : ComplexPlace F → ℂ, ∏ w, g w (z w) ∂complexProduct F
  · exact integral_prod_mul (fun x : RealPlace F → ℝ ↦ ∏ w, f w (x w))
      (fun z : ComplexPlace F → ℂ ↦ ∏ w, g w (z w))
  · have hr := integral_fintype_prod_volume_eq_prod f
    have hc : (∫ z : ComplexPlace F → ℂ, ∏ w, g w (z w) ∂complexProduct F) =
        ∏ w : ComplexPlace F, ∫ z : ℂ, g w z ∂complexHaar :=
      integral_fintype_prod_eq_prod g
    exact congrArg₂ (fun a b : ℂ ↦ a * b) hr hc

end NormEuclidean.InfiniteTraceProduct
