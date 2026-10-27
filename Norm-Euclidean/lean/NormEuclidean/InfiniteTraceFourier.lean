import NormEuclidean.InfiniteTraceProduct

/-!
# Actual infinite adelic trace Fourier integration

The actual global archimedean character and Haar measure factor into
their real and complex trace normalizations. Fourier inversion below
is proved for separated continuous integrable functions with integrable
ordinary local transforms. No arbitrary adelic inversion theorem is asserted.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.InfiniteTraceFourier

open NumberField MeasureTheory MeasureTheory.Measure Set
open InfiniteTraceProduct ArchimedeanTraceFourier
open scoped NumberField Classical FourierTransform NormEuclidean.InfiniteTraceHaar

variable (F : Type*) [Field F] [NumberField F]

/-- Separated functions on the actual original infinite completions, in their proved coordinates. -/
def tensor (f : RealPlace F → ℝ → ℂ) (g : ComplexPlace F → ℂ → ℂ)
    (a : InfiniteAdeleRing F) : ℂ :=
  (∏ w : RealPlace F, f w ((InfiniteTraceHaar.coordinates F a).1 w)) *
    ∏ w : ComplexPlace F, g w ((InfiniteTraceHaar.coordinates F a).2 w)

/-- The literal trace-character Fourier integral on the original infinite adele ring. -/
def fourier (f : InfiniteAdeleRing F → ℂ) (w : InfiniteAdeleRing F) : ℂ :=
  ∫ a : InfiniteAdeleRing F, AdelicTraceCharacter.infiniteCharacter (a * w) * f a
    ∂InfiniteTraceHaar.haar F

theorem character_eq (a : InfiniteAdeleRing F) :
    AdelicTraceCharacter.infiniteCharacter a =
      (Real.fourierChar (-InfiniteAdelicTrace.trace a) : ℂ) := by
  change AdelicTraceCharacter.realPhase (-(InfiniteAdelicTrace.trace a :
    AddCircle (1 : ℝ))) = _
  rw [← AddCircle.coe_neg, phase_eq]

theorem phase_sum {I : Type*} (S : Finset I) (f : I → ℝ) :
    (Real.fourierChar (∑ i ∈ S, f i) : ℂ) = ∏ i ∈ S, (Real.fourierChar (f i) : ℂ) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, Real.fourierChar.map_add_eq_mul, Circle.coe_mul,
      Finset.prod_insert ha, ih]

/-- Factorization uses the original infinite adelic trace character, including its negative sign. -/
theorem character_product (a : InfiniteAdeleRing F) :
    AdelicTraceCharacter.infiniteCharacter a =
      (∏ w : RealPlace F,
        (Real.fourierChar (-((InfiniteTraceHaar.coordinates F a).1 w)) : ℂ)) *
        ∏ w : ComplexPlace F,
          (Real.fourierChar (-(2 * ((InfiniteTraceHaar.coordinates F a).2 w).re)) : ℂ) := by
  rw [character_eq, trace_coordinates, neg_add, Real.fourierChar.map_add_eq_mul,
    Circle.coe_mul, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
    phase_sum, phase_sum]

/-- Tensor Fourier integration is the product of the proved real and complex local transforms. -/
theorem fourier_tensor
    (f : RealPlace F → ℝ → ℂ) (g : ComplexPlace F → ℂ → ℂ)
    (w : InfiniteAdeleRing F) :
    fourier F (tensor F f g) w =
      tensor F (fun v ↦ 𝓕 (f v)) (fun v ↦ complexFourier (g v)) w := by
  let wr (v : RealPlace F) := (InfiniteTraceHaar.coordinates F w).1 v
  let wc (v : ComplexPlace F) := (InfiniteTraceHaar.coordinates F w).2 v
  let fr (v : RealPlace F) (x : ℝ) := (Real.fourierChar (-(x * wr v)) : ℂ) * f v x
  let fc (v : ComplexPlace F) (z : ℂ) :=
    (Real.fourierChar (-(2 * (z * wc v).re)) : ℂ) * g v z
  have he (a : InfiniteAdeleRing F) :
      AdelicTraceCharacter.infiniteCharacter (a * w) * tensor F f g a =
        tensor F fr fc a := by
    rw [character_product]
    have hm : InfiniteTraceHaar.coordinates F (a * w) =
        InfiniteTraceHaar.coordinates F a * InfiniteTraceHaar.coordinates F w :=
      map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a w
    rw [hm]
    simp only [tensor, fr, fc, wr, wc, Finset.prod_mul_distrib,
      Prod.fst_mul, Prod.snd_mul, Pi.mul_apply]
    ring
  unfold fourier
  simp_rw [he]
  rw [show (∫ a, tensor F fr fc a ∂InfiniteTraceHaar.haar F) =
    (∏ v : RealPlace F, ∫ x, fr v x) *
      ∏ v : ComplexPlace F, ∫ z, fc v z ∂complexHaar from tensor_integral F fr fc]
  unfold tensor
  congr 1
  · apply Finset.prod_congr rfl
    intro v _
    exact (Real.fourier_real_eq (f v) (wr v)).symm

/-- Double transformation of the separated family is actual adelic reflection. -/
theorem tensor_double
    (f : RealPlace F → ℝ → ℂ) (g : ComplexPlace F → ℂ → ℂ)
    (hf : ∀ v, Integrable (f v)) (hF : ∀ v, Integrable (𝓕 (f v)))
    (hfc : ∀ v, Continuous (f v)) (hg : ∀ v, Integrable (g v))
    (hG : ∀ v, Integrable (𝓕 (g v))) (hgc : ∀ v, Continuous (g v))
    (w : InfiniteAdeleRing F) :
    fourier F (fourier F (tensor F f g)) w = tensor F f g (-w) := by
  have he : fourier F (tensor F f g) =
      tensor F (fun v ↦ 𝓕 (f v)) (fun v ↦ complexFourier (g v)) :=
    funext (fourier_tensor F f g)
  rw [he, fourier_tensor]
  simp only [tensor, map_neg, Prod.fst_neg, Prod.snd_neg, Pi.neg_apply]
  congr 1
  · exact Finset.prod_congr rfl fun v _ ↦ real_double (hf v) (hF v) (hfc v) _
  · exact Finset.prod_congr rfl fun v _ ↦ complex_double (hg v) (hG v) (hgc v) _

end NormEuclidean.InfiniteTraceFourier
