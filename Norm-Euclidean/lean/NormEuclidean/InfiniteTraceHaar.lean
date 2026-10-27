import NormEuclidean.InfiniteAdelicTrace
import NormEuclidean.PrincipalAdeleTopology
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Trace normalization on the actual infinite adele ring

The real factor is Lebesgue measure and each complex factor contributes
twice planar Lebesgue measure. The mixed-coordinate measure therefore
has the factor `2 ^ r₂`. Its actual integral-lattice fundamental domain
has measure `sqrt |disc(F)|`, without a covolume normalization premise.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.InfiniteTraceHaar

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open MeasureTheory MeasureTheory.Measure Set
open scoped NumberField Classical ENNReal NormEuclidean.PrincipalAdeleTopology

variable (F : Type*) [Field F] [NumberField F]

scoped instance infiniteMeasurable : MeasurableSpace (InfiniteAdeleRing F) := borel _
scoped instance infiniteBorel : BorelSpace (InfiniteAdeleRing F) := ⟨rfl⟩

open scoped NormEuclidean.InfiniteTraceHaar

/-- The standard mixed-coordinate equivalence respects the original completion topology. -/
def coordinates : InfiniteAdeleRing F ≃ₜ+ mixedEmbedding.mixedSpace F := by
  let h := (Homeomorph.piEquivPiSubtypeProd (fun w : InfinitePlace F ↦ IsReal w)
    (fun w ↦ w.Completion)).trans
    (Homeomorph.prodCongr
      (Homeomorph.piCongrRight fun w ↦ (isometryEquivRealOfIsReal w.2).toHomeomorph)
      ((Homeomorph.piCongrRight fun w ↦
        (isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp w.2)).toHomeomorph).trans
        (Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ)
          (Equiv.subtypeEquivRight fun _ ↦ not_isReal_iff_isComplex))))
  exact ⟨(InfiniteAdeleRing.ringEquiv_mixedSpace F).toAddEquiv,
    h.continuous, h.symm.continuous⟩

@[simp]
theorem coordinates_apply (a : InfiniteAdeleRing F) :
    coordinates F a = InfiniteAdeleRing.ringEquiv_mixedSpace F a := rfl

@[simp]
theorem coordinates_diagonal (x : F) :
    coordinates F (algebraMap F (InfiniteAdeleRing F) x) = mixedEmbedding F x :=
  (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (K := F)).symm

/-- Each complex place supplies the factor two required by the trace pairing. -/
def mixedMeasure : Measure (mixedEmbedding.mixedSpace F) :=
  (2 : ℝ≥0∞) ^ nrComplexPlaces F • volume

instance mixedMeasure_isHaar : IsAddHaarMeasure (mixedMeasure F) :=
  IsAddHaarMeasure.smul volume (by positivity) (by finiteness)

/-- The trace-normalized Haar measure on the unchanged infinite adele ring. -/
def haar : Measure (InfiniteAdeleRing F) := (mixedMeasure F).map (coordinates F).symm

instance haar_isHaar : IsAddHaarMeasure (haar F) :=
  (coordinates F).symm.isAddHaarMeasure_map _

/-- The mixed coordinates carry the actual infinite measure to its explicit normalization. -/
theorem coordinates_preserving :
    MeasurePreserving (coordinates F) (haar F) (mixedMeasure F) := by
  refine ⟨(coordinates F).continuous.measurable, ?_⟩
  rw [haar]
  rw [Measure.map_map (show Measurable (coordinates F) from
    (coordinates F).continuous.measurable) (show Measurable (coordinates F).symm from
    (coordinates F).symm.continuous.measurable)]
  have hid : (coordinates F) ∘ (coordinates F).symm = id :=
    funext (coordinates F).apply_symm_apply
  rw [hid, Measure.map_id]

/-- The usual half-open integral-basis fundamental domain in actual infinite completions. -/
def integralDomain : Set (InfiniteAdeleRing F) :=
  coordinates F ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)

theorem integralDomain_measurable : MeasurableSet (integralDomain F) := by
  exact (ZSpan.fundamentalDomain_measurableSet _).preimage
    (coordinates F).continuous.measurable

/-- Complex multiplicities cancel the `2⁻ʳ²` in the discriminant covolume formula. -/
theorem mixed_integral_volume :
    mixedMeasure F (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) =
      ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|) := by
  rw [mixedMeasure, Measure.smul_apply, smul_eq_mul,
    mixedEmbedding.volume_fundamentalDomain_latticeBasis, ← mul_assoc,
    ← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow, one_mul]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) ENNReal.ofReal_ne_top).mp
  simp only [ENNReal.coe_toReal, Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

/-- The actual infinite fundamental-domain volume is the square root absolute discriminant. -/
theorem integral_volume :
    haar F (integralDomain F) = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|) := by
  rw [integralDomain, ← mixed_integral_volume F]
  exact (coordinates_preserving F).measure_preimage
    (ZSpan.fundamentalDomain_measurableSet _).nullMeasurableSet

end NormEuclidean.InfiniteTraceHaar
